module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasChainA
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExpChartStandardSmooth

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationDeterminesChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitFunctionHolomorphic
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitFunctionHolomorphic
open Filter Topology Metric

namespace GlobalTheory.CompanionTheory.HoloChart

theorem holomorphic_inverse_with_parameters :
    ∀ (n : ℕ) (I J : Type) [Fintype I] [Fintype J] (Ω : Set ((Fin n → ℂ) × (I → ℂ)))
      (Φ : (Fin n → ℂ) × (I → ℂ) → (J → ℂ)) (b₀ : Fin n → ℂ) (x₀ : I → ℂ)
      (L : (I → ℂ) ≃L[ℂ] (J → ℂ)), IsOpen Ω → (b₀, x₀) ∈ Ω → DifferentiableOn ℂ Φ Ω →
      HasFDerivAt (fun x => Φ (b₀, x)) (L : (I → ℂ) →L[ℂ] (J → ℂ)) x₀ →
  ∃ (ε δ : ℝ) (X : (Fin n → ℂ) × (J → ℂ) → (I → ℂ)), 0 < ε ∧ 0 < δ ∧ X (b₀, Φ (b₀, x₀)) = x₀ ∧
    DifferentiableOn ℂ X (ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε) ∧
    (∀ p ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε, (p.1, X p) ∈ Ω ∧ Φ (p.1, X p) = p.2 ∧
      ∀ v, fderiv ℂ (fun x => Φ (p.1, x)) (X p) v = 0 → v = 0) ∧
    ∀ b ∈ ball b₀ δ, ∀ x ∈ ball x₀ δ, (b, x) ∈ Ω ∧ Φ (b, x) ∈ ball (Φ (b₀, x₀)) ε ∧
      X (b, Φ (b, x)) = x := by
  intro n I J _ _ Ω Φ b₀ x₀ L hΩ ha hΦ hL
  have cS := ReciprocityTheory.ChartRestriction.DS.S7.cca_contDiffOn hΩ hΦ
  have cΦ : ContDiffAt ℂ 1 Φ (b₀, x₀) :=
    (cS.contDiffAt (hΩ.mem_nhds ha)).of_le (by exact_mod_cast le_top)
  have hinr : ∀ p : (Fin n → ℂ) × (I → ℂ), DifferentiableAt ℂ Φ p →
      HasFDerivAt (fun x => Φ (p.1, x))
        ((fderiv ℂ Φ p).comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (I → ℂ))) p.2 := fun p hp =>
    HasFDerivAt.comp p.2 (f := fun x => (p.1, x)) hp.hasFDerivAt (hasFDerivAt_prodMk_right p.1 p.2)
  let D := fderiv ℂ Φ (b₀, x₀)
  have hD : HasFDerivAt Φ D (b₀, x₀) := (cΦ.differentiableAt one_ne_zero).hasFDerivAt
  have hDL : D.comp (ContinuousLinearMap.inr ℂ (Fin n → ℂ) (I → ℂ)) = (L : (I → ℂ) →L[ℂ] (J → ℂ)) :=
    (hinr (b₀, x₀) hD.differentiableAt).unique hL
  have hDuv : ∀ u v, D (u, v) = D (u, 0) + L v := fun u v => by
    have h1 : D (0, v) = L v := by
      have := congrArg (fun A : (I → ℂ) →L[ℂ] (J → ℂ) => A v) hDL
      simpa using this
    rw [← h1, ← map_add (f := _)]; simp
  let F₀ : ((Fin n → ℂ) × (I → ℂ)) →L[ℂ] ((Fin n → ℂ) × (J → ℂ)) :=
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod D
  let G₀ : ((Fin n → ℂ) × (J → ℂ)) →L[ℂ] ((Fin n → ℂ) × (I → ℂ)) :=
    (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (J → ℂ)).prod
      ((L.symm : (J → ℂ) →L[ℂ] (I → ℂ)).comp
        (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (J → ℂ) -
          (D.comp (ContinuousLinearMap.inl ℂ (Fin n → ℂ) (I → ℂ))).comp
            (ContinuousLinearMap.fst ℂ (Fin n → ℂ) (J → ℂ))))
  have hGF : Function.LeftInverse G₀ F₀ := by
    rintro ⟨u, v⟩
    simp [F₀, G₀, hDuv u v]
  have hFG : Function.RightInverse G₀ F₀ := by
    rintro ⟨u, w⟩
    have h : G₀ (u, w) = (u, L.symm (w - D (u, 0))) := by simp [G₀]
    rw [h]
    refine Prod.ext rfl ?_
    show D (u, L.symm (w - D (u, 0))) = w
    rw [hDuv]
    simp
  let F' : ((Fin n → ℂ) × (I → ℂ)) ≃L[ℂ] ((Fin n → ℂ) × (J → ℂ)) :=
    ContinuousLinearEquiv.equivOfInverse F₀ G₀ hGF hFG
  let F : (Fin n → ℂ) × (I → ℂ) → (Fin n → ℂ) × (J → ℂ) := fun p => (p.1, Φ p)
  have hF : HasFDerivAt F (F' : ((Fin n → ℂ) × (I → ℂ)) →L[ℂ] ((Fin n → ℂ) × (J → ℂ))) (b₀, x₀) :=
    hasFDerivAt_fst.prodMk hD
  have cF : ContDiffAt ℂ 1 F (b₀, x₀) := contDiffAt_fst.prodMk cΦ
  let T := cF.toOpenPartialHomeomorph F (f' := F') hF one_ne_zero
  have hTF : ∀ p, T p = F p := fun _ => rfl
  have src : (b₀, x₀) ∈ T.source := cF.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero
  have tgt : F (b₀, x₀) ∈ T.target :=
    cF.image_mem_toOpenPartialHomeomorph_target (f' := F') hF one_ne_zero
  have hinv : T.symm (F (b₀, x₀)) = (b₀, x₀) := T.left_inv src
  let O := (T.target ∩ interior {w | ContDiffAt ℂ 1 T.symm w}) ∩ (T.target ∩ T.symm ⁻¹' Ω)
  have oO : IsOpen O := (T.open_target.inter isOpen_interior).inter (T.isOpen_inter_preimage_symm hΩ)
  have mO : F (b₀, x₀) ∈ O := by
    refine ⟨⟨tgt, mem_interior_iff_mem_nhds.2 ?_⟩, tgt, ?_⟩
    · exact (cF.to_localInverse (f' := F') hF one_ne_zero).eventually (by simp)
    · simpa [hinv] using ha
  obtain ⟨ε, ε0, hε⟩ := Metric.isOpen_iff.1 oO _ mO
  have hball : ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε ⊆ O := by
    rw [ball_prod_same]; exact hε
  obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (Filter.inter_mem
    (T.open_source.mem_nhds src) (hΩ.mem_nhds ha))
    (hF.continuousAt.preimage_mem_nhds (ball_mem_nhds (F (b₀, x₀)) ε0)))
  have hsec : ∀ p ∈ O, T.symm p = (p.1, (T.symm p).2) ∧ Φ (T.symm p) = p.2 := fun p hp => by
    have h : F (T.symm p) = p := T.right_inv hp.1.1
    have h1 : (T.symm p).1 = p.1 := congrArg Prod.fst h
    have h2 : Φ (T.symm p) = p.2 := congrArg Prod.snd h
    exact ⟨Prod.ext h1 rfl, h2⟩
  refine ⟨ε, min δ δ, fun p => (T.symm p).2, ε0, lt_min δ0 δ0, ?_, ?_, ?_, ?_⟩
  · exact congrArg Prod.snd hinv
  · intro p hp
    have c : ContDiffAt ℂ 1 T.symm p := interior_subset (hball hp).1.2
    exact ((differentiableAt_snd).comp p (c.differentiableAt one_ne_zero)).differentiableWithinAt
  · intro p hp
    have hpO := hball hp
    obtain ⟨e1, e2⟩ := hsec p hpO
    have hq : T.symm p ∈ Ω := hpO.2.2
    have hq' : (p.1, (T.symm p).2) ∈ Ω := e1 ▸ hq
    refine ⟨hq', by rw [← e1]; exact e2, fun v hv => ?_⟩
    have dΦ : DifferentiableAt ℂ Φ (T.symm p) := (hΦ _ hq).differentiableAt (hΩ.mem_nhds hq)
    have h1 := (hinr (T.symm p) dΦ).fderiv
    have h2 : (T.symm p).1 = p.1 := congrArg Prod.fst e1
    rw [h2] at h1
    rw [h1] at hv
    have dF : HasFDerivAt F ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod
        (fderiv ℂ Φ (T.symm p))) (T.symm p) := hasFDerivAt_fst.prodMk dΦ.hasFDerivAt
    have c : ContDiffAt ℂ 1 T.symm p := interior_subset hpO.1.2
    have dS : HasFDerivAt T.symm (fderiv ℂ T.symm p) (F (T.symm p)) := by
      rw [show F (T.symm p) = p from T.right_inv hpO.1.1]
      exact (c.differentiableAt one_ne_zero).hasFDerivAt
    have hcomp := dS.comp (T.symm p) dF
    have hid : HasFDerivAt (T.symm ∘ F) (ContinuousLinearMap.id ℂ _) (T.symm p) := by
      refine (hasFDerivAt_id (𝕜 := ℂ) (T.symm p)).congr_of_eventuallyEq ?_
      filter_upwards [T.open_source.mem_nhds (T.map_target hpO.1.1)] with q hq
      exact T.left_inv hq
    have hu := hcomp.unique hid
    have hv' : fderiv ℂ Φ (T.symm p) (0, v) = 0 := by simpa using hv
    have e0 : ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) (I → ℂ)).prod
        (fderiv ℂ Φ (T.symm p))) (0, v) = 0 := Prod.ext (by simp) (by simpa using hv')
    have h3 := DFunLike.congr_fun hu (0, v)
    rw [ContinuousLinearMap.comp_apply, e0, map_zero] at h3
    exact (congrArg Prod.snd h3).symm
  · intro b hb x hx
    have hbx : (b, x) ∈ ball (b₀, x₀) δ := by
      rw [← ball_prod_same]; exact ⟨by simpa using hb, by simpa using hx⟩
    obtain ⟨⟨h1, h2⟩, h3⟩ := hδ hbx
    have h3' : F (b, x) ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε := by
      rw [ball_prod_same]; exact h3
    exact ⟨h2, h3'.2, congrArg Prod.snd (T.left_inv h1)⟩

end GlobalTheory.CompanionTheory.HoloChart
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ImplicitFunctionHolomorphicStatement
open Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.implicit_function_holomorphic : ∀ (n : ℕ) (I J : Type) [Fintype I] [Fintype J] (Ω : Set ((Fin n → ℂ) × (I → ℂ))) (Φ : (Fin n → ℂ) × (I → ℂ) → (J → ℂ)) (b₀ : Fin n → ℂ) (x₀ : I → ℂ) (L : (I → ℂ) ≃L[ℂ] (J → ℂ)), IsOpen Ω → (b₀, x₀) ∈ Ω → DifferentiableOn ℂ Φ Ω → HasFDerivAt (fun x => Φ (b₀, x)) (L : (I → ℂ) →L[ℂ] (J → ℂ)) x₀ →
  ∃ (ε δ : ℝ) (X : (Fin n → ℂ) × (J → ℂ) → (I → ℂ)), 0 < ε ∧ 0 < δ ∧ X (b₀, Φ (b₀, x₀)) = x₀ ∧
    DifferentiableOn ℂ X (ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε) ∧
    (∀ p ∈ ball b₀ ε ×ˢ ball (Φ (b₀, x₀)) ε, (p.1, X p) ∈ Ω ∧ Φ (p.1, X p) = p.2 ∧
      ∀ v, fderiv ℂ (fun x => Φ (p.1, x)) (X p) v = 0 → v = 0) ∧
    ∀ b ∈ ball b₀ δ, ∀ x ∈ ball x₀ δ, (b, x) ∈ Ω ∧ Φ (b, x) ∈ ball (Φ (b₀, x₀)) ε ∧ X (b, Φ (b, x)) = x := by
  first | exact @GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters | exact GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters | (intros; apply GlobalTheory.CompanionTheory.HoloChart.holomorphic_inverse_with_parameters <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationDeterminesChart
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StdSmoothChart

open MvPolynomial

section Poly

variable {R ι : Type} [CommRing R]

theorem differentiableOn_eval₂ [Fintype ι] {n : ℕ} {B : Set (Fin n → ℂ)}
    (ψ : (Fin n → ℂ) → (R →+* ℂ)) (hψ : ∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B)
    (p : MvPolynomial ι R) :
    DifferentiableOn ℂ (fun bx : (Fin n → ℂ) × (ι → ℂ) => eval₂ (ψ bx.1) bx.2 p)
      (B ×ˢ Set.univ) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval₂_C]
    exact (hψ a).comp differentiableOn_fst (fun x hx => hx.1)
  | add p q hp hq =>
    simp only [eval₂_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [eval₂_mul, eval₂_X]
    exact hp.mul (differentiableOn_pi.1 differentiableOn_snd i)

def dirDeriv [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (p : MvPolynomial ι R) : ℂ :=
  ∑ i, eval₂ ψ x (pderiv i p) * v i

theorem dirDeriv_C [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (a : R) :
    dirDeriv ψ x v (C a) = 0 := by
  simp [dirDeriv]

theorem dirDeriv_add [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (p q : MvPolynomial ι R) :
    dirDeriv ψ x v (p + q) = dirDeriv ψ x v p + dirDeriv ψ x v q := by
  simp [dirDeriv, add_mul, Finset.sum_add_distrib]

theorem dirDeriv_mul [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (p q : MvPolynomial ι R) :
    dirDeriv ψ x v (p * q) = eval₂ ψ x p * dirDeriv ψ x v q + eval₂ ψ x q * dirDeriv ψ x v p := by
  simp only [dirDeriv, Derivation.leibniz, smul_eq_mul, eval₂_add, eval₂_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem dirDeriv_X [Fintype ι] [DecidableEq ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (i : ι) :
    dirDeriv ψ x v (X i) = v i := by
  simp [dirDeriv, pderiv_X, Pi.single_apply, apply_ite]

theorem hasFDerivAt_eval₂ [Fintype ι] [DecidableEq ι] (ψ : R →+* ℂ) (p : MvPolynomial ι R)
    (x : ι → ℂ) :
    HasFDerivAt (fun x => eval₂ ψ x p)
      (∑ i, eval₂ ψ x (pderiv i p) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i)
      x := by
  have h := ReciprocityTheory.ChartRestriction.G.Geo.Tor.hasFDerivAt_eval (map ψ p) x
  simp only [eval_map, pderiv_map] at h
  exact h

def dualEval (ψ : R →+* ℂ) (x v : ι → ℂ) : MvPolynomial ι R →+* DualNumber ℂ :=
  eval₂Hom ((TrivSqZeroExt.inlHom ℂ ℂ).comp ψ)
    (fun i => TrivSqZeroExt.inl (x i) + TrivSqZeroExt.inr (v i))

theorem dualEval_fst [Fintype ι] (ψ : R →+* ℂ) (x v : ι → ℂ) (p : MvPolynomial ι R) :
    (dualEval ψ x v p).fst = eval₂ ψ x p ∧ (dualEval ψ x v p).snd = dirDeriv ψ x v p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp [dualEval, dirDeriv_C]
  | add p q hp hq =>
    simp [map_add (f := _), hp.1, hp.2, hq.1, hq.2, dirDeriv_add]
  | mul_X p i hp =>
    have hX : dualEval ψ x v (X i) = TrivSqZeroExt.inl (x i) + TrivSqZeroExt.inr (v i) := by
      simp [dualEval]
    rw [map_mul, hX]
    refine ⟨by simp [hp.1], ?_⟩
    rw [dirDeriv_mul, dirDeriv_X]
    simp [hp.1, hp.2, mul_comm]
    ring

end Poly

section Pres

variable {R A ι σ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype σ]

theorem algebraMap_ring_eq (P : Algebra.SubmersivePresentation R A ι σ) (χ : A →+* ℂ)
    (p : MvPolynomial ι R) :
    χ (algebraMap P.Ring A p) =
      eval₂ (χ.comp (algebraMap R A)) (fun i => χ (P.val i)) p := by
  rw [P.algebraMap_apply, aeval_def, ← coe_eval₂Hom, map_eval₂Hom]
  rfl

theorem exists_lift (P : Algebra.SubmersivePresentation R A ι σ) {S : Type} [CommRing S]
    (f : MvPolynomial ι R →+* S) (hf : ∀ j, f (P.relation j) = 0) :
    ∃ χ : A →+* S, ∀ p : MvPolynomial ι R, χ (algebraMap P.Ring A p) = f p :=
  ⟨(algebraMap P.Ring A).liftOfSurjective P.algebraMap_surjective ⟨f, by
      show P.ker ≤ _
      rw [← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩; exact hf j⟩, fun p => RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩

theorem ringHom_ext (P : Algebra.SubmersivePresentation R A ι σ) {χ χ' : A →+* ℂ}
    (h : ∀ p : MvPolynomial ι R, χ (algebraMap P.Ring A p) = χ' (algebraMap P.Ring A p)) :
    χ = χ' := by
  refine RingHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
  exact h p

theorem der_eq_dirDeriv [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ) (χ : A →+* ℂ)
    (D : A →+ ℂ) (h0 : ∀ r, D (algebraMap R A r) = 0)
    (hL : ∀ x y, D (x * y) = χ x * D y + χ y * D x) (p : MvPolynomial ι R) :
    D (algebraMap P.Ring A p) =
      dirDeriv (χ.comp (algebraMap R A)) (fun i => χ (P.val i)) (fun i => D (P.val i)) p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [dirDeriv_C, show algebraMap P.Ring A (C a) = algebraMap R A a from
      (IsScalarTower.algebraMap_apply R P.Ring A a).symm]
    exact h0 a
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, dirDeriv_add]
  | mul_X p i hp =>
    have hX : algebraMap P.Ring A (X i) = P.val i := by simp
    rw [map_mul, hL, dirDeriv_mul, dirDeriv_X, hX, hp, algebraMap_ring_eq]
    simp

theorem exists_der [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ) (ψ : R →+* ℂ)
    (x v : ι → ℂ) (hx : ∀ j, eval₂ ψ x (P.relation j) = 0)
    (hv : ∀ j, dirDeriv ψ x v (P.relation j) = 0) (χ : A →+* ℂ)
    (hχ : ∀ p : MvPolynomial ι R, χ (algebraMap P.Ring A p) = eval₂ ψ x p) :
    ∃ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) ∧
      (∀ a b, D (a * b) = χ a * D b + χ b * D a) ∧
      ∀ p : MvPolynomial ι R, D (algebraMap P.Ring A p) = dirDeriv ψ x v p := by
  obtain ⟨E, hE⟩ := exists_lift P (dualEval ψ x v) (fun j => by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [(dualEval_fst ψ x v _).1, hx j]; rfl
    · rw [(dualEval_fst ψ x v _).2, hv j]; rfl)
  have hfst : ∀ a, (E a).fst = χ a := fun a => by
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    rw [hE, hχ, (dualEval_fst ψ x v _).1]
  refine ⟨⟨⟨fun a => (E a).snd, by simp⟩, fun a b => by simp⟩, fun r => ?_, fun a b => ?_,
    fun p => ?_⟩
  · show (E (algebraMap R A r)).snd = 0
    rw [IsScalarTower.algebraMap_apply R P.Ring A r, hE, (dualEval_fst ψ x v _).2]
    exact dirDeriv_C ψ x v r
  · show (E (a * b)).snd = χ a * (E b).snd + χ b * (E a).snd
    simp [map_mul, hfst, mul_comm]
  · show (E _).snd = _
    rw [hE, (dualEval_fst ψ x v _).2]

theorem exists_dir [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ)
    (χ : A →+* ℂ) (w : σ → ℂ) :
    ∃ v : ι → ℂ, ∀ j, dirDeriv (χ.comp (algebraMap R A)) (fun i => χ (P.val i)) v (P.relation j)
      = w j := by
  classical
  let ev : MvPolynomial ι R →+* ℂ :=
    eval₂Hom (χ.comp (algebraMap R A)) (fun i => χ (P.val i))
  let M : Matrix σ σ ℂ := ev.mapMatrix P.jacobiMatrix
  have dt : IsUnit M.det := by
    have : M.det = χ (algebraMap P.Ring A P.jacobiMatrix.det) := by
      rw [algebraMap_ring_eq]
      exact (RingHom.map_det ev _).symm
    rw [this, ← P.jacobian_eq_jacobiMatrix_det]
    exact P.jacobian_isUnit.map χ
  let u : σ → ℂ := Matrix.vecMul w M⁻¹
  have hu : Matrix.vecMul u M = w := by
    simp only [u, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ dt, Matrix.vecMul_one]
  refine ⟨fun i => ∑ j', if i = P.map j' then u j' else 0, fun j => ?_⟩
  have : ∀ j', ev (pderiv (P.map j') (P.relation j)) = M j' j := fun j' => by
    simp [M, P.jacobiMatrix_apply]
  rw [← hu]
  simp only [dirDeriv, Finset.mul_sum, Matrix.vecMul, dotProduct]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← this j', mul_comm]
  rfl

end Pres

end GlobalTheory.CompanionTheory.Ar.StdSmoothChart

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.StdSmoothChart

open MvPolynomial

section Family

variable {R A ι σ : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype σ]

theorem hasFDerivAt_family [Fintype ι] [DecidableEq ι] {J : Type} [Fintype J] (ψ : R →+* ℂ)
    (Q : J → MvPolynomial ι R) (x : ι → ℂ) :
    ∃ F : (ι → ℂ) →L[ℂ] (J → ℂ), HasFDerivAt (fun x j => eval₂ ψ x (Q j)) F x ∧
      ∀ v j, F v j = dirDeriv ψ x v (Q j) := by
  refine ⟨ContinuousLinearMap.pi fun j => ∑ i, eval₂ ψ x (pderiv i (Q j)) •
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i,
    hasFDerivAt_pi.2 fun j => hasFDerivAt_eval₂ ψ (Q j) x, fun v j => ?_⟩
  simp [dirDeriv]

theorem algebraMap_relation (P : Algebra.SubmersivePresentation R A ι σ) (j : σ) :
    algebraMap P.Ring A (P.relation j) = 0 := by
  rw [P.algebraMap_apply, P.aeval_val_relation]

theorem bijective_base [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ) (χ₀ : A →+* ℂ)
    {g : ℕ} (t : Fin g → A) (T : Fin g → MvPolynomial ι R)
    (hT : ∀ c, algebraMap P.Ring A (T c) = t c)
    (hinj : ∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) →
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0)
    (hsurj : ∀ c, ∃ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) ∧
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0)
    (F : (ι → ℂ) →L[ℂ] (σ ⊕ Fin g → ℂ))
    (hF : ∀ v j, F v j = dirDeriv (χ₀.comp (algebraMap R A)) (fun i => χ₀ (P.val i)) v
      (Sum.elim P.relation T j)) :
    Function.Bijective F := by
  classical
  constructor
  · refine (injective_iff_map_eq_zero F).2 fun v hv => ?_
    have hv' : ∀ j, dirDeriv (χ₀.comp (algebraMap R A)) (fun i => χ₀ (P.val i)) v
        (Sum.elim P.relation T j) = 0 := fun j => by rw [← hF, hv]; rfl
    obtain ⟨D, h0, hL, hD⟩ := exists_der P (χ₀.comp (algebraMap R A)) (fun i => χ₀ (P.val i)) v
      (fun j => by rw [← algebraMap_ring_eq, algebraMap_relation, map_zero])
      (fun j => hv' (Sum.inl j)) χ₀ (fun p => algebraMap_ring_eq P χ₀ p)
    have hD0 : D = 0 := hinj D h0 hL fun c => by
      rw [← hT c, hD]; exact hv' (Sum.inr c)
    funext i
    have := hD (X i)
    rw [hD0, dirDeriv_X] at this
    exact this.symm
  · intro w
    obtain ⟨v₁, hv₁⟩ := exists_dir P χ₀ (fun j => w (Sum.inl j))
    choose Dc h0 hL hDc using hsurj
    have hFc : ∀ c j, F (fun i => Dc c (P.val i)) j =
        Dc c (algebraMap P.Ring A (Sum.elim P.relation T j)) := fun c j => by
      rw [hF, der_eq_dirDeriv P χ₀ (Dc c) (h0 c) (hL c)]
    refine ⟨v₁ + ∑ c, (w (Sum.inr c) - F v₁ (Sum.inr c)) • (fun i => Dc c (P.val i)), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum]
    funext j
    simp only [map_smul, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hFc]
    rcases j with j | c'
    · simp only [Sum.elim_inl, algebraMap_relation, map_zero, mul_zero, Finset.sum_const_zero,
        add_zero]
      rw [hF]
      exact hv₁ j
    · simp only [Sum.elim_inr, hT, hDc, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring

theorem der_zero [Fintype ι] (P : Algebra.SubmersivePresentation R A ι σ) (χ : A →+* ℂ)
    (ψ : R →+* ℂ) (x : ι → ℂ) (hψ : χ.comp (algebraMap R A) = ψ)
    (hx : (fun i => χ (P.val i)) = x) {g : ℕ} (t : Fin g → A) (T : Fin g → MvPolynomial ι R)
    (hT : ∀ c, algebraMap P.Ring A (T c) = t c)
    (F : (ι → ℂ) →L[ℂ] (σ ⊕ Fin g → ℂ))
    (hF : ∀ v j, F v j = dirDeriv ψ x v (Sum.elim P.relation T j))
    (hinj : ∀ v, F v = 0 → v = 0)
    (D : A →+ ℂ) (h0 : ∀ r, D (algebraMap R A r) = 0)
    (hL : ∀ x y, D (x * y) = χ x * D y + χ y * D x) (ht : ∀ c, D (t c) = 0) : D = 0 := by
  subst hψ hx
  have hv := hinj (fun i => D (P.val i)) (funext fun j => by
    rw [hF, ← der_eq_dirDeriv P χ D h0 hL]
    rcases j with j | c
    · simp [algebraMap_relation]
    · simp [hT, ht])
  refine AddMonoidHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
  rw [der_eq_dirDeriv P χ D h0 hL, hv]
  simp [dirDeriv]

end Family

section Embed

variable {σ : Type} [Fintype σ] {g : ℕ}

theorem elim_mem_ball (z : Fin g → ℂ) {r : ℝ} (hr : 0 < r) (hz : z ∈ Metric.ball 0 r) :
    (Sum.elim 0 z : σ ⊕ Fin g → ℂ) ∈ Metric.ball (0 : σ ⊕ Fin g → ℂ) r := by
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  rintro (j | c)
  · simpa using hr
  · simpa using (dist_pi_lt_iff hr).1 (Metric.mem_ball.1 hz) c

theorem differentiable_elim :
    Differentiable ℂ (fun z : Fin g → ℂ => (Sum.elim 0 z : σ ⊕ Fin g → ℂ)) := by
  refine differentiable_pi.2 ?_
  rintro (j | c)
  · simpa using differentiable_const (0 : ℂ)
  · simpa using differentiable_apply c

end Embed

end GlobalTheory.CompanionTheory.Ar.StdSmoothChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.StdSmoothChart

theorem exists_sections : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsStandardSmooth R A] (n g : ℕ) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), IsOpen B → (∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B) → ∀ b₀ ∈ B, ∀ (χ₀ : A →+* ℂ) (t : Fin g → A), χ₀.comp (algebraMap R A) = ψ b₀ → (∀ c, χ₀ (t c) = 0) →
  (∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) → (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0) →
  (∀ c, ∃ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) ∧ (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0) →
  ∃ (N : ℕ) (f : Fin N → A) (ε δ : ℝ) (Ψ : (Fin n → ℂ) → (Fin g → ℂ) → (A →+* ℂ)), 0 < ε ∧ 0 < δ ∧ ball b₀ ε ⊆ B ∧ Ψ b₀ 0 = χ₀ ∧
    (∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, (Ψ b z).comp (algebraMap R A) = ψ b ∧ (∀ c, Ψ b z (t c) = z c) ∧
      ∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) → (∀ x y, D (x * y) = Ψ b z x * D y + Ψ b z y * D x) → (∀ c, D (t c) = 0) → D = 0) ∧
    (∀ a : A, DifferentiableOn ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψ bz.1 bz.2 a) (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε)) ∧
    (∀ c, ∃ j, f j = t c) ∧
    ∀ b ∈ ball b₀ δ, ∀ χ : A →+* ℂ, χ.comp (algebraMap R A) = ψ b → (∀ j, ‖χ (f j) - χ₀ (f j)‖ < δ) →
      (fun c => χ (t c)) ∈ ball (0 : Fin g → ℂ) ε ∧ χ = Ψ b (fun c => χ (t c)) := by
  intro R A _ _ _ _ n g B ψ hB hψ b₀ hb₀ χ₀ t h₀ ht hinj hsurj
  classical
  obtain ⟨I₀, K₀, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := A)
  letI := Fintype.ofFinite I₀
  letI := Fintype.ofFinite K₀
  choose T hT using fun c => P.algebraMap_surjective (t c)
  obtain ⟨Q, hQ⟩ : ∃ Q : K₀ ⊕ Fin g → MvPolynomial I₀ R, Q = Sum.elim P.relation T := ⟨_, rfl⟩
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : (Fin n → ℂ) × (I₀ → ℂ) → (K₀ ⊕ Fin g → ℂ),
      Φ = fun bx j => MvPolynomial.eval₂ (ψ bx.1) bx.2 (Q j) := ⟨_, rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : I₀ → ℂ, (fun i => χ₀ (P.val i)) = x₀ := ⟨_, rfl⟩
  have hΦ : DifferentiableOn ℂ Φ (B ×ˢ Set.univ) := by
    rw [hΦd]
    exact differentiableOn_pi.2 fun j => differentiableOn_eval₂ ψ hψ (Q j)
  have e₀ : ∀ p, MvPolynomial.eval₂ (ψ b₀) x₀ p = χ₀ (algebraMap P.Ring A p) := fun p => by
    rw [algebraMap_ring_eq, h₀, hx₀]

  have eQ : ∀ (b : Fin n → ℂ) (χ : A →+* ℂ), χ.comp (algebraMap R A) = ψ b →
      Φ (b, fun i => χ (P.val i)) = Sum.elim (0 : K₀ → ℂ) (fun c => χ (t c)) := fun b χ hχ => by
    funext j
    rw [hΦd]
    show MvPolynomial.eval₂ (ψ b) _ (Q j) = _
    rw [← hχ, ← algebraMap_ring_eq, hQ]
    rcases j with j | c
    · simp [algebraMap_relation]
    · simp [hT]
  have Φ₀ : Φ (b₀, x₀) = 0 := by
    rw [← hx₀, eQ b₀ χ₀ h₀]
    funext j
    rcases j with j | c
    · rfl
    · exact ht c
  obtain ⟨F₀, hF₀, hF₀v⟩ := hasFDerivAt_family (ψ b₀) Q x₀
  have bij : Function.Bijective F₀ := bijective_base P χ₀ t T hT hinj hsurj F₀ (by
    rw [h₀, hx₀, ← hQ]; exact hF₀v)
  obtain ⟨L, hL⟩ : ∃ L : (I₀ → ℂ) ≃L[ℂ] (K₀ ⊕ Fin g → ℂ),
      (L : (I₀ → ℂ) →L[ℂ] (K₀ ⊕ Fin g → ℂ)) = F₀ :=
    ⟨(LinearEquiv.ofBijective F₀.toLinearMap bij).toContinuousLinearEquiv, by ext; rfl⟩
  obtain ⟨ε', δ', X, ε'0, δ'0, hX₀, hXd, hX, hXinv⟩ := GlobalTheory.T.implicit_function_holomorphic n I₀ (K₀ ⊕ Fin g)
    (B ×ˢ Set.univ) Φ b₀ x₀ L (hB.prod isOpen_univ) ⟨hb₀, trivial⟩ hΦ (by
      rw [hL, hΦd]; exact hF₀)
  rw [Φ₀] at hX₀ hXd hX hXinv
  obtain ⟨ε'', ε''0, hε''⟩ := Metric.isOpen_iff.1 hB b₀ hb₀
  obtain ⟨ε, hε⟩ : ∃ ε, ε = min ε' ε'' := ⟨_, rfl⟩
  have ε0 : 0 < ε := hε ▸ lt_min ε'0 ε''0
  have εa : ε ≤ ε' := hε ▸ min_le_left _ _
  have εb : ε ≤ ε'' := hε ▸ min_le_right _ _
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = min δ' ε := ⟨_, rfl⟩
  have δ0 : 0 < δ := hδ ▸ lt_min δ'0 ε0
  have δa : δ ≤ δ' := hδ ▸ min_le_left _ _
  have δb : δ ≤ ε := hδ ▸ min_le_right _ _
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin g → ℂ) → (K₀ ⊕ Fin g → ℂ), emb = fun z => Sum.elim (0 : K₀ → ℂ) z :=
    ⟨_, rfl⟩
  have inU : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε,
      (b, emb z) ∈ ball b₀ ε' ×ˢ ball (0 : K₀ ⊕ Fin g → ℂ) ε' := fun b hb z hz => by
    refine ⟨ball_subset_ball εa hb, ?_⟩
    rw [hemb]
    exact ball_subset_ball εa (elim_mem_ball z ε0 hz)
  have hev : ∀ b x j, Φ (b, x) j = MvPolynomial.eval₂ (ψ b) x (Q j) := fun b x j => by rw [hΦd]
  have rel : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ∀ j,
      MvPolynomial.eval₂ (ψ b) (X (b, emb z)) (P.relation j) = 0 := fun b hb z hz j => by
    have := congrFun (hX _ (inU b hb z hz)).2.1 (Sum.inl j)
    rw [hev, hQ] at this
    rw [hemb] at this ⊢
    simpa using this
  have lf : ∀ (b : Fin n → ℂ) (x : I₀ → ℂ), (∀ j, MvPolynomial.eval₂ (ψ b) x (P.relation j) = 0) →
      ∃ χ : A →+* ℂ, ∀ p, χ (algebraMap P.Ring A p) = MvPolynomial.eval₂ (ψ b) x p :=
    fun b x hx => exists_lift P (MvPolynomial.eval₂Hom (ψ b) x) hx
  choose Ψ₀ hΨ₀ using lf
  obtain ⟨Ψ, hΨd⟩ : ∃ Ψ : (Fin n → ℂ) → (Fin g → ℂ) → (A →+* ℂ), Ψ = fun b z =>
      if h : b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε then Ψ₀ b _ (rel b h.1 z h.2 ) else χ₀ :=
    ⟨_, rfl⟩
  have hΨ : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, ∀ p,
      Ψ b z (algebraMap P.Ring A p) = MvPolynomial.eval₂ (ψ b) (X (b, emb z)) p :=
    fun b hb z hz p => by
      rw [hΨd]
      simp only [dif_pos (show b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε from ⟨hb, hz⟩)]
      exact hΨ₀ _ _ _ p
  have hcomp : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε,
      (Ψ b z).comp (algebraMap R A) = ψ b := fun b hb z hz => RingHom.ext fun r => by
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply R P.Ring A r, hΨ b hb z hz]
    exact MvPolynomial.eval₂_C _ _ _
  have hval : ∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε,
      (fun i => Ψ b z (P.val i)) = X (b, emb z) := fun b hb z hz => by
    funext i
    rw [show P.val i = algebraMap P.Ring A (MvPolynomial.X i) by simp, hΨ b hb z hz]
    exact MvPolynomial.eval₂_X _ _ _
  have emb0 : emb 0 = 0 := by
    rw [hemb]
    funext j
    rcases j with j | c <;> rfl
  have mb : b₀ ∈ ball b₀ ε := mem_ball_self ε0
  have m0 : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε := mem_ball_self ε0
  obtain ⟨e⟩ : Nonempty (I₀ ⊕ Fin g ≃ Fin (Fintype.card (I₀ ⊕ Fin g))) :=
    ⟨Fintype.equivFin _⟩
  refine ⟨_, fun j => Sum.elim P.val t (e.symm j), ε, δ, Ψ, ε0, δ0,
    (ball_subset_ball εb).trans hε'', ?_, ?_, ?_, ?_, ?_⟩
  · refine ringHom_ext P fun p => ?_
    rw [hΨ b₀ mb 0 m0, emb0, hX₀, e₀]
  · intro b hb z hz
    refine ⟨hcomp b hb z hz, fun c => ?_, fun D h0 hLD hDt => ?_⟩
    · have := congrFun (hX _ (inU b hb z hz)).2.1 (Sum.inr c)
      rw [hev, hQ, hemb] at this
      rw [← hT c, hΨ b hb z hz, hemb]
      simpa using this
    · obtain ⟨F, hF, hFv⟩ := hasFDerivAt_family (ψ b) Q (X (b, emb z))
      refine der_zero P (Ψ b z) (ψ b) (X (b, emb z)) (hcomp b hb z hz) (hval b hb z hz) t T hT F
        (by rw [← hQ]; exact hFv) (fun v hv => ?_) D h0 hLD hDt
      refine (hX _ (inU b hb z hz)).2.2 v ?_
      have hF' : HasFDerivAt (fun x => Φ (b, x)) F (X (b, emb z)) := by
        rw [hΦd]; exact hF
      show fderiv ℂ (fun x => Φ (b, x)) (X (b, emb z)) v = 0
      rw [hF'.fderiv, hv]
  · intro a
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    have hG : DifferentiableOn ℂ
        (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (bz.1, X (bz.1, emb bz.2)))
        (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) := by
      refine differentiableOn_fst.prodMk (hXd.comp (differentiableOn_fst.prodMk ?_) ?_)
      · rw [hemb]
        have hdz : Differentiable ℂ (fun z : Fin g → ℂ => (Sum.elim 0 z : K₀ ⊕ Fin g → ℂ)) :=
          differentiable_elim
        exact (hdz.comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin g → ℂ)).differentiable).differentiableOn
      · exact fun bz hbz => inU _ hbz.1 _ hbz.2
    refine DifferentiableOn.congr (f := fun bz : (Fin n → ℂ) × (Fin g → ℂ) =>
      MvPolynomial.eval₂ (ψ bz.1) (X (bz.1, emb bz.2)) p) ?_ fun bz hbz => hΨ _ hbz.1 _ hbz.2 p
    exact (differentiableOn_eval₂ ψ hψ p).comp hG fun bz hbz =>
      ⟨hε'' (ball_subset_ball εb hbz.1), trivial⟩
  · exact fun c => ⟨e (Sum.inr c), by simp⟩
  · intro b hb χ hχ hj
    have hb' : b ∈ ball b₀ ε := ball_subset_ball δb hb
    have hx : (fun i => χ (P.val i)) ∈ ball x₀ δ' := by
      refine (dist_pi_lt_iff δ'0).2 fun i => ?_
      have := hj (e (Sum.inl i))
      rw [← hx₀, dist_eq_norm]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl] at this
      exact this.trans_le δa
    have hz : (fun c => χ (t c)) ∈ ball (0 : Fin g → ℂ) ε := by
      refine (dist_pi_lt_iff ε0).2 fun c => ?_
      have := hj (e (Sum.inr c))
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, ht, sub_zero] at this
      rw [dist_eq_norm]
      simpa using this.trans_le δb
    refine ⟨hz, ?_⟩
    have hinv := (hXinv b (ball_subset_ball δa hb) _ hx).2.2
    rw [eQ b χ hχ] at hinv
    refine ringHom_ext P fun p => ?_
    rw [hΨ b hb' _ hz, hemb]
    show _ = MvPolynomial.eval₂ (ψ b) (X (b, Sum.elim (0 : K₀ → ℂ) fun c => χ (t c))) p
    rw [hinv, algebraMap_ring_eq, hχ]

end GlobalTheory.CompanionTheory.Ar.StdSmoothChart
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DerivationDeterminesChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_determines_chart : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsStandardSmooth R A] (n g : ℕ) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), IsOpen B → (∀ r : R, DifferentiableOn ℂ (fun b => ψ b r) B) → ∀ b₀ ∈ B, ∀ (χ₀ : A →+* ℂ) (t : Fin g → A), χ₀.comp (algebraMap R A) = ψ b₀ → (∀ c, χ₀ (t c) = 0) →
  (∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) → (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0) →
  (∀ c, ∃ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) ∧ (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0) →
  ∃ (N : ℕ) (f : Fin N → A) (ε δ : ℝ) (Ψ : (Fin n → ℂ) → (Fin g → ℂ) → (A →+* ℂ)), 0 < ε ∧ 0 < δ ∧ ball b₀ ε ⊆ B ∧ Ψ b₀ 0 = χ₀ ∧
    (∀ b ∈ ball b₀ ε, ∀ z ∈ ball (0 : Fin g → ℂ) ε, (Ψ b z).comp (algebraMap R A) = ψ b ∧ (∀ c, Ψ b z (t c) = z c) ∧
      ∀ D : A →+ ℂ, (∀ r, D (algebraMap R A r) = 0) → (∀ x y, D (x * y) = Ψ b z x * D y + Ψ b z y * D x) → (∀ c, D (t c) = 0) → D = 0) ∧
    (∀ a : A, DifferentiableOn ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψ bz.1 bz.2 a) (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε)) ∧
    (∀ c, ∃ j, f j = t c) ∧
    ∀ b ∈ ball b₀ δ, ∀ χ : A →+* ℂ, χ.comp (algebraMap R A) = ψ b → (∀ j, ‖χ (f j) - χ₀ (f j)‖ < δ) →
      (fun c => χ (t c)) ∈ ball (0 : Fin g → ℂ) ε ∧ χ = Ψ b (fun c => χ (t c)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.StdSmoothChart.exists_sections | exact GlobalTheory.CompanionTheory.Ar.StdSmoothChart.exists_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.StdSmoothChart.exists_sections <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHolomorphicExponentialChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.ExpChart GlobalTheory.HolHom in
theorem exp_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (N : ℕ) (f : Fin N → Γ(G.left, V)) (ε : ℝ) (Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ IsHolTo (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ bz.1 bz.2).left) ∧ (∀ b ∈ ball b₀ ε, Ψ b 0 = 1 ∧ (∀ a : Fin g, IsDerivAt0 (fun z => (Ψ b z).left) (Pi.single a 1) (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)) ∧ ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V ∧ ∀ a, valAt' (Ψ b z).left V (t a) = z a) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) → (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (fun a => valAt' x.left V (t a)) := open GlobalTheory.CompanionTheory.Ar.Flat.ExpChart GlobalTheory.HolHom in by
  intro R _ G _ _ g n M B ψ hsm hB b₀ hb₀
  obtain ⟨V, t, ρ, hV, hρ, hss, hθ, hrat⟩ := GlobalTheory.T.exists_exp_chart_standard_smooth R G g M (ψ b₀) hsm
  letI : Algebra R Γ(G.left, V) := (ExpChart.cst G.hom V).toAlgebra
  haveI : Algebra.IsStandardSmooth R Γ(G.left, V) := hss
  have halg : ∀ r, algebraMap R Γ(G.left, V) r = ExpChart.cst G.hom V r := fun _ => rfl
  have h₀ := (hθ (ψ b₀) hρ).1
  let χ₀ : Γ(G.left, V) →+* ℂ := evalHom (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V h₀
  have hχv : ∀ a, valAt' (1 : Over.mk (spMap (ψ b₀)) ⟶ G).left V a = χ₀ a := fun a => valR_eq _ _ h₀ a
  have hχc : χ₀.comp (algebraMap R Γ(G.left, V)) = ψ b₀ := RingHom.ext fun r => by
    show χ₀ (ExpChart.cst G.hom V r) = ψ b₀ r
    rw [← hχv]; exact val_cst V _ h₀ r
  have ht₀ : ∀ c, χ₀ (t c) = 0 := fun c => by rw [← hχv]; exact (hθ (ψ b₀) hρ).2.1 c
  have hder : ∀ (θ : R →+* ℂ) (a : Fin g), θ ρ ≠ 0 → ∃ D : Γ(G.left, V) →+ ℂ,
      (∀ f, D f = TrivSqZeroExt.snd (valR (spMap (dualMap θ) ≫ (M.pt (Pi.single a 1)).left) V f)) ∧
      (∀ r, D (ExpChart.cst G.hom V r) = 0) ∧
      (∀ f f', D (f * f') = valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f * D f' +
        valAt' (1 : Over.mk (spMap θ) ⟶ G).left V f' * D f) := by
    intro θ a hr
    have hin := (hθ θ hr).1
    obtain ⟨D, hD, hL⟩ := tan_der (tan_base M θ (Pi.single a 1)) hin
    refine ⟨D, hD, fun r => ?_, hL⟩
    have hv := (le_preimage_dual_iff (tan_base M θ (Pi.single a 1)) V).2 hin
    rw [hD, valR_eq _ _ hv, valR_cst G.hom V _ _ (tan_over M θ (Pi.single a 1)) hv]
    simp [TrivSqZeroExt.algebraMap_eq_inl']
  have hD₀ : ∀ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) →
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) → (∀ c, D (t c) = 0) → D = 0 := by
    intro D hc hl hz
    obtain ⟨c, hcD, -⟩ := GlobalTheory.T.derivation_vanishing_constants R G g M (ψ b₀) hsm V hV h₀ D hc (fun f f' => by
      rw [hχv, hχv]; exact hl f f')
    have hc0 : ∀ a, c a = 0 := fun a => by
      have := hcD (t a)
      rw [hz a] at this
      simp only [(hθ (ψ b₀) hρ).2.2] at this
      simpa using this.symm
    ext f
    rw [hcD f]
    simp [hc0]
  have hS₀ : ∀ c, ∃ D : Γ(G.left, V) →+ ℂ, (∀ r, D (algebraMap R _ r) = 0) ∧
      (∀ x y, D (x * y) = χ₀ x * D y + χ₀ y * D x) ∧ ∀ c', D (t c') = if c = c' then 1 else 0 := by
    intro c
    obtain ⟨D, hD, hc, hl⟩ := hder (ψ b₀) c hρ
    refine ⟨D, hc, fun x y => ?_, fun c' => ?_⟩
    · rw [hl, hχv, hχv]
    · rw [hD]; exact (hθ (ψ b₀) hρ).2.2 c c'
  obtain ⟨N, f, ε, δ, Ψa, hε, hδ, hεB, hΨ₀, hprop, hdiff, hft, huniq⟩ :=
    GlobalTheory.T.derivation_determines_chart R Γ(G.left, V) n g B ψ hB.1 hB.2 b₀ hb₀ χ₀ t hχc ht₀ hD₀ hS₀

  have hev : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 ∧
      ∀ j, ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ := by
    have hc : ∀ u, ContinuousAt (fun b => ψ b u) b₀ := fun u =>
      (hB.2 u).continuousOn.continuousAt (hB.1.mem_nhds hb₀)
    have h1 : ∀ᶠ b in 𝓝 b₀, ψ b ρ ≠ 0 := (hc ρ).eventually_ne hρ
    have h2 : ∀ j, ∀ᶠ b in 𝓝 b₀,
        ‖valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) - χ₀ (f j)‖ < δ := by
      intro j
      obtain ⟨u, k, hu⟩ := hrat (f j)
      have hq : ContinuousAt (fun b => ψ b u / ψ b ρ ^ k) b₀ := (hc u).div ((hc ρ).pow k) (pow_ne_zero k hρ)
      have hq0 : ψ b₀ u / ψ b₀ ρ ^ k = χ₀ (f j) := by
        rw [div_eq_iff (pow_ne_zero k hρ), ← hu _ hρ, hχv]
      have hb := hq.eventually (Metric.ball_mem_nhds _ hδ)
      filter_upwards [hb, h1] with b hb1 hb2
      have : valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V (f j) = ψ b u / ψ b ρ ^ k := by
        rw [eq_div_iff (pow_ne_zero k hb2)]; exact hu _ hb2
      rw [this, ← hq0]
      simpa [dist_eq_norm] using hb1
    filter_upwards [h1, eventually_all.2 h2] with b a1 a2 using ⟨a1, a2⟩
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ε', hε', h1', h2', h3'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε₁ ∧ ε' ≤ ε ∧ ε' ≤ δ :=
    ⟨min ε₁ (min ε δ), lt_min hε₁ (lt_min hε hδ), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hex : ∀ b z, ∃ x : Over.mk (spMap (ψ b)) ⟶ G, b ∈ ball b₀ ε → z ∈ ball (0 : Fin g → ℂ) ε →
      ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = Ψa b z a := by
    intro b z
    by_cases h : b ∈ ball b₀ ε ∧ z ∈ ball (0 : Fin g → ℂ) ε
    · obtain ⟨x, hx, hv⟩ := exists_pt hV (ψ b) (Ψa b z) (fun r => congrArg (fun q => q r) (hprop b h.1 z h.2).1)
      exact ⟨x, fun _ _ => ⟨hx, hv⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose Ψ hΨ using hex
  have hbε : ∀ b ∈ ball b₀ ε', b ∈ ball b₀ ε := fun b hb => ball_subset_ball h2' hb
  have hzε : ∀ z ∈ ball (0 : Fin g → ℂ) ε', z ∈ ball (0 : Fin g → ℂ) ε := fun b hb => ball_subset_ball h2' hb
  have hzero : (0 : Fin g → ℂ) ∈ ball (0 : Fin g → ℂ) ε' := mem_ball_self hε'
  have hone : ∀ b ∈ ball b₀ ε', Ψ b 0 = 1 := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := hball b (ball_subset_ball h1' hb)
    have hin := (hθ (ψ b) hb1).1
    have hc : (evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin).comp (algebraMap R Γ(G.left, V)) = ψ b :=
      RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w _) hin r
    have hv : ∀ a, evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin a = valAt' (1 : Over.mk (spMap (ψ b)) ⟶ G).left V a :=
      fun a => (valR_eq _ _ hin a).symm
    have := (huniq b (ball_subset_ball h3' hb) _ hc (fun j => by rw [hv]; exact hb2 j)).2
    have hz : (fun c => evalHom (1 : Over.mk (spMap (ψ b)) ⟶ G).left V hin (t c)) = 0 := by
      funext c
      rw [hv]; exact (hθ (ψ b) hb1).2.1 c
    rw [hz] at this
    obtain ⟨hx, hvx⟩ := hΨ b 0 (hbε b hb) (hzε 0 hzero)
    refine pt_ext hV hx hin fun a => ?_
    rw [hvx, ← this, hv]
  have hHol : ∀ p ∈ ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε', HolAt (fun q : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ q.1 q.2).left) p := by
    intro p hp
    have hop : IsOpen (ball b₀ ε' ×ˢ ball (0 : Fin g → ℂ) ε') := isOpen_ball.prod isOpen_ball
    have hnb := hop.mem_nhds hp
    have hop' : IsOpen (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) := isOpen_ball.prod isOpen_ball
    refine holAt_of_affine hV (hΨ _ _ (hbε _ hp.1) (hzε _ hp.2)).1 ?_ fun a => ?_
    · filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).1
    · have hd : DifferentiableAt ℂ (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => Ψa bz.1 bz.2 a) p :=
        (hdiff a).differentiableAt (hop'.mem_nhds ⟨hbε _ hp.1, hzε _ hp.2⟩)
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [hnb] with q hq using (hΨ _ _ (hbε _ hq.1) (hzε _ hq.2)).2 a
  have hfib : ∀ b ∈ ball b₀ ε', HolAt (fun z => (Ψ b z).left) 0 := by
    intro b hb
    have := (hHol (b, 0) ⟨hb, hzero⟩).precomp (k := fun z : Fin g → ℂ => (b, z)) (z := 0)
      ((differentiableAt_const b).prodMk differentiableAt_id)
    exact this
  refine ⟨V, t, N, f, ε', Ψ, hε', (ball_subset_ball h2').trans hεB, ?_, fun b hb => ⟨hone b hb, fun a => ?_, fun z hz => ?_⟩, ε', hε', fun b hb x hxV hnear => ?_⟩
  · exact isHolTo_of_holAt (isOpen_ball.prod isOpen_ball) hHol
  ·
    obtain ⟨hb1, -⟩ := hball b (ball_subset_ball h1' hb)
    obtain ⟨hx, hvx⟩ := hΨ b 0 (hbε b hb) (hzε 0 hzero)
    obtain ⟨v', hv'⟩ := (hfib b hb).exists_isDerivAt (Pi.single a 1)
    have hb' : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left) = (Ψ b 0).left := by
      rw [tan_base M (ψ b) (Pi.single a 1), hone b hb]
    obtain ⟨D₁, hD₁, hL₁⟩ := tan_der hv'.1 hx
    obtain ⟨D₂, hD₂, hL₂⟩ := tan_der hb' hx
    have hnb : ball (0 : Fin g → ℂ) ε' ∈ 𝓝 (0 : Fin g → ℂ) := ball_mem_nhds _ hε'
    have hval : ∀ c, D₁ (t c) = if a = c then 1 else 0 := by
      intro c
      have e : (fun z => valAt' (Ψ b z).left V (t c)) =ᶠ[𝓝 0] fun z => z c := by
        filter_upwards [hnb] with z hz
        rw [(hΨ b z (hbε b hb) (hzε z hz)).2]
        exact (hprop b (hbε b hb) z (hzε z hz)).2.1 c
      rw [hD₁, hv'.2 V hx, e.fderiv_eq, (hasFDerivAt_apply c (0 : Fin g → ℂ)).fderiv]
      simp [Pi.single_apply, eq_comm]
    have hcon1 : ∀ r, D₁ (ExpChart.cst G.hom V r) = 0 := by
      intro r
      have e : (fun z => valAt' (Ψ b z).left V (ExpChart.cst G.hom V r)) =ᶠ[𝓝 0] fun _ => ψ b r := by
        filter_upwards [hnb] with z hz
        exact val_cst V _ (hΨ b z (hbε b hb) (hzε z hz)).1 r
      rw [hD₁, hv'.2 V hx, e.fderiv_eq]
      simp
    obtain ⟨D₃, hD₃, hcon2, -⟩ := hder (ψ b) a hb1
    have hD23 : ∀ f, D₂ f = D₃ f := fun f => by rw [hD₂, hD₃]
    have hz : D₁ - D₂ = 0 := by
      refine (hprop b (hbε b hb) 0 (hzε 0 hzero)).2.2 _ (fun r => ?_) (fun x y => ?_) (fun c => ?_)
      · show D₁ (ExpChart.cst G.hom V r) - D₂ (ExpChart.cst G.hom V r) = 0
        rw [hcon1, hD23, hcon2, sub_zero]
      · simp only [AddMonoidHom.sub_apply]
        rw [hL₁, hL₂, hvx, hvx]
        ring
      · simp only [AddMonoidHom.sub_apply]
        rw [hval, hD₂, (hθ (ψ b) hb1).2.2 a c, sub_self]
    have heq : v' = spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left := by
      refine point_ext hV ((le_preimage_dual_iff hv'.1 V).2 hx) ((le_preimage_dual_iff hb' V).2 hx) fun f => ?_
      refine TrivSqZeroExt.ext ((fst_valR hv'.1 hx f).trans (fst_valR hb' hx f).symm) ?_
      have := DFunLike.congr_fun hz f
      simp only [AddMonoidHom.sub_apply, AddMonoidHom.zero_apply, sub_eq_zero] at this
      rw [← hD₁, ← hD₂, this]
    rw [← heq]
    exact (isDerivAt0_iff _ _ _).2 hv'
  · obtain ⟨hx, hvx⟩ := hΨ b z (hbε b hb) (hzε z hz)
    refine ⟨hx, fun a => ?_⟩
    rw [hvx]
    exact (hprop b (hbε b hb) z (hzε z hz)).2.1 a
  · have hbδ := ball_subset_ball h3' hb
    have hc : (evalHom x.left V hxV).comp (algebraMap R Γ(G.left, V)) = ψ b :=
      RingHom.ext fun r => valR_cst G.hom V _ _ (Over.w x) hxV r
    have hv : ∀ a, evalHom x.left V hxV a = valAt' x.left V a := fun a => (valR_eq _ _ hxV a).symm
    have hΨb₀ : ∀ a, valAt' (Ψ b₀ 0).left V a = χ₀ a := fun a => by
      rw [(hΨ b₀ 0 (mem_ball_self hε) (hzε 0 hzero)).2, hΨ₀]
    have hn : ∀ j, ‖evalHom x.left V hxV (f j) - χ₀ (f j)‖ < δ := fun j => by
      rw [hv, ← hΨb₀]
      exact (hnear j).trans_le h3'
    obtain ⟨-, hχ⟩ := huniq b hbδ _ hc hn
    have hmem : (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε' := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff hε']
      intro c
      obtain ⟨j, hj⟩ := hft c
      have := hnear j
      rw [hΨb₀, hj, ht₀, sub_zero] at this
      exact this
    refine ⟨hmem, ?_⟩
    obtain ⟨hx, hvx⟩ := hΨ b _ (hbε b hb) (hzε _ hmem)
    refine pt_ext hV hxV hx fun a => ?_
    rw [hvx, ← hv, hχ]
    simp only [hv]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHolomorphicExponentialChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_holomorphic_exponential_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Smooth G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∃ (V : G.left.Opens) (t : Fin g → Γ(G.left, V)) (N : ℕ) (f : Fin N → Γ(G.left, V)) (ε : ℝ) (Ψ : ∀ b : Fin n → ℂ, (Fin g → ℂ) → (Over.mk (spMap (ψ b)) ⟶ G)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ IsHolTo (ball b₀ ε ×ˢ ball (0 : Fin g → ℂ) ε) (fun bz : (Fin n → ℂ) × (Fin g → ℂ) => (Ψ bz.1 bz.2).left) ∧ (∀ b ∈ ball b₀ ε, Ψ b 0 = 1 ∧ (∀ a : Fin g, IsDerivAt0 (fun z => (Ψ b z).left) (Pi.single a 1) (spMap (dualMap (ψ b)) ≫ (M.pt (Pi.single a 1)).left)) ∧ ∀ z ∈ ball (0 : Fin g → ℂ) ε, ⊤ ≤ (Ψ b z).left ⁻¹ᵁ V ∧ ∀ a, valAt' (Ψ b z).left V (t a) = z a) ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ b ∈ ball b₀ δ, ∀ x : Over.mk (spMap (ψ b)) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V → (∀ j, ‖valAt' x.left V (f j) - valAt' (Ψ b₀ 0).left V (f j)‖ < δ) → (fun a => valAt' x.left V (t a)) ∈ ball (0 : Fin g → ℂ) ε ∧ x = Ψ b (fun a => valAt' x.left V (t a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exp_chart | exact GlobalTheory.CompanionTheory.Ar.Flat.exp_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exp_chart <;> assumption)
end
