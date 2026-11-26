module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.CoordSpan
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.ExistsNonzeroPhysicalHighestWeightVectorTensFock
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.VNormSqLowKSubRootLt

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.SignedActionTensor
noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section Gen

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem mem_highestWeightSub_iff (ε : Fin n → Bool) (F : Fin n → Fin n → Module.End ℂ W) (γ : Fin n → ℝ) (x : W) :
    x ∈ khwSub ε F γ ↔ IsKHWVec ε F γ x := by
  simp only [khwSub, IsKHWVec, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b hab he => h2 a b ⟨hab, he⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun a b h => h2 a b h.1 h.2⟩

theorem support_subset_physicalModes {ε : Fin n → Bool} {z : TensorProduct ℂ W (Fock n)} (hz : z ∈ physicalSubspace ε)
    {s : Finset (Fin (n * n))} (hs : tcoef ((fockBasis n).coord s) z ≠ 0) : s ⊆ lfPhysModes ε := by
  intro m hm
  by_contra hnot
  obtain ⟨x, rfl⟩ := finProdFinEquiv.surjective m
  have hx : ¬ (ε x.1 = true ∧ ε x.2 = false) := fun h => hnot ((lf_mem_phys ε x.1 x.2).2 h)
  have h0 : cmT (N := W) x.1 x.2 z = 0 := by
    simp only [physicalSubspace, Submodule.mem_iInf, LinearMap.mem_ker] at hz
    exact hz x.1 x.2 hx
  have h1 : LinearMap.lTensor W (cpFock x.1 x.2 ∘ₗ cmFock x.1 x.2) z = 0 := by
    rw [LinearMap.lTensor_comp, LinearMap.comp_apply]
    have : LinearMap.lTensor W (cmFock x.1 x.2) z = 0 := h0
    rw [this, map_zero]
  have h2 := congrArg (tcoef ((fockBasis n).coord s)) h1
  rw [tcoef_lTensor, gc_coord_num x s, if_pos hm, one_smul, map_zero] at h2
  exact hs h2

theorem signedAction_tensor (ε : Fin n → Bool) (a b : Fin n) :
    sgE ε (cpT (N := W) (n := n)) cmT a b = LinearMap.lTensor W (sgE ε cpFock cmFock a b) := by
  apply TensorProduct.ext'
  intro m f
  unfold sgE
  split_ifs <;> simp [cpT, cmT, LinearMap.sum_apply, TensorProduct.tmul_sum]

end Gen

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem line_exists {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W) :
    ∃ z ∈ lineSub ε E lam W, z ≠ 0 := by
  obtain ⟨x, hxT, hxP, hx0, hxK⟩ := lowFock_exists ε hE hlam hW
  exact ⟨x, ⟨⟨(mem_highestWeightSub_iff _ _ _ x).2 hxK, hxT⟩, hxP⟩, hx0⟩

theorem tensorCoeff_diagAction (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (a : Fin n)
    (s : Finset (Fin (n * n))) (z : TensorProduct ℂ M (Fock n)) :
    tcoef ((fockBasis n).coord s) (diagE ε (eT E) cpT cmT a a z) =
      E a a (tcoef ((fockBasis n).coord s) z) + ((fockWt ε s a : ℝ) : ℂ) • tcoef ((fockBasis n).coord s) z := by
  rw [diagE, LinearMap.add_apply, map_add (f := _), signedAction_tensor, eT, tcoef_map_left, tcoef_lTensor, coord_comp_sg, tcoef_smul]

theorem line_deg {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W)
    {z : TensorProduct ℂ M (Fock n)} (hz : z ∈ lineSub ε E lam W) :
    z ∈ LinearMap.range (TensorProduct.map W.subtype (⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ)).subtype) := by
  obtain ⟨⟨hK, hT⟩, hP⟩ := hz
  replace hK := (mem_highestWeightSub_iff _ _ _ z).1 hK
  have hdeg : ∀ s, tcoef ((fockBasis n).coord s) z ≠ 0 → s.card = sDeg ε := by
    intro s hs
    have hsub := support_subset_physicalModes hP hs
    have hmem : tcoef ((fockBasis n).coord s) z ∈ W := tcoef_mem hT _
    have hEa : ∀ a, E a a (tcoef ((fockBasis n).coord s) z) =
        (((gaW ε lam a - fockWt ε s a : ℝ) : ℂ)) • tcoef ((fockBasis n).coord s) z := by
      intro a
      have h := congrArg (tcoef ((fockBasis n).coord s)) (hK.1 a)
      rw [tensorCoeff_diagAction, map_smul] at h
      rw [Complex.ofReal_sub, sub_smul, ← h]
      abel
    have hZ := zPlus_V hE hW _ hmem
    have hZ' : zPlus ε E (tcoef ((fockBasis n).coord s) z) =
        (∑ c ∈ plusIdx ε, (((gaW ε lam c - fockWt ε s c : ℝ) : ℂ))) • tcoef ((fockBasis n).coord s) z := by
      unfold zPlus
      rw [LinearMap.sum_apply, Finset.sum_smul]
      exact Finset.sum_congr rfl fun c _ => hEa c
    rw [hZ] at hZ'
    have hc : (∑ c ∈ plusIdx ε, ((lowK ε lam c : ℝ) : ℂ)) = ∑ c ∈ plusIdx ε, (((gaW ε lam c - fockWt ε s c : ℝ) : ℂ)) :=
      smul_left_injective ℂ hs hZ'
    have hr : (∑ c ∈ plusIdx ε, lowK ε lam c) = ∑ c ∈ plusIdx ε, (gaW ε lam c - fockWt ε s c) := by
      exact_mod_cast hc
    rw [Finset.sum_sub_distrib, gc_plus_sum hsub] at hr
    have h2 := sDeg_eq_sum ε
    have h3 : (sDeg ε : ℝ) = (s.card : ℝ) := by
      rw [h2]
      have : ∀ c, (rhoHol ε - rhoN ε) c = gaW ε lam c - lowK ε lam c := by
        intro c
        simp only [gaW, lowK, Pi.add_apply, Pi.sub_apply]
        ring
      rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_sub_distrib]
      linarith
    exact_mod_cast h3.symm
  rw [tcoef_expand z]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : tcoef ((fockBasis n).coord s) z = 0
  · rw [hs, TensorProduct.zero_tmul]
    exact Submodule.zero_mem _
  · have hb : fockBasis n s ∈ ⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ) := by
      rw [← hdeg s hs]
      exact gs_basis_deg s
    exact ⟨(⟨tcoef ((fockBasis n).coord s) z, tcoef_mem hT _⟩ : W) ⊗ₜ (⟨fockBasis n s, hb⟩ : ⋀[ℂ]^(sDeg ε) (Fin n × Fin n → ℂ)), by
      simp [TensorProduct.map_tmul]⟩

theorem line_ker {ε : Fin n → Bool} {lam : Fin n → ℝ} {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) {W : Submodule ℂ M} (hW : IsKIrrHW ε E (lowK ε lam) W)
    (hc : ∀ v ∈ W, casimir E v = ((casVal lam : ℝ) : ℂ) • v)
    {z : TensorProduct ℂ M (Fock n)} (hz : z ∈ lineSub ε E lam W) : (dOp ε (eT E) cpT + dOp' ε (eT E) cmT) z = 0 := by
  obtain ⟨⟨hK, hT⟩, hP⟩ := hz
  replace hK := (mem_highestWeightSub_iff _ _ _ z).1 hK
  have hKv : IsKHWVec ε (diagE ε (eT E) cpT cmT) ((lam - rhoC ε) + rhoHol ε) z := hK
  have hcas : casimir (eT (n := n) E) z = ((casVal lam : ℝ) : ℂ) • z := by
    rw [ssh_casimir_eT]
    obtain ⟨y, rfl⟩ := hT
    have hcomp : casimir E ∘ₗ W.subtype = ((casVal lam : ℝ) : ℂ) • W.subtype := by
      ext v
      simp [hc v v.2]
    rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.id_comp, hcomp, TensorProduct.map_smul_left,
      LinearMap.smul_apply]
  have h2 := two_D_sq_khw (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) hKv hcas
  have hzero : (((nsq (lam - rhoC ε + rhoC ε) - nsq (rho n) : ℝ) : ℂ) - ((casVal lam : ℝ) : ℂ)) = 0 := by
    rw [sub_add_cancel, casVal, sub_self]
  rw [hzero, zero_smul] at h2
  set D := dOp ε (eT E) cpT + dOp' ε (eT E) cmT with hD
  have hDD : D (D z) = 0 := by
    have h3 : (2 : ℂ) • (D * D) z = 0 := h2
    rw [smul_eq_zero] at h3
    rcases h3 with h3 | h3
    · norm_num at h3
    · exact h3
  have hf : tform (D z) (D z) = 0 := by
    rw [hD, tform_D hU, ← hD, hDD]
    unfold tform
    simp
  by_contra hne
  have := tform_self_re_pos hne
  rw [hf] at this
  simp at this

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ}

section Gen

variable {X : Type*} [AddCommGroup X] [Module ℂ X] {A : Fin n → Fin n → Module.End ℂ X}

theorem exists_joint_eigenvector_alt (hcomm : ∀ a c (v : X), A a a (A c c v) = A c c (A a a v)) (s : Finset (Fin n)) :
    ∀ T : Submodule ℂ X, FiniteDimensional ℂ T → (∀ c, ∀ v ∈ T, A c c v ∈ T) → T ≠ ⊥ →
      ∃ w ∈ T, w ≠ 0 ∧ ∃ μ : Fin n → ℂ, ∀ c ∈ s, A c c w = μ c • w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro T _ _ hT
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
    exact ⟨w, hw, hw0, 0, by simp⟩
  | insert a s ha ih =>
    intro T hfd hst hT
    have : Nontrivial T := Submodule.nontrivial_iff_ne_bot.mpr hT
    let f : Module.End ℂ T := (A a a).restrict (fun v hv => hst a v hv)
    obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue f
    obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
    have hv1 : f v = lam • v := Module.End.mem_eigenspace_iff.mp hv.1
    have hv2 : (v : X) ≠ 0 := fun h => hv.2 (Subtype.ext h)
    have hv3 : A a a v = lam • (v : X) := by
      have := congrArg Subtype.val hv1
      simpa [f] using this
    let T' : Submodule ℂ X := T ⊓ Module.End.eigenspace (A a a) lam
    have hfd' : FiniteDimensional ℂ T' := Submodule.finiteDimensional_of_le inf_le_left
    have hst' : ∀ c, ∀ u ∈ T', A c c u ∈ T' := by
      intro c u hu
      refine ⟨hst c u hu.1, ?_⟩
      have h2 : A a a u = lam • u := Module.End.mem_eigenspace_iff.mp hu.2
      show A c c u ∈ Module.End.eigenspace (A a a) lam
      rw [Module.End.mem_eigenspace_iff, hcomm a c u, h2, map_smul]
    have hT' : T' ≠ ⊥ := by
      intro h
      have : (v : X) ∈ T' := ⟨v.2, Module.End.mem_eigenspace_iff.mpr hv3⟩
      rw [h, Submodule.mem_bot] at this
      exact hv2 this
    obtain ⟨w, hw, hw0, μ, hμ⟩ := ih T' hfd' hst' hT'
    refine ⟨w, hw.1, hw0, Function.update μ a lam, ?_⟩
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · rw [Function.update_self]
      exact Module.End.mem_eigenspace_iff.mp hw.2
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      rw [Function.update_of_ne hca]
      exact hμ c hc

theorem exists_highestWeight_general (ε : Fin n → Bool)
    (hK : ∀ a b c d, ε a = ε b → ε c = ε d →
      A a b * A c d - A c d * A a b = (if b = c then A a d else 0) - (if d = a then A c b else 0))
    (hreal : ∀ c (w : X) (z : ℂ), w ≠ 0 → A c c w = z • w → z = ((z.re : ℝ) : ℂ))
    {S : Submodule ℂ X} (hfd : FiniteDimensional ℂ S) (hS : IsKStableSub ε A S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε A μ w := by
  classical
  have hcomm : ∀ a c (v : X), A a a (A c c v) = A c c (A a a v) := by
    intro a c v
    have h := LinearMap.congr_fun (hK a a c c rfl rfl) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    by_cases hac : a = c
    · subst hac; rfl
    · simp only [if_neg hac, if_neg (Ne.symm hac), LinearMap.zero_apply, sub_zero, sub_eq_zero] at h
      exact h
  have hshift : ∀ {μ : Fin n → ℝ} {w : X}, (∀ c, A c c w = (μ c : ℂ) • w) → ∀ {a b : Fin n}, a ≠ b → ε a = ε b →
      ∀ c, A c c (A a b w) = ((μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0) : ℝ) : ℂ) • A a b w := by
    intro μ w hw a b hab hεab c
    have h := LinearMap.congr_fun (hK c c a b rfl hεab) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hw c, map_smul] at h
    by_cases hca : c = a
    · subst hca
      simp [hab, Ne.symm hab] at h ⊢
      linear_combination (norm := module) h
    · by_cases hcb : c = b
      · subst hcb
        simp [hca] at h ⊢
        linear_combination (norm := module) h
      · simp [hca, hcb, Ne.symm hcb] at h ⊢
        linear_combination (norm := module) h
  have hSc : ∀ c, ∀ v ∈ S, A c c v ∈ S := fun c => hS c c rfl
  let P : Set (Fin n → ℝ) := {μ | ∃ w ∈ S, w ≠ 0 ∧ ∀ c, A c c w = (μ c : ℂ) • w}
  have hPfin : P.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (r : ℂ)})
      (fun c => (Module.End.finite_hasEigenvalue _).preimage
        (Complex.ofReal_injective.injOn))).subset ?_
    rintro μ ⟨w, hw, hw0, hμ⟩ c -
    show Module.End.HasEigenvalue ((A c c).restrict (hSc c)) (μ c : ℂ)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨w, hw⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa using hμ c)
    · intro h
      exact hw0 (congrArg Subtype.val h)
  have hPne : P.Nonempty := by
    obtain ⟨w, hw, hw0, z, hz⟩ := exists_joint_eigenvector_alt hcomm Finset.univ S hfd hSc hne
    refine ⟨fun c => (z c).re, w, hw, hw0, fun c => ?_⟩
    rw [hz c (Finset.mem_univ c)]
    congr 1
    exact hreal c w (z c) hw0 (hz c (Finset.mem_univ c))
  obtain ⟨μ, ⟨w, hw, hw0, hμ⟩, hmax⟩ := Set.exists_max_image P kUnitWtLin hPfin hPne
  refine ⟨w, hw, hw0, μ, hμ, ?_⟩
  intro a b hab hεab
  by_contra h
  have hmem : (fun c => μ c + (if c = a then 1 else 0) - (if c = b then 1 else 0)) ∈ P :=
    ⟨A a b w, hS a b hεab w hw, h, fun c => hshift hμ (ne_of_lt hab) hεab c⟩
  exact absurd (hmax _ hmem) (not_le.mpr (kUnitWtLin_shift μ hab))

end Gen

section Alg

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem diagAction_commutator {W : Type*} [AddCommGroup W] [Module ℂ W] {E cp cm : Fin n → Fin n → Module.End ℂ W}
    (hE : IsGlRep E) (hC : IsCAR cp cm) (hEC : CommutesCAR E cp cm) (ε : Fin n → Bool)
    (a b c d : Fin n) (hab : ε a = ε b) (hcd : ε c = ε d) :
    diagE ε E cp cm a b * diagE ε E cp cm c d - diagE ε E cp cm c d * diagE ε E cp cm a b =
      (if b = c then diagE ε E cp cm a d else 0) - (if d = a then diagE ε E cp cm c b else 0) := by
  have e1 := hE a b c d
  have e2 := sgE_comm hC ε a b c d hab hcd
  have h1 := E_comm_sgE hEC ε a b c d
  have h2 := E_comm_sgE hEC ε c d a b
  have key : (E a b + sgE ε cp cm a b) * (E c d + sgE ε cp cm c d) -
      (E c d + sgE ε cp cm c d) * (E a b + sgE ε cp cm a b) =
      (E a b * E c d - E c d * E a b) + (sgE ε cp cm a b * sgE ε cp cm c d - sgE ε cp cm c d * sgE ε cp cm a b) := by
    simp only [add_mul, mul_add]
    rw [h1, ← h2]
    abel
  unfold diagE
  rw [key, e1, e2]
  split_ifs <;> abel

theorem tmul_mem_tensorFock {S : Submodule ℂ N} {v : N} (hv : v ∈ S) (f : Fock n) :
    v ⊗ₜ f ∈ tensFock (n := n) S :=
  ⟨⟨v, hv⟩ ⊗ₜ f, by simp [TensorProduct.map_tmul]⟩

theorem mem_tensorFock_of_coeffs {S : Submodule ℂ N} {y : TensorProduct ℂ N (Fock n)}
    (hy : ∀ s, tcoef ((fockBasis n).coord s) y ∈ S) : y ∈ tensFock S := by
  rw [tcoef_expand y]
  exact Submodule.sum_mem _ fun s _ => tmul_mem_tensorFock (hy s) _

theorem tensorFock_finiteDimensional {S : Submodule ℂ N} (hS : FiniteDimensional ℂ S) :
    FiniteDimensional ℂ (tensFock (n := n) S) := by
  have : Module.Finite ℂ (Fock n) := Module.Finite.of_basis (fockBasis n)
  exact LinearMap.finiteDimensional_range _

theorem tensorFock_mono {S T : Submodule ℂ N} (h : S ≤ T) : tensFock (n := n) S ≤ tensFock T := by
  intro y hy
  exact mem_tensorFock_of_coeffs fun s => h (tcoef_mem hy _)

theorem tensorFock_diagAction_stable (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ N} {S : Submodule ℂ N}
    (hS : IsKStableSub ε E S) {a b : Fin n} (hab : ε a = ε b) {y : TensorProduct ℂ N (Fock n)}
    (hy : y ∈ tensFock S) : diagE ε (eT E) cpT cmT a b y ∈ tensFock S := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v f =>
    rw [diagE, LinearMap.add_apply, signedAction_tensor]
    refine add_mem ?_ ?_
    · simp only [eT, TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply]
      exact tmul_mem_tensorFock (hS a b hab _ v.2) f
    · simp only [TensorProduct.map_tmul, LinearMap.id_apply, Submodule.subtype_apply, LinearMap.lTensor_tmul]
      exact tmul_mem_tensorFock v.2 _
  | add x x' hx hx' =>
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem hx hx'

end Alg

section Form

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem tensorForm_smul_left (c : ℂ) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (c • y) y' = star c * tform y y' := by
  rw [← tform_conj y' (c • y), tform_smul_right, star_mul', tform_conj]

theorem tensorForm_signedAction_adjoint (ε : Fin n → Bool) (a b : Fin n) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (sgE ε cpT cmT a b y) y' = tform y (sgE ε cpT cmT b a y') := by
  unfold sgE
  have s1 : (ε b = true ∧ ε a = true) ↔ (ε a = true ∧ ε b = true) := and_comm
  have s2 : (ε b = false ∧ ε a = false) ↔ (ε a = false ∧ ε b = false) := and_comm
  simp only [s1, s2]
  split_ifs with h1 h2
  · simp only [LinearMap.sum_apply, Module.End.mul_apply, tform_sum_left, tform_sum_right]
    refine sum_congr rfl fun x _ => ?_
    rw [tform_cpT, tform_cmT]
  · simp only [LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply, tform_neg_left,
      tform_neg_right, tform_sum_left, tform_sum_right]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [tform_cpT, tform_cmT]
  · simp [tform]

theorem tensorForm_diagAction_adjoint {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {a b : Fin n} (hab : ε a = ε b) (y y' : TensorProduct ℂ M (Fock n)) :
    tform (diagE ε (eT E) cpT cmT a b y) y' = tform y (diagE ε (eT E) cpT cmT b a y') := by
  simp only [diagE, LinearMap.add_apply, tform_add_left, tform_add_right, tform_eT hU, tensorForm_signedAction_adjoint]
  simp [adjSign, hab]

theorem exists_highestWeight_in_stable {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E)
    (hU : IsInfUnitary ε E) {S : Submodule ℂ (TensorProduct ℂ M (Fock n))} (hfd : FiniteDimensional ℂ S)
    (hS : IsKStableSub ε (diagE ε (eT E) cpT cmT) S) (hne : S ≠ ⊥) :
    ∃ w ∈ S, w ≠ 0 ∧ ∃ μ : Fin n → ℝ, IsKHWVec ε (diagE ε (eT E) cpT cmT) μ w := by
  refine exists_highestWeight_general ε (fun a b c d hab hcd =>
    diagAction_commutator (eT_isGlRep hE) cpT_cmT_isCAR (eT_commutesCAR E) ε a b c d hab hcd) ?_ hfd hS hne
  intro c w z hw0 hw
  have h := tensorForm_diagAction_adjoint hU (a := c) (b := c) rfl w w
  rw [hw, tensorForm_smul_left, tform_smul_right] at h
  have hne : tform w w ≠ 0 := fun h0 => by
    have := tform_self_re_pos hw0
    rw [h0] at this
    simp at this
  have h2 : star z = z := mul_right_cancel₀ hne h
  exact (Complex.conj_eq_iff_re.mp h2).symm

end Form

end ReciprocityTheory.ChartRestriction.DS.TRGap
