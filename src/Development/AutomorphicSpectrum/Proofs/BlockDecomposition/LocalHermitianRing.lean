module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianRing
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianRing
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.RingHyp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_sigR (h : IsCMExt F E σ) (y : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a e =>
    change a ⊗ₜ[F] σ (σ e) = _
    rw [cm_conj_conj h]

theorem finrank_loc (h : IsCMExt F E σ) : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
  rw [Module.finrank_baseChange, h.2.2.1]

theorem noeth_intLoc : IsNoetherianRing (intLoc F E v) := by
  let _ := (GlobalTheory.Orb.intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) (intLoc F E v) := GlobalTheory.Orb.finite_intLocMap v
  exact IsNoetherianRing.of_finite (v.adicCompletionIntegers F) _

theorem isUnit_intCast {m : ℤ} (hm : m ≠ 0) : IsUnit ((m : ℤ) : Fv F v ⊗[F] E) := by
  have h1 : IsUnit ((m : ℤ) : E) := isUnit_iff_ne_zero.2 (by exact_mod_cast hm)
  simpa using h1.map (inclR (F := F) (Fv F v))

theorem denom_intLoc (a : Fv F v ⊗[F] E) :
    ∃ s ∈ intLoc F E v, IsUnit s ∧ s * a ∈ intLoc F E v := by
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v a
  obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have he' : IsIntegral ℤ (m • x) := he x (Finset.mem_singleton_self x)
  have hmem : ((m : ℤ) : Fv F v ⊗[F] E) ∈ intLoc F E v := intCast_mem _ m
  refine ⟨_, hmem, isUnit_intCast hm, ?_⟩
  have h2 := tmul_mem_intLoc (E := E) (one_mem (v.adicCompletionIntegers F)) ⟨m • x, he'⟩
  have e : ((m : ℤ) : Fv F v ⊗[F] E) * a =
      ((m : ℤ) : Fv F v ⊗[F] E) * (a - (1 : Fv F v) ⊗ₜ[F] x) + (1 : Fv F v) ⊗ₜ[F] (m • x) := by
    have e1 : ((m : ℤ) : Fv F v ⊗[F] E) * (1 : Fv F v) ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] (m • x) := by
      rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
    rw [mul_sub, e1, sub_add_cancel]
  rw [e]
  exact add_mem (mul_mem hmem hx) h2

theorem span_eq_of {R : Type} [CommRing R] {𝔬 : Subring R} {S : Set R} {u : R}
    (hu : u ∈ Submodule.span 𝔬 S) (h : ∀ s ∈ S, ∃ c ∈ 𝔬, s = c * u) :
    Submodule.span 𝔬 S = Submodule.span 𝔬 {u} := by
  refine le_antisymm (Submodule.span_le.2 fun s hs => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hu)
  obtain ⟨c, hc, rfl⟩ := h s hs
  exact Submodule.mem_span_singleton.2 ⟨⟨c, hc⟩, rfl⟩

theorem finEmb_injective (hf : IsField (Fv F v ⊗[F] E)) (τ : E →ₐ[F] FvBar F v) :
    Function.Injective (finEmb F v τ) :=
  (injective_iff_map_eq_zero _).2 fun y hy => by
    by_contra h0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel h0
    have := congrArg (finEmb F v τ) hb
    simp [hy] at this

theorem absBar_finEmb_eq (hf : IsField (Fv F v ⊗[F] E)) (τ τ' : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absBar F v (finEmb F v τ y) = absBar F v (finEmb F v τ' y) := by
  apply NNReal.eq
  change spectralNorm (Fv F v) (FvBar F v) _ = spectralNorm (Fv F v) (FvBar F v) _
  rw [spectralNorm, spectralNorm, minpoly.algHom_eq _ (finEmb_injective hf τ),
    minpoly.algHom_eq _ (finEmb_injective hf τ')]

theorem principal_field (hf : IsField (Fv F v ⊗[F] E)) (I : Submodule (intLoc F E v) (Fv F v ⊗[F] E))
    (hI : I.FG) (hu : ∃ u ∈ I, IsUnit u) : ∃ u : Fv F v ⊗[F] E, IsUnit u ∧ I = Submodule.span (intLoc F E v) {u} := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨w, hw, hwu⟩ := hu
  have : Nontrivial (Fv F v ⊗[F] E) := ⟨hf.exists_pair_ne⟩
  let τ₀ : E →ₐ[F] FvBar F v := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let N : Fv F v ⊗[F] E → NNReal := fun y => absBar F v (finEmb F v τ₀ y)
  have hN0 : ∀ y, N y = 0 → y = 0 := fun y hy =>
    finEmb_injective hf τ₀ (by rw [map_zero]; exact (absBar_eq_zero F v).1 hy)
  have hS : S.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    subst hc
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hw
    exact hwu.ne_zero hw
  obtain ⟨u, huS, hmax⟩ := S.exists_max_image N hS
  have hu0 : u ≠ 0 := by
    rintro rfl
    have h0 : (Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E))) ≤ ⊥ :=
      Submodule.span_le.2 fun s hs => by
        refine hN0 s (le_antisymm ?_ zero_le)
        have := hmax s hs
        rwa [show N 0 = 0 from by simp [N, (absBar_eq_zero F v).2 rfl]] at this
    exact hwu.ne_zero (by simpa using h0 hw)
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel hu0
  have huU : IsUnit u := IsUnit.of_mul_eq_one b hb
  refine ⟨u, huU, span_eq_of (Submodule.subset_span huS) fun s hs => ⟨b * s, ?_, ?_⟩⟩
  · refine mem_intLoc_iff_absFin_le_one.2 ((absFin_le_iff F v).2 fun τ => ?_)
    rw [absBar_finEmb_eq hf τ τ₀, map_mul, absBar_mul]
    have h1 : absBar F v (finEmb F v τ₀ u) * absBar F v (finEmb F v τ₀ b) = 1 := by
      rw [← absBar_mul, ← map_mul, hb, map_one]
      simpa using absBar_algebraMap F v 1
    calc _ ≤ absBar F v (finEmb F v τ₀ b) * absBar F v (finEmb F v τ₀ u) := mul_le_mul' le_rfl (hmax s hs)
      _ = 1 := by rw [mul_comm, h1]
  · rw [mul_right_comm, mul_comm b, hb, one_mul]

theorem exists_dom (ρ : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (S : Finset (Fv F v ⊗[F] E)) {w : Fv F v ⊗[F] E}
    (hw : w ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E))) (hwu : IsUnit w) :
    ∃ j ∈ S, ρ j ≠ 0 ∧ ∀ s ∈ S, ‖ρ s‖₊ ≤ ‖ρ j‖₊ := by
  have hex : ∃ j ∈ S, ρ j ≠ 0 := by
    by_contra hc
    push Not at hc
    have h0 : ∀ y ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E)), ρ y = 0 := fun y hy => by
      induction hy using Submodule.span_induction with
      | mem x hx => exact hc x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
      | smul a x _ hx => rw [Subring.smul_def, smul_eq_mul, map_mul, hx, mul_zero]
    exact (hwu.map ρ).ne_zero (h0 w hw)
  obtain ⟨j0, hj0, hj0'⟩ := hex
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image (fun s => ‖ρ s‖₊) ⟨j0, hj0⟩
  refine ⟨j, hj, fun e => hj0' ?_, hmax⟩
  have := hmax j0 hj0
  rw [e, nnnorm_zero] at this
  exact nnnorm_eq_zero.1 (le_antisymm this zero_le)

theorem principal_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (I : Submodule (intLoc F E v) (Fv F v ⊗[F] E))
    (hI : I.FG) (hu : ∃ u ∈ I, IsUnit u) : ∃ u : Fv F v ⊗[F] E, IsUnit u ∧ I = Submodule.span (intLoc F E v) {u} := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨w, hw, hwu⟩ := hu
  obtain ⟨j1, hj1, h1, hm1⟩ := exists_dom (splitProj τ) S hw hwu
  obtain ⟨j2, hj2, h2, hm2⟩ := exists_dom (splitProj (τ.comp σ)) S hw hwu
  set e := splitIdem h τ with he
  have heI : e ∈ intLoc F E v := splitIdem_mem h τ
  set u : Fv F v ⊗[F] E := e * j1 + (1 - e) * j2 with hu
  have hup : splitProj τ u = splitProj τ j1 := by simp [hu, he]
  have huq : splitProj (τ.comp σ) u = splitProj (τ.comp σ) j2 := by simp [hu, he]
  have hmem : u ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E)) :=
    add_mem (Submodule.smul_mem _ (⟨e, heI⟩ : intLoc F E v) (Submodule.subset_span hj1))
      (Submodule.smul_mem _ (⟨1 - e, sub_mem (one_mem _) heI⟩ : intLoc F E v) (Submodule.subset_span hj2))
  have hunit : IsUnit u := by
    refine IsUnit.of_mul_eq_one ((splitAlgEquiv h τ).symm ((splitProj τ j1)⁻¹, (splitProj (τ.comp σ) j2)⁻¹)) ?_
    refine split_ext h τ ?_ ?_
    · simp [hup, h1]
    · simp [huq, h2]
  refine ⟨u, hunit, span_eq_of hmem fun s hs => ?_⟩
  refine ⟨(splitAlgEquiv h τ).symm (splitProj τ s / splitProj τ j1, splitProj (τ.comp σ) s / splitProj (τ.comp σ) j2),
    (mem_intLoc_iff_split h τ).2 ⟨?_, ?_⟩, split_ext h τ ?_ ?_⟩
  · rw [splitProj_symm, ← nnnorm_le_one_iff_mem, nnnorm_div]
    exact div_le_one_of_le₀ (hm1 s hs) zero_le
  · rw [splitProj_comp_symm, ← nnnorm_le_one_iff_mem, nnnorm_div]
    exact div_le_one_of_le₀ (hm2 s hs) zero_le
  · simp [hup, h1]
  · simp [huq, h2]

theorem isHermRing_intLoc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)),
      IsHermRing (sigR (Fv F v) σ) (intLoc F E v) := by
  intro F E _ _ _ _ _ σ h v
  have h2 : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := finrank_loc h
  have hfin : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.finite_of_finrank_pos (by omega)
  refine
    { invol := sigR_sigR h
      conj_mem := fun a ha => sigR_mem_intLoc σ ha
      nontrivial := Module.nontrivial_of_finrank_pos (R := Fv F v) (by omega)
      artinian := IsArtinianRing.of_finite (Fv F v) _
      noeth := noeth_intLoc
      two := ?_
      denom := denom_intLoc
      principal := fun I hI hu => ?_ }
  · have h1 : IsUnit (2 : E) := isUnit_iff_ne_zero.2 two_ne_zero
    have h3 := h1.map (inclR (F := F) (Fv F v))
    rwa [map_ofNat] at h3
  · by_cases hf : IsField (Fv F v ⊗[F] E)
    · exact principal_field hf I hI hu
    · obtain ⟨φ⟩ := nonempty_algHom_of_not_isField (K := Fv F v) h2 hf
      exact principal_split h ((φ.restrictScalars F).comp Algebra.TensorProduct.includeRight) I hI hu

end GlobalTheory.CompanionTheory.KFin.RingHyp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianRingStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hermitian_ring : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), IsHermRing (sigR (Fv F v) σ) (intLoc F E v) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc | exact GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc | (intros; apply GlobalTheory.CompanionTheory.KFin.RingHyp.isHermRing_intLoc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagCriterion
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagCriterion
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin.Tri

theorem cnt_le {r : ℕ} (S : Finset (Fin r)) (i : Fin r) : cnt S i ≤ S.card := by
  unfold cnt
  exact_mod_cast Finset.card_filter_le _ _

theorem exists_least {r : ℕ} {S : Finset (Fin r)} {i : Fin r} (h : cnt S i < S.card) :
    ∃ j ∈ S, i ≤ j ∧ ∀ j' ∈ S, i ≤ j' → j ≤ j' := by
  have hne : (S.filter (i ≤ ·)).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hn
    have : S.filter (· < i) = S := Finset.filter_true_of_mem fun x hx => not_le.mp (hn hx)
    simp [cnt, this] at h
  refine ⟨(S.filter (i ≤ ·)).min' hne, ?_, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).1
  · exact (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2
  · intro j' hj' hij'
    exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hj', hij'⟩)

theorem exists_between {r : ℕ} {S : Finset (Fin r)} {i k : Fin r} (h : cnt S i < cnt S k) :
    ∃ t ∈ S, i ≤ t ∧ t < k := by
  by_contra hn
  push_neg at hn
  have hsub : S.filter (· < k) ⊆ S.filter (· < i) := by
    intro t ht
    obtain ⟨htS, htk⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨htS, ?_⟩
    by_contra hti
    exact absurd htk (not_lt.mpr (hn t htS (not_lt.mp hti)))
  have := Finset.card_le_card hsub
  unfold cnt at h
  omega

theorem inv_neg_tri {ι : Type} [Fintype ι] [DecidableEq ι] {L : Type} [Field L] (lv : ι → ℤ)
    {M M' : Matrix ι ι L} (h : M * M' = 1)
    (hM : ∀ u v, lv v < lv u → lv v < 0 → M u v = 0) :
    ∀ u v, lv v < lv u → lv v < 0 → M' u v = 0 := by
  intro u v huv hv
  letI : Invertible M := ⟨M', mul_eq_one_comm.mp h, h⟩
  have hinv : M⁻¹ = M' := Matrix.inv_eq_right_inv h
  have hb : M.BlockTriangular (fun w => if lv w ≤ lv v then (0 : ℤ) else 1) := by
    intro a b hab
    by_cases hb' : lv b ≤ lv v
    · by_cases ha' : lv a ≤ lv v
      · simp [hb', ha'] at hab
      · exact hM a b (by omega) (by omega)
    · by_cases ha' : lv a ≤ lv v <;> simp [hb', ha'] at hab
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  rw [hinv] at this
  apply this
  have h1 : ¬ lv u ≤ lv v := by omega
  simp [h1]

theorem col_zero {L : Type} [Field L] {n r m : ℕ} (X Y : Matrix (Fin n) (Fin r) L)
    (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L)
    (hQ : Qi * frm X Z Y = 1) (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L)
    (hst : ∀ j ∈ S, StabUpTo X g j) (u v : Idx r m)
    (huv : lev m S v < lev m S u) (hv : lev m S v < 0) : (Qi * g * frm X Z Y) u v = 0 := by
  rcases v with i | k | i
  · have hi : cnt S i < S.card := by simpa [lev] using hv
    obtain ⟨j, hjS, hij, hmin⟩ := exists_least hi
    obtain ⟨b, hb, hbz⟩ := hst j hjS i hij
    have hc : X *ᵥ b = frm X Z Y *ᵥ (Sum.elim b (fun _ => 0)) := by
      ext a
      simp [frm, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    have hcol : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i)) = Sum.elim b (fun _ => 0) := by
      have e1 : (fun w => (Qi * g * frm X Z Y) w (Sum.inl i))
          = Qi *ᵥ (g *ᵥ (fun a => X a i)) := by
        ext w
        rw [Matrix.mul_assoc]
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, frm]
      rw [e1, hb, hc, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec]
    have hval : (Qi * g * frm X Z Y) u (Sum.inl i) = Sum.elim b (fun _ => 0) u := congrFun hcol u
    rw [hval]
    rcases u with k | w
    · simp only [Sum.elim_inl]
      have hc' : cnt S i < cnt S k := by simpa [lev] using huv
      obtain ⟨t, htS, hit, htk⟩ := exists_between hc'
      exact hbz k (lt_of_le_of_lt (hmin t htS hit) htk)
    · simp
  · simp [lev] at hv
  · have := cnt_le S i
    simp only [lev] at hv
    omega

theorem cT_mul' {L : Type} [Field L] (s : L →+* L) {a b c : Type} [Fintype b]
    (A : Matrix a b L) (B : Matrix b c L) : cT s (A * B) = cT s B * cT s A := by
  simp [cT, Matrix.transpose_mul, Matrix.map_mul]

theorem cT_one' {L : Type} [Field L] (s : L →+* L) {a : Type} [DecidableEq a] :
    cT s (1 : Matrix a a L) = 1 := by
  simp [cT]

theorem block_tri (L : Type) [Field L] (s : L →+* L) (n r m : ℕ)
    (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L)
    (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L)
    (hXX : cT s X * J * X = 0) (hXY : cT s X * J * Y = 1) (hXZ : cT s X * J * Z = 0)
    (hQ : Qi * frm X Z Y = 1) (hQ' : frm X Z Y * Qi = 1) (S : Finset (Fin r))
    (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g) (hJ : cT s g * J * g = J)
    (hst : ∀ j ∈ S, StabUpTo X g j) :
    (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  obtain ⟨gi, h1⟩ := hg.exists_right_inv
  have hrow0 : cT s X * J * frm X Z Y = Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L)
        (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L)) := by
    rw [frm, Matrix.mul_fromCols, Matrix.mul_fromCols, hXX, hXZ, hXY]
  set Q := frm X Z Y with hQdef
  set M := Qi * g * Q with hMdef
  set M' := Qi * gi * Q with hM'def
  have hMM' : M * M' = 1 := by
    calc M * M' = Qi * g * (Q * Qi) * gi * Q := by simp only [hMdef, hM'def, Matrix.mul_assoc]
      _ = Qi * (g * gi) * Q := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.mul_one, hQ]
  have A1 : ∀ u v, lev m S v < lev m S u → lev m S v < 0 → M u v = 0 :=
    fun u v huv hv => col_zero X Y Z Qi hQ S g hst u v huv hv
  have A2 := inv_neg_tri (lev m S) hMM' A1
  set H := cT s Q * J * Q with hHdef
  have hgJ : cT s gi * J = J * g := by
    have e : cT s gi * cT s g = 1 := by
      rw [← cT_mul', h1, cT_one']
    calc cT s gi * J = cT s gi * (cT s g * J * g) := by rw [hJ]
      _ = (cT s gi * cT s g) * J * g := by simp only [Matrix.mul_assoc]
      _ = J * g := by rw [e, Matrix.one_mul]
  have hHM : H * M = cT s M' * H := by
    have e : cT s Qi * cT s Q = 1 := by rw [← cT_mul', hQ', cT_one']
    calc H * M = cT s Q * J * (Q * Qi) * g * Q := by simp only [hHdef, hMdef, Matrix.mul_assoc]
      _ = cT s Q * (J * g) * Q := by rw [hQ']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cT s Q * (cT s gi * J) * Q := by rw [hgJ]
      _ = cT s Q * cT s gi * (cT s Qi * cT s Q) * J * Q := by rw [e]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = cT s M' * H := by simp only [hM'def, hHdef, cT_mul', Matrix.mul_assoc]
  have hrow : ∀ l w, H (Sum.inl l) w = (Matrix.fromCols (0 : Matrix (Fin r) (Fin r) L)
      (Matrix.fromCols (0 : Matrix (Fin r) (Fin m) L) (1 : Matrix (Fin r) (Fin r) L))) l w := by
    intro l w
    rw [← hrow0]
    simp only [hHdef, hQdef, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, frm,
      Matrix.fromCols_apply_inl]
  have lx : ∀ i, lev m S (Sum.inl i) = cnt S i - S.card := fun _ => rfl
  have lz : ∀ k, lev m S (Sum.inr (Sum.inl k)) = 0 := fun _ => rfl
  have ly : ∀ i, lev m S (Sum.inr (Sum.inr i)) = S.card - cnt S i := fun _ => rfl
  intro u v huv
  by_cases hv : lev m S v < 0
  · exact A1 u v huv hv
  push_neg at hv
  rcases u with i | k | l
  · have := cnt_le S i
    rw [lx] at huv
    omega
  · rw [lz] at huv
    omega
  have hl0 : lev m S (Sum.inl l) < 0 := by
    have := cnt_le S l
    rw [ly] at huv; rw [lx]; omega
  have hlv : lev m S v < - lev m S (Sum.inl l) := by rw [ly] at huv; rw [lx]; omega
  have e1 : M (Sum.inr (Sum.inr l)) v = (H * M) (Sum.inl l) v := by
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hrow, Matrix.one_apply]
  rw [e1, hHM, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases hw : lev m S (Sum.inl l) < lev m S w
  · have : M' w (Sum.inl l) = 0 := A2 w _ hw hl0
    simp [cT, this]
  push_neg at hw
  rcases w with l' | k | l'
  · rcases v with a | b | c
    · simp [hrow]
    · simp [hrow]
    · by_cases hc : l' = c
      · subst hc
        have := cnt_le S l'
        simp only [lx, ly] at hw hlv
        omega
      · simp [hrow, Matrix.one_apply, hc]
  · rw [lz] at hw
    omega
  · have := cnt_le S l'
    rw [ly] at hw
    omega

theorem witt_blockTriangular : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (∀ j ∈ S, StabUpTo X g j) → (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  intro L _ s _ n r m J X Y Z Qi _ hXX _ hXY hXZ _ hQ hQ' S g hg hJ hst
  exact block_tri L s n r m J X Y Z Qi hXX hXY hXZ hQ hQ' S g hg hJ hst

end GlobalTheory.CompanionTheory.CFin.Tri
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameStabilizerFlagCriterionStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_stabilizer_flag_criterion : ∀ (L : Type) [Field L] (s : L →+* L), (∀ x, s (s x) = x) → ∀ (n r m : ℕ) (J : Matrix (Fin n) (Fin n) L) (X Y : Matrix (Fin n) (Fin r) L) (Z : Matrix (Fin n) (Fin m) L) (Qi : Matrix (Idx r m) (Fin n) L), cT s J = J → cT s X * J * X = 0 → cT s Y * J * Y = 0 → cT s X * J * Y = 1 → cT s X * J * Z = 0 → cT s Y * J * Z = 0 → Qi * frm X Z Y = 1 → frm X Z Y * Qi = 1 → ∀ (S : Finset (Fin r)) (g : Matrix (Fin n) (Fin n) L), IsUnit g → cT s g * J * g = J → (∀ j ∈ S, StabUpTo X g j) → (Qi * g * frm X Z Y).BlockTriangular (lev m S) := by
  first | exact @GlobalTheory.CompanionTheory.CFin.Tri.witt_blockTriangular | exact GlobalTheory.CompanionTheory.CFin.Tri.witt_blockTriangular | (intros; apply GlobalTheory.CompanionTheory.CFin.Tri.witt_blockTriangular <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolic
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolic
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Closed

open GlobalTheory.CompanionTheory.BZPhiPhi

section LinAlg

variable {k : Type} [Field k]

theorem exists_GL_row (N m : ℕ) (r : Fin (N + 1) → k) (hr0 : ∀ l : Fin (N + 1), l.val < m → r l = 0)
    (hr : r ≠ 0) :
    ∃ A : GL (Fin (N + 1)) k, (A : Matrix (Fin (N + 1)) (Fin (N + 1)) k) (Fin.last N) = r ∧
      ∀ i l : Fin (N + 1), m ≤ i.val → l.val < m → (A : Matrix (Fin (N + 1)) (Fin (N + 1)) k) i l = 0 := by
  classical
  obtain ⟨l0, hl0⟩ : ∃ l, r l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  have hml : m ≤ l0.val := by
    by_contra h
    exact hl0 (hr0 l0 (by omega))
  let B : Matrix (Fin (N + 1)) (Fin (N + 1)) k := (1 : Matrix _ _ k).updateRow l0 r
  have hB : B.det = r l0 := by
    have h1 := Matrix.cramer_apply (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k) r l0
    rw [Matrix.cramer_one] at h1
    have h2 := Matrix.updateRow_transpose (M := (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k)) (j := l0) (c := r)
    rw [Matrix.transpose_one] at h2
    show ((1 : Matrix (Fin (N + 1)) (Fin (N + 1)) k).updateRow l0 r).det = r l0
    rw [h2, Matrix.det_transpose, ← h1]
    rfl
  let σ : Equiv.Perm (Fin (N + 1)) := Equiv.swap l0 (Fin.last N)
  let A : Matrix (Fin (N + 1)) (Fin (N + 1)) k := B.submatrix σ id
  have hA : A.det ≠ 0 := by
    have : A.det = _ := Matrix.det_permute σ B
    rw [this, hB]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, hl0]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hA, ?_, ?_⟩
  · funext l
    show B (σ (Fin.last N)) l = r l
    simp [σ, B]
  · intro i l hi hl
    show B (σ i) l = 0
    have hs : m ≤ (σ i).val := by
      simp only [σ, Equiv.swap_apply_def]
      split_ifs
      · have := Fin.is_lt l
        have h3 : l0.val ≤ N := by omega
        simp only [Fin.val_last]
        omega
      · exact hml
      · exact hi
    simp only [B, Matrix.updateRow_apply]
    split_ifs
    · exact hr0 l hl
    · rw [Matrix.one_apply_ne]
      intro e
      rw [e] at hs
      omega

theorem levi_val (n : ℕ) (A : GL (Fin n) k) :
    (((levi k n A : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (A : Matrix (Fin n) (Fin n) k) := rfl

theorem mirProj_val (n : ℕ) (g : Mir k n) (i l : Fin n) :
    ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i l =
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc l) := rfl

theorem glEmbMat_last_cast (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (l : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc l) = 0 := by
  simp [glEmbMat]

theorem mirProj_levi_eq (n : ℕ) (A : GL (Fin n) k) : mirabolicProjection k n (levi k n A) = A := by
  ext i l
  rw [mirProj_val, levi_val]
  simp [glEmbMat]

theorem rowQ_ne_zero (n : ℕ) (p : Mir k (n + 1)) : rowQ k n p ≠ 0 := by
  intro h
  have key : vecMul (eLast k n) ((mirabolicProjection k (n + 1) p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      rowQ k n p := by
    rw [vecMul_eLast]
    rfl
  have h2 : eLast k n = 0 := by
    have h3 := congrArg (fun v => vecMul v ((((mirabolicProjection k (n + 1) p)⁻¹ : GL (Fin (n + 1)) k)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k)) key
    simp only [h, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, vecMul_one, zero_vecMul] at h3
    exact h3
  have h4 := congrFun h2 (Fin.last n)
  simp [eLast] at h4

theorem entry_of_mirProj_eq_one (n : ℕ) (u : Mir k n) (hu : mirabolicProjection k n u = 1) (i l : Fin (n + 1))
    (hil : i ≠ l) (hl : l ≠ Fin.last n) :
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i l = 0 := by
  obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.2 hl
  induction i using Fin.lastCases with
  | last =>
    rw [(mem_Mir_iff k _).1 u.2]
    simp [eLast, Pi.single_apply, Fin.castSucc_ne_last]
  | cast i =>
    rw [← mirProj_val, hu]
    have : i ≠ l' := fun e => hil (by rw [e])
    simp [Matrix.one_apply, this]

theorem row_levi (n : ℕ) (y : Mir k n) (t : Fin (n + 2)) :
    (((levi k (n + 1) (y : GL (Fin (n + 1)) k) : Mir k (n + 1)) : GL (Fin (n + 2)) k) :
        Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) t =
      (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) k) (Fin.castSucc (Fin.last n)) t := by
  rw [levi_val]
  have hy := (mem_Mir_iff k _).1 y.2
  induction t using Fin.lastCases with
  | last => simp [glEmbMat, Matrix.one_apply, Fin.castSucc_ne_last]
  | cast t =>
    simp only [glEmbMat, Fin.lastCases_castSucc]
    rw [hy]
    by_cases h : t = Fin.last n
    · subst h; simp [eLast]
    · have : (Fin.last n) ≠ t := fun e => h e.symm
      simp [eLast, Pi.single_apply, h, Matrix.one_apply, this]

end LinAlg

section Conc

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_mirabolicParabolic_iff_lt (m j : ℕ) (g : Mir k (m + (j + 1))) :
    g ∈ MirabolicParabolic k m (j + 1) ↔ ∀ i l : Fin (m + (j + 1) + 1), m ≤ i.val → l.val < m →
      ((g : GL (Fin (m + (j + 1) + 1)) k) : Matrix (Fin (m + (j + 1) + 1)) (Fin (m + (j + 1) + 1)) k) i l = 0 := by
  rw [mem_mirabolicParabolic_iff]
  constructor
  · intro h i l hi hl
    have hb : i.val - m < j + 1 + 1 := by have := i.2; omega
    have h1 := h ⟨i.val - m, hb⟩ ⟨l.val, hl⟩
    have e1 : eGP m (j + 1) ⟨true, ⟨i.val - m, hb⟩⟩ = i := Fin.ext (by rw [blockIndex_true_val]; simp; omega)
    have e2 : eGP m (j + 1) ⟨false, ⟨l.val, hl⟩⟩ = l := Fin.ext (by rw [blockIndex_false_val])
    rwa [e1, e2] at h1
  · intro h b a
    apply h
    · rw [blockIndex_true_val]; omega
    · rw [blockIndex_false_val]; exact a.2

theorem set_eq (m j : ℕ) :
    {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} =
      {g | ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0} := by
  ext g
  constructor
  · rintro ⟨h, hh, x, rfl⟩ l hl
    have e : (h * embedding₂ k (m + j) x)⁻¹ = embedding₂ k (m + j) x⁻¹ * h⁻¹ := by
      rw [_root_.mul_inv_rev, map_inv]
    rw [e]
    have hi := (mem_mirabolicParabolic_iff_lt k m j h⁻¹).1 (inv_mem hh)
    show ((embedding₂ k (m + j) x⁻¹).1.1 * (h⁻¹ : Mir k (m + j + 1)).1.1)
        (Fin.castSucc (Fin.last (m + j))) (Fin.castSucc l) = 0
    rw [Matrix.mul_apply]
    simp only [embedding₂, MonoidHom.comp_apply, Subgroup.coe_subtype]
    simp only [row_levi, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hi _ _ (by simp) (by simpa using hl)
  · intro hg
    obtain ⟨A, hA1, hA2⟩ := exists_GL_row (m + j) m (rowQ k (m + j) g⁻¹) hg (rowQ_ne_zero _ _)
    let d : Mir k (m + (j + 1)) := levi k (m + j + 1) A
    have hd : d ∈ MirabolicParabolic k m (j + 1) := by
      rw [mem_mirabolicParabolic_iff_lt]
      intro i l hi hl
      have hl' : l ≠ Fin.last (m + j + 1) := by
        intro e; rw [e] at hl; simp at hl; omega
      obtain ⟨l', rfl⟩ := Fin.exists_castSucc_eq.2 hl'
      show (levi k (m + j + 1) A).1.1 i _ = 0
      rw [levi_val]
      induction i using Fin.lastCases with
      | last => exact glEmbMat_last_cast _ _ _
      | cast i =>
        simp only [glEmbMat, Fin.lastCases_castSucc]
        exact hA2 i l' (by simpa using hi) (by simpa using hl)
    have rd : rowQ k (m + j) d = rowQ k (m + j) g⁻¹ := by
      funext l
      have : rowQ k (m + j) d l = (A : Matrix _ _ k) (Fin.last (m + j)) l := by
        show (levi k (m + j + 1) A).1.1 _ _ = _
        rw [levi_val]
        simp [glEmbMat]
      rw [this, hA1]
    have hq : g⁻¹ * d⁻¹ ∈ Q k (m + j) := mul_inv_mem_Q_of_rowQ_eq _ _ _ rd.symm
    have hq' : (g⁻¹ * d⁻¹)⁻¹ ∈ Q k (m + j) := inv_mem hq
    let y : Mir k (m + j) := ⟨mirabolicProjection k (m + j + 1) (g⁻¹ * d⁻¹)⁻¹, hq'⟩
    let u : Mir k (m + j + 1) := (g⁻¹ * d⁻¹)⁻¹ * (embedding₂ k (m + j) y)⁻¹
    have hu : mirabolicProjection k (m + j + 1) u = 1 := by
      simp only [u, map_mul, map_inv (mirabolicProjection k (m + j + 1)) (embedding₂ k (m + j) y)]
      have : mirabolicProjection k (m + j + 1) (embedding₂ k (m + j) y) = mirabolicProjection k (m + j + 1) (g⁻¹ * d⁻¹)⁻¹ :=
        mirProj_levi_eq _ _
      rw [this]
      simp
    have huH : u ∈ MirabolicParabolic k m (j + 1) := by
      rw [mem_mirabolicParabolic_iff_lt]
      intro i l hi hl
      refine entry_of_mirProj_eq_one _ u hu i l ?_ ?_
      · intro e; rw [e] at hi; omega
      · intro e; rw [e] at hl; simp at hl; omega
    refine ⟨d⁻¹ * u, mul_mem (inv_mem hd) huH, y, ?_⟩
    simp only [u]
    group

theorem isClosed_HGP_iota (m j : ℕ) :
    IsClosed {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  rw [set_eq]
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun l => isClosed_iInter fun _ =>
    isClosed_eq (((continuous_apply l).comp (continuous_rowQ (m + j))).comp continuous_inv) continuous_const

end Conc

end GlobalTheory.CompanionTheory.LeibPhi.Closed

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedParabolicMulEmbeddedMirabolicStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_parabolic_mul_embedded_mirabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ),
    IsClosed {g : Mir k (m + (j + 1)) | ∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x} := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota | exact GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Closed.isClosed_HGP_iota <;> assumption)
end
end
