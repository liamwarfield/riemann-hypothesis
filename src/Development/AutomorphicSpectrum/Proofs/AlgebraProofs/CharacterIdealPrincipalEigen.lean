module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBcPull
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

private theorem sum_smul_cols_eq_mul_vec {C R X : Type} [Field C] [CommRing R] [Algebra R C]
    [Fintype X] (B : Matrix X X C) (c : X → R) :
    (∑ j, c j • fun x => B x j) = B *ᵥ fun j => algebraMap R C (c j) := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp only [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]

theorem mem_span_cols_iff {C R X : Type} [Field C] [CommRing R] [Algebra R C] [Fintype X]
    [DecidableEq X] (B : Matrix X X C) (hB : IsUnit B.det) (u : X → C) :
    u ∈ Submodule.span R (Set.range fun j x => B x j) ↔
      ∀ j, ∃ r : R, algebraMap R C r = (B⁻¹ *ᵥ u) j := by
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hinv' : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ j
    refine ⟨c j, ?_⟩
    rw [sum_smul_cols_eq_mul_vec, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  · intro h
    choose c hc using h
    refine ⟨c, ?_⟩
    have e : (fun j => algebraMap R C (c j)) = B⁻¹ *ᵥ u := funext hc
    rw [sum_smul_cols_eq_mul_vec, e, Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]

theorem exists_denominator {C R X : Type} [Field C] [CommRing R] [Algebra R C]
    (v : Valuation C NNReal) (hv : v.Integers R) [Fintype X] [Nonempty X] (w : X → C) :
    ∃ c : R, c ≠ 0 ∧ ∀ d : R,
      (∀ j, ∃ r : R, algebraMap R C r = algebraMap R C d * w j) ↔ d ∈ Ideal.span {c} := by
  classical
  by_cases hall : ∀ j, v (w j) ≤ 1
  · have h10 : (1 : R) ≠ 0 := by
      intro h
      have h' := congrArg (algebraMap R C) h
      simp at h'
    refine ⟨1, h10, fun d => ?_⟩
    constructor
    · intro _
      simp [Ideal.span_singleton_one]
    · intro _ j
      apply hv.exists_of_le_one
      rw [map_mul]
      calc v (algebraMap R C d) * v (w j) ≤ 1 * 1 := mul_le_mul' (hv.map_le_one d) (hall j)
        _ = 1 := one_mul 1
  · push Not at hall
    obtain ⟨j1, hj1⟩ := hall
    obtain ⟨j0, -, hj0⟩ :=
      Finset.exists_max_image Finset.univ (fun j => v (w j)) Finset.univ_nonempty
    have hgt : 1 < v (w j0) := lt_of_lt_of_le hj1 (hj0 j1 (Finset.mem_univ _))
    have hw0 : w j0 ≠ 0 := by
      intro h
      simp [h] at hgt
    have hinvle : v (w j0)⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ hgt.le
    obtain ⟨c, hc⟩ := hv.exists_of_le_one hinvle
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact inv_ne_zero hw0 hc.symm
    refine ⟨c, hc0, fun d => ?_⟩
    rw [Ideal.mem_span_singleton, hv.dvd_iff_le, hc]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := h j0
      have e : algebraMap R C d = (algebraMap R C d * w j0) * (w j0)⁻¹ :=
        (mul_inv_cancel_right₀ hw0 _).symm
      rw [e, map_mul, ← hr]
      exact mul_le_of_le_one_left zero_le (hv.map_le_one r)
    · intro h j
      apply hv.exists_of_le_one
      rw [map_mul]
      calc v (algebraMap R C d) * v (w j) ≤ v (w j0)⁻¹ * v (w j0) :=
            mul_le_mul' h (hj0 j (Finset.mem_univ _))
        _ = 1 := by rw [← map_mul, inv_mul_cancel₀ hw0, map_one]

private theorem smul_algebra_map_char_eq {C R F : Type} [Field C] [CommRing R] [Algebra R C] [Field F]
    (χ : MulChar F R) (c : R) :
    (c • fun a => algebraMap R C (χ a)) = fun a => algebraMap R C (c * χ a) := by
  funext a
  simp only [Pi.smul_apply, Algebra.smul_def, map_mul]

theorem eig_rank_one : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ χ : MulChar F R, (∃ c : R, c ≠ 0 ∧ xIdeal AA.carrier χ = Ideal.span {c}) ∧ ∀ g, g ∈ eig AA.carrier χ ↔ ∃ c ∈ xIdeal AA.carrier χ, g = fun a => algebraMap R C (c * χ a) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ AA _ χ
  obtain ⟨B, hB, hM⟩ := AA.lat
  have key : ∀ d : R, d ∈ xIdeal AA.carrier χ ↔
      (d • fun a => algebraMap R C (χ a)) ∈ AA.carrier := fun d => by
    simp only [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc0, hc⟩ := exists_denominator v hv (B⁻¹ *ᵥ fun a => algebraMap R C (χ a))
    refine ⟨c, hc0, ?_⟩
    ext d
    rw [key, hM, mem_span_cols_iff B hB, ← hc d]
    refine forall_congr' fun j => exists_congr fun r => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  · intro g
    constructor
    · rintro ⟨hgM, hg⟩
      have hint : ∀ x, ∃ r : R, algebraMap R C r = g x := AA.le_int hgM
      obtain ⟨r, hr⟩ := hint 1
      have hgf : g = fun a => algebraMap R C (r * χ a) := by
        funext a
        have h := hg a 1
        rw [smul_eq_mul, mul_one] at h
        rw [h, ← hr, map_mul]
        exact mul_comm _ _
      refine ⟨r, ?_, hgf⟩
      rw [key, smul_algebra_map_char_eq, ← hgf]
      exact hgM
    · rintro ⟨c, hc, rfl⟩
      rw [key, smul_algebra_map_char_eq] at hc
      refine ⟨hc, fun a x => ?_⟩
      simp only [smul_eq_mul, map_mul]
      ring

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigenStatement
alias GlobalTheory.T.character_ideal_principal_eigen := GlobalTheory.CompanionTheory.Ar.GR.eig_rank_one
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtension
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem ext_tensor_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) :=
  PositivityTheory.HtPt.Mh.ext_tensor

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtensionStatement
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_scalar_extension : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change | exact GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundle
open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem deg_shortExact : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → IsBun C L ∧ IsBun C L'' ∧ deg C L' = deg C L + deg C L'' := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g hL' hSE
  obtain ⟨hf, hfg, hg, hL, hL''⟩ := hSE
  have hsub := GlobalTheory.T.sub_and_quotient_bundles K C V' L' (LinearMap.range f) hL'
  obtain ⟨e1, he1⟩ : ∃ e : V ≃ₗ[K] LinearMap.range f, ∀ x, (e x : V') = f x :=
    ⟨LinearEquiv.ofInjective f hf, fun x => by simp⟩
  have hker : LinearMap.range f = LinearMap.ker g := (LinearMap.exact_iff.mp hfg).symm
  obtain ⟨e2, he2⟩ : ∃ e : (V' ⧸ LinearMap.range f) ≃ₗ[K] V'',
      ∀ y, e (Submodule.Quotient.mk y) = g y :=
    ⟨(Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective g hg),
      fun y => by simp [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]⟩
  have hc1 : ∀ (i : C.I) (x : LinearMap.range f),
      x ∈ GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f) i ↔ e1.symm x ∈ L i := by
    intro i x
    simp only [GlobalTheory.CompanionTheory.Ar.Crv.sub, AddSubgroup.mem_comap]
    rw [hL i, ← he1, LinearEquiv.apply_symm_apply]
    exact Iff.rfl
  have hc2 : ∀ (i : C.I) (z : V' ⧸ LinearMap.range f),
      z ∈ GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f) i ↔ e2 z ∈ L'' i := by
    intro i z
    simp only [GlobalTheory.CompanionTheory.Ar.Crv.quot]
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h2 : e2 (Submodule.Quotient.mk y) ∈ L'' i := by
        rw [he2]
        exact (hL'' i (g y)).2 ⟨y, hy, rfl⟩
      exact h2
    · intro hz
      obtain ⟨y, hy, hyz⟩ := (hL'' i _).1 hz
      refine ⟨y, hy, e2.injective ?_⟩
      have h3 : e2 (Submodule.Quotient.mk y) = e2 z := by rw [he2, hyz]
      exact h3
  obtain ⟨hLb, hdL⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C (LinearMap.range f) V
    (GlobalTheory.CompanionTheory.Ar.Crv.sub C L' (LinearMap.range f)) L e1.symm hsub.1 hc1
  obtain ⟨hL''b, hdL''⟩ := GlobalTheory.T.degree_invariant_linear_equiv K C (V' ⧸ LinearMap.range f) V''
    (GlobalTheory.CompanionTheory.Ar.Crv.quot C L' (LinearMap.range f)) L'' e2 hsub.2 hc2
  refine ⟨hLb, hL''b, ?_⟩
  rw [GlobalTheory.T.degree_additive_sub_quotient K C V' L' (LinearMap.range f) hL']
  unfold GlobalTheory.CompanionTheory.Ar.Crv.subDeg
  rw [hdL, hdL'']

end GlobalTheory.CompanionTheory.Ar.Crv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ShortExactFirstTermBundleStatement
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_first_term_bundle : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V''), IsBun C L' → ShortExact C L L' L'' f g → IsBun C L ∧ IsBun C L'' ∧ deg C L' = deg C L + deg C L'' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact | exact GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwoMulFinrank
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

namespace PtBasic

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem ht_surjective : Function.Surjective P.ht := by
  have : P.om.IsFullLattice C := P.om_lat
  have hspan : Submodule.span C (P.om : Set Ω) = ⊤ := Submodule.IsFullLattice.span_eq_top
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
  intro y hy
  obtain ⟨x, -, hx⟩ := P.κ_mem y hy
  show y ∈ LinearMap.range P.ht
  rw [LinearMap.mem_range]
  refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
  rw [map_smul, hx, ← algebraMap_smul C κ y, smul_smul, inv_mul_cancel₀ P.κ_ne, one_smul]

theorem T_lattice : P.T.IsLattice C := by
  obtain ⟨hli, -, hT⟩ := P.free
  have hfg : P.T.FG := by
    rw [hT]
    exact Submodule.fg_span (Set.finite_range _)
  refine ⟨hfg, ?_⟩
  intro s hs hliO
  rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact linearIndepOn_empty C id
  have hinj : Function.Injective (algebraMap O C) := by
    intro a b hab
    apply hliO.linearIndependent.smul_left_injective ⟨x, hx⟩
    change a • x = b • x
    rw [← algebraMap_smul C a x, ← algebraMap_smul C b x, hab]
  have : FaithfulSMul O C := (faithfulSMul_iff_algebraMap_injective O C).mpr hinj
  have : Nontrivial O := (algebraMap O C).domain_nontrivial
  refine Submodule.linearIndepOn_of_finrank_le_finrank_span P.T hfg ?_ hs hliO
  rw [hT, Submodule.span_span_of_tower O, finrank_span_eq_card hli,
    finrank_span_eq_card (hli.restrict_scalars' O)]

theorem rho_t_mem (a : 𝓞 E) (i : Fin N) : P.ρ a (P.t i) ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hmem : ∀ k, P.ρ (RingOfIntegers.basis E k) (P.t i) ∈ P.T := fun k => by
    rw [hT]
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  rw [← (RingOfIntegers.basis E).sum_repr a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun k _ => zsmul_mem (hmem k) _

theorem T_stable (a : 𝓞 E) : ∀ x ∈ P.T, P.ρ a x ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hle : P.T ≤ P.T.comap ((P.ρ a).restrictScalars O) := by
    nth_rewrite 1 [hT]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) ∈ P.T
    rw [show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) =
        (P.ρ a * P.ρ (RingOfIntegers.basis E q.2)) (P.t q.1) from rfl, ← map_mul]
    exact rho_t_mem P _ _
  exact fun x hx => hle hx

theorem ht_eigProj (σ : E →+* C) (x : V) :
    P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, P.ht_lin]

theorem om'_lattice : P.om'.IsLattice C := by
  have : P.om.IsFullLattice C := P.om_lat
  apply Submodule.IsLattice.mono_of_fg C (show P.om' ≤ P.om from ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact P.ht_mem x hx
  · rw [HTPoint.om']
    exact (T_lattice P).fg.map _

theorem omHT_eq (σ : E →+* C) :
    P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O) := by
  have hcomm : ((eigProj P.ρΩ σ).restrictScalars O) ∘ₗ (P.ht.restrictScalars O) =
      (P.ht.restrictScalars O) ∘ₗ ((eigProj P.ρ σ).restrictScalars O) :=
    LinearMap.ext fun x => (ht_eigProj P σ x).symm
  show (P.T.map (P.ht.restrictScalars O)).map ((eigProj P.ρΩ σ).restrictScalars O) =
    (P.T.map ((eigProj P.ρ σ).restrictScalars O)).map (P.ht.restrictScalars O)
  rw [← Submodule.map_comp, ← Submodule.map_comp, hcomm]

theorem e_skew (x y : V) : P.e x y = - P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add (f := _), LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem dualLat_flip : dualLat P.e.flip P.T = P.T := by
  conv_rhs => rw [← P.perfect]
  ext y
  simp only [LatBasic.mem_dualLat, LinearMap.flip_apply]
  refine forall₂_congr fun x _ => ?_
  rw [e_skew P y x, neg_mem_iff]
include P in
theorem finite_V : Module.Finite C V := by
  obtain ⟨s, hs⟩ := (T_lattice P).fg
  refine ⟨⟨s, ?_⟩⟩
  rw [← Submodule.span_span_of_tower O, hs, P.free.2.1]
include P in
theorem two_mul_finrank : 2 * finrank C Ω = finrank C V := by
  haveI := finite_V P
  have hrefl : LinearMap.BilinForm.IsRefl P.e := fun x y h => by rw [e_skew P y x, h, neg_zero]
  have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
    ext x
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.mem_ker]
    rw [P.lagr x]
    refine forall₂_congr fun y _ => ?_
    rw [e_skew P y x, neg_eq_zero]
  have htop : LinearMap.BilinForm.orthogonal P.e ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    exact (Submodule.mem_bot C).mpr (P.nondeg x fun y => hx y Submodule.mem_top)
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl (LinearMap.ker P.ht)
  rw [horth, htop, inf_bot_eq, finrank_bot, add_zero] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker P.ht
  rw [LinearMap.range_eq_top.mpr (ht_surjective P), finrank_top] at h2
  omega

end PtBasic

theorem htPoint_basic : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω), Function.Surjective P.ht ∧ P.T.IsLattice C ∧ (∀ (a : 𝓞 E), ∀ x ∈ P.T, P.ρ a x ∈ P.T) ∧ (∀ (σ : E →+* C) x, P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x)) ∧ P.om'.IsLattice C ∧ (∀ σ : E →+* C, P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O)) ∧ dualLat P.e.flip P.T = P.T ∧ 2 * Module.finrank C Ω = Module.finrank C V := by
  intro C _ v O _ _ _ _ _ E _ _ c _ κ N V _ _ _ _ Ω _ _ _ _ P
  exact ⟨PtBasic.ht_surjective P, PtBasic.T_lattice P, PtBasic.T_stable P, PtBasic.ht_eigProj P,
    PtBasic.om'_lattice P, PtBasic.omHT_eq P, PtBasic.dualLat_flip P, PtBasic.two_mul_finrank P⟩

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigSubEqDifferentSmulEigQuot
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem apply_of_mem_eigSp (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {x : V}
    (hx : x ∈ eigSp ρ σ) (a : 𝓞 E) : ρ a x = σ (a : E) • x := by
  have := (Submodule.mem_iInf _).1 hx a
  simpa [sub_eq_zero] using this

theorem sum_smul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) {N : ℕ} (t : Fin N → V)
    (y : Fin N → K) :
    ∑ i, y i • eigProj ρ σ (t i) =
      ∑ q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E),
        (y q.1 * σ (dualInt E q.2)) • ρ (RingOfIntegers.basis E q.2) (t q.1) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [eigProj, LinearMap.sum_apply, Finset.smul_sum, mul_smul]

omit [Algebra A K] [IsScalarTower A K V] in
theorem mem_of_isFreeOn (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) {N : ℕ} (t : Fin N → V)
    (h : IsFreeOn ρ X t) (i : Fin N) : t i ∈ X := by
  have h1 : t i = ∑ k, (RingOfIntegers.basis E).repr 1 k • ρ (RingOfIntegers.basis E k) (t i) := by
    have := congrArg (fun a => ρ a (t i)) ((RingOfIntegers.basis E).sum_repr 1)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, map_one, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.one_apply] at this
    exact this.symm
  rw [h1, h.2.2]
  refine Submodule.sum_mem _ fun k _ => ?_
  refine zsmul_mem ?_ _
  exact Submodule.subset_span ⟨(i, k), rfl⟩

theorem eigSub_eq_different_smul_eigQuot : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (X : Submodule A V) (N : ℕ) (t : Fin N → V) (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → IsFreeOn ρ X t → (∀ x, x ∈ eigQuot ρ σ X ↔ d • x ∈ eigSub ρ σ X) ∧ eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) ∧ LinearIndependent K (fun i => eigProj ρ σ (t i)) ∧ Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
  intro A K _ _ _ _ V _ _ _ _ E _ _ ρ X N t σ d hinj hσ hd hX
  obtain ⟨he1, he2, -, he4⟩ := ProjEig.eigProj_spec K V E ρ σ
  obtain ⟨hd0, hd1, u, hu⟩ := GlobalTheory.T.different_generator_dual_integral A K E σ d hinj hσ hd
  have hQ : eigQuot ρ σ X = Submodule.span A (Set.range fun i => eigProj ρ σ (t i)) := by
    apply le_antisymm
    · unfold eigQuot
      rw [hX.2.2, Submodule.map_span_le]
      rintro _ ⟨⟨i, k⟩, rfl⟩
      obtain ⟨a, ha⟩ := hσ (RingOfIntegers.basis E k)
      have : eigProj ρ σ (ρ (RingOfIntegers.basis E k) (t i)) = a • eigProj ρ σ (t i) := by
        rw [← Module.End.mul_apply, he4, Module.End.mul_apply,
          apply_of_mem_eigSp ρ σ (he1 _), ← ha, IsScalarTower.algebraMap_smul]
      simp only [LinearMap.restrictScalars_apply]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨t i, mem_of_isFreeOn ρ X t hX i, rfl⟩
  have hli : LinearIndependent K (fun i => eigProj ρ σ (t i)) := by
    rw [Fintype.linearIndependent_iff]
    intro y hy i
    rw [sum_smul_eigProj] at hy
    have h0 := Fintype.linearIndependent_iff.1 hX.1 _ hy
    calc y i = y i * ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) := by
          rw [hu, mul_one]
      _ = ∑ k, algebraMap A K (u k) * algebraMap A K d * (y i * σ (dualInt E k)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := Finset.sum_eq_zero fun k _ => by
          have := h0 (i, k)
          simp only at this
          rw [this, mul_zero]
  have hsp : Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) = eigSp ρ σ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact he1 _
    · intro x hx
      rw [← he2 x hx]
      have hx' : x ∈ Submodule.span K (X : Set V) := by rw [hX.2.1]; trivial
      have : (Submodule.span K (X : Set V)).map (eigProj ρ σ) ≤
          Submodule.span K (Set.range fun i => eigProj ρ σ (t i)) := by
        rw [Submodule.map_span_le]
        intro m hm
        apply Submodule.span_le_restrictScalars A K
        rw [← hQ]
        exact ⟨m, hm, rfl⟩
      exact this ⟨x, hx', rfl⟩
  refine ⟨fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hQ, hli, hsp⟩
  · refine ⟨?_, ?_⟩
    · rw [hQ, Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨c, rfl⟩ := hx
      have : d • ∑ i, c i • eigProj ρ σ (t i) =
          ∑ i, (algebraMap A K (c i) * algebraMap A K d) • eigProj ρ σ (t i) := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← map_mul, IsScalarTower.algebraMap_smul, mul_comm, mul_smul]
      rw [this, sum_smul_eigProj, hX.2.2]
      refine Submodule.sum_mem _ fun q _ => ?_
      obtain ⟨a, ha⟩ := hd1 q.2
      rw [mul_assoc, ← ha, ← map_mul, IsScalarTower.algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    · obtain ⟨m, -, rfl⟩ := hx
      exact Submodule.smul_mem _ d (show _ ∈ (eigSp ρ σ).restrictScalars A from he1 m)
  · obtain ⟨hx1, hx2⟩ := hx
    have hxe : x ∈ eigSp ρ σ := by
      have h2 : algebraMap A K d • x ∈ eigSp ρ σ := by
        rw [IsScalarTower.algebraMap_smul]; exact hx2
      exact (Submodule.smul_mem_iff _ hd0).1 h2
    rw [← hsp, Submodule.mem_span_range_iff_exists_fun] at hxe
    obtain ⟨y, rfl⟩ := hxe
    have hx1' : d • ∑ i, y i • eigProj ρ σ (t i) ∈ X := hx1
    rw [hX.2.2, Submodule.mem_span_range_iff_exists_fun] at hx1'
    obtain ⟨c, hc⟩ := hx1'
    have h3 : d • ∑ i, y i • eigProj ρ σ (t i) =
        ∑ i, (y i * algebraMap A K d) • eigProj ρ σ (t i) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm, mul_smul, IsScalarTower.algebraMap_smul]
    rw [h3, sum_smul_eigProj] at hc
    have h4 : ∀ q, algebraMap A K (c q) = y q.1 * algebraMap A K d * σ (dualInt E q.2) := by
      refine Fintype.linearIndependent_iffₛ.1 hX.1 _ _ ?_
      rw [← hc]
      exact Finset.sum_congr rfl fun q _ => IsScalarTower.algebraMap_smul _ _ _
    rw [hQ]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h5 : y i = algebraMap A K (∑ k, u k * c (i, k)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← mul_one (y i), ← hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, h4]
      ring
    rw [h5, IsScalarTower.algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.HT.SubDiffQuot
end
end
