module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableInfRestrictScalarsOfLeSpan
open IsDiscreteValuationRing Pointwise

namespace GlobalTheory

section TorsionFree

variable {R V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [AddCommGroup V]
  [Module R V] [Module.IsTorsionFree R V]

end TorsionFree

section Span

variable {R : Type*} (K : Type*) {V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem exists_ne_zero_smul_mem_of_mem_span_fractionField {M : Submodule R V} {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem exists_ne_zero_smul_le_of_le_span_fractionField {M N : Submodule R V} (hN : N.FG)
    (h : (N : Set V) ⊆ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • N ≤ M := by
  classical
  obtain ⟨s, rfl⟩ := hN
  have key : ∀ x : s, ∃ a : R, a ≠ 0 ∧ a • (x : V) ∈ M := fun x =>
    exists_ne_zero_smul_mem_of_mem_span_fractionField K (h (Submodule.subset_span x.2))
  choose c hc hc' using key
  refine ⟨∏ x, c x, Finset.prod_ne_zero_iff.mpr fun x _ => hc x, ?_⟩
  rw [Submodule.smul_span, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨d, hd⟩ : c ⟨x, hx⟩ ∣ ∏ x, c x := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
  change (∏ x, c x) • x ∈ M
  rw [hd, mul_comm, mul_smul]
  exact M.smul_mem _ (hc' ⟨x, hx⟩)

theorem span_inf_restrictScalars_eq {M : Submodule R V} {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) = W := by
  refine le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_
  obtain ⟨a, ha, hax⟩ := exists_ne_zero_smul_mem_of_mem_span_fractionField K (h hx)
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha
  rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
  exact Submodule.subset_span ⟨hax, W.smul_of_tower_mem a hx⟩

variable {K}


omit [IsDomain R] [IsFractionRing R K] in
theorem fractionField_smul_inf_restrictScalars {s : K} (hs : s ≠ 0) (Θ : Submodule R V) (W : Submodule K V) :
    s • Θ ⊓ W.restrictScalars R = s • (Θ ⊓ W.restrictScalars R) := by
  ext x
  simp only [Submodule.mem_inf, Submodule.mem_smul_pointwise_iff_exists,
    Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, h⟩
    exact ⟨y, ⟨hy, (W.smul_mem_iff hs).mp h⟩, rfl⟩
  · rintro ⟨y, ⟨hy, h⟩, rfl⟩
    exact ⟨⟨y, hy, rfl⟩, W.smul_mem s h⟩

variable [IsPrincipalIdealRing R]

theorem isLattice_comap_subtype {M : Submodule R V} (hM : M.FG) {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Submodule.IsLattice K (M.comap (W.subtype.restrictScalars R)) := by
  apply Submodule.IsLattice.of_fg K
  apply Submodule.fg_of_fg_map_injective (W.subtype.restrictScalars R) W.injective_subtype
  exact hM.of_le (Submodule.map_comap_le _ _)

theorem finrank_inf_restrictScalars_of_le_span {M : Submodule R V} (hM : M.FG)
    {W : Submodule K V} (h : W ≤ Submodule.span K (M : Set V)) :
    Module.finrank R ↥(M ⊓ W.restrictScalars R) = Module.finrank K W := by
  have : Submodule.IsFullLattice K (M.comap (W.subtype.restrictScalars R)) := by
    have := isLattice_comap_subtype hM h
    refine { span_eq_top := ?_ }
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨a, ha, hax⟩ := exists_ne_zero_smul_mem_of_mem_span_fractionField K (h x.2)
    have ha' : algebraMap R K a ≠ 0 := by simpa using ha
    rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
    exact Submodule.subset_span hax
  have e := Submodule.equivMapOfInjective (W.subtype.restrictScalars R) W.injective_subtype
    (M.comap (W.subtype.restrictScalars R))
  have hr : LinearMap.range (W.subtype.restrictScalars R) = W.restrictScalars R := by
    ext x
    simp
  rw [Submodule.map_comap_eq, hr, inf_comm] at e
  rw [← e.finrank_eq, Module.finrank, Module.finrank, Submodule.IsLattice.rank' K]

end Span

section FractionField

variable {R K V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
  [IsScalarTower R K V]

theorem log_ordFrac_units_smul_zpow {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℤ) :
    WithZero.log (Ring.ordFrac R (u • algebraMap R K ϖ ^ n)) = n := by
  rw [Units.smul_def, Algebra.smul_def, map_mul, Ring.ordFrac_of_isUnit u.isUnit, one_mul,
    map_zpow₀, Ring.ordFrac_irreducible hϖ, WithZero.log_zpow, WithZero.log_exp]
  simp

theorem log_ordFrac_algebraMap {a : R} (ha : a ≠ 0) :
    WithZero.log (Ring.ordFrac R (algebraMap R K a)) = (addVal R a).toNat := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have := log_ordFrac_units_smul_zpow (K := K) hϖ u n
  rw [Units.smul_def, Algebra.smul_def, zpow_natCast, ← map_pow, ← map_mul] at this
  rw [this, addVal_def' u hϖ]
  simp


variable (K) in
theorem relLength_ne_top_of_subset_span {A B : Submodule R V} (hA : A.FG)
    (h : (A : Set V) ⊆ Submodule.span K (B : Set V)) : relLength A B ≠ ⊤ := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  obtain ⟨a, ha, hab⟩ := exists_ne_zero_smul_le_of_le_span_fractionField K hA h
  exact ne_top_of_le_ne_top (relLength_smul_self_ne_top hA ha) (relLength_anti_right A hab)


variable (K) in
theorem subset_span_of_relLength_ne_top {A B : Submodule R V} (h : relLength A B ≠ ⊤) :
    (A : Set V) ⊆ Submodule.span K (B : Set V) := by
  intro x hx
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [relLength_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  obtain ⟨-, h⟩ := h
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd
    (M := Submodule.span R {(Submodule.Quotient.mk ⟨x, hx⟩ : A ⧸ B.submoduleOf A)}) ϖ
    ⟨_, Submodule.mem_span_singleton_self _⟩
  obtain ⟨y, hy'⟩ := y
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy'
  have h₁ : (ϖ ^ n * (ϖ * c - 1)) •
      (Submodule.Quotient.mk ⟨x, hx⟩ : A ⧸ B.submoduleOf A) = 0 := by
    have := congrArg Subtype.val hy
    simp only [Submodule.coe_smul, smul_smul] at this
    rw [mul_sub, mul_one, sub_smul, ← mul_assoc, ← pow_succ, sub_eq_zero]
    exact this
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h₁
  have h₂ : ϖ ^ n * (ϖ * c - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero n hϖ.ne_zero) fun h₀ =>
      hϖ.not_isUnit (IsUnit.of_mul_eq_one c (sub_eq_zero.mp h₀))
  have h₃ : algebraMap R K (ϖ ^ n * (ϖ * c - 1)) ≠ 0 := by
    rwa [map_ne_zero_iff _ (IsFractionRing.injective R K)]
  rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ h₃, algebraMap_smul]
  exact Submodule.subset_span h₁


variable (K) in
theorem lengthCommensurable_iff_span_eq {A B : Submodule R V} (hA : A.FG) (hB : B.FG) :
    LengthCommensurable A B ↔
      Submodule.span K (A : Set V) = Submodule.span K (B : Set V) :=
  ⟨fun h => le_antisymm (Submodule.span_le.mpr (subset_span_of_relLength_ne_top K h.1))
      (Submodule.span_le.mpr (subset_span_of_relLength_ne_top K h.2)),
    fun h => ⟨relLength_ne_top_of_subset_span K hA (h ▸ Submodule.subset_span),
      relLength_ne_top_of_subset_span K hB (h ▸ Submodule.subset_span)⟩⟩

theorem lengthCommensurable_inf_restrictScalars_of_le_span {M Θ : Submodule R V} (hM : M.FG)
    (hΘ : Θ.FG) {W : Submodule K V} (hW : W ≤ Submodule.span K (M : Set V))
    (hW' : W ≤ Submodule.span K (Θ : Set V)) :
    LengthCommensurable (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) := by
  rw [lengthCommensurable_iff_span_eq K (hM.of_le inf_le_left) (hΘ.of_le inf_le_left),
    span_inf_restrictScalars_eq K hW, span_inf_restrictScalars_eq K hW']

theorem signedLength_smul_self_fractionField {B : Submodule R V} (hB : B.FG) {s : K} (hs : s ≠ 0) :
    LengthCommensurable B (s • B) ∧
      signedLength B (s • B) = WithZero.log (Ring.ordFrac R s) * Module.finrank R B := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  have key : ∀ {a : R}, a ≠ 0 → LengthCommensurable B (algebraMap R K a • B) ∧
      signedLength B (algebraMap R K a • B) =
        WithZero.log (Ring.ordFrac R (algebraMap R K a)) * Module.finrank R B := by
    intro a ha
    have e : algebraMap R K a • B = a • B := by
      ext x
      simp only [Submodule.mem_smul_pointwise_iff_exists, algebraMap_smul]
    rw [e, log_ordFrac_algebraMap ha]
    exact ⟨lengthCommensurable_smul_self hB ha, signedLength_smul_self hB ha⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) s
  have hb₀ : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb₁ : algebraMap R K b ≠ 0 := by simpa using hb₀
  have ha₁ : algebraMap R K a ≠ 0 := fun h => hs (by rw [h, zero_div])
  have ha₀ : a ≠ 0 := by simpa using ha₁
  obtain ⟨ca, sa⟩ := key ha₀
  obtain ⟨cb, sb⟩ := key hb₀
  have hreg : IsSMulRegular V (algebraMap R K a / algebraMap R K b) := IsSMulRegular.of_ne_zero hs
  have e : (algebraMap R K a / algebraMap R K b) • algebraMap R K b • B = algebraMap R K a • B := by
    rw [smul_smul, div_mul_cancel₀ _ hb₁]
  have cb' := (lengthCommensurable_smul_smul_iff hreg).mpr cb
  have sb' := cb.signedLength_smul_smul hreg
  rw [e] at cb' sb'
  refine ⟨ca.trans cb'.symm, ?_⟩
  rw [ca.signedLength_eq_add cb'.symm, cb'.signedLength_swap, sb', sa, sb, map_div₀,
    WithZero.log_div ((map_ne_zero _).mpr ha₁) ((map_ne_zero _).mpr hb₁)]
  ring

theorem LengthCommensurable.signedLength_smul_right {A B : Submodule R V}
    (h : LengthCommensurable A B) (hB : B.FG) {s : K} (hs : s ≠ 0) :
    LengthCommensurable A (s • B) ∧
      signedLength A (s • B) =
        signedLength A B + WithZero.log (Ring.ordFrac R s) * Module.finrank R B := by
  obtain ⟨c, e⟩ := signedLength_smul_self_fractionField hB hs
  exact ⟨h.trans c, by rw [h.signedLength_eq_add c, e]⟩

theorem signedLength_inf_smul_inf_of_le_span {M Θ : Submodule R V} (hM : M.FG) (hΘ : Θ.FG)
    {W : Submodule K V} (hW : W ≤ Submodule.span K (M : Set V))
    (hW' : W ≤ Submodule.span K (Θ : Set V)) {s : K} (hs : s ≠ 0) :
    LengthCommensurable (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) ∧
      LengthCommensurable (M ⊓ W.restrictScalars R) (s • Θ ⊓ W.restrictScalars R) ∧
      signedLength (M ⊓ W.restrictScalars R) (s • Θ ⊓ W.restrictScalars R) =
        signedLength (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) +
          WithZero.log (Ring.ordFrac R s) * Module.finrank K W := by
  have h := lengthCommensurable_inf_restrictScalars_of_le_span hM hΘ hW hW'
  rw [fractionField_smul_inf_restrictScalars hs, ← finrank_inf_restrictScalars_of_le_span hΘ hW']
  exact ⟨h, h.signedLength_smul_right (hΘ.of_le inf_le_left) hs⟩

theorem signedLength_inf_smul_inf (M Θ : Submodule R V) [Submodule.IsFullLattice K M]
    [Submodule.IsFullLattice K Θ] (W : Submodule K V) {s : K} (hs : s ≠ 0) :
    LengthCommensurable (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) ∧
      LengthCommensurable (M ⊓ W.restrictScalars R) (s • Θ ⊓ W.restrictScalars R) ∧
      signedLength (M ⊓ W.restrictScalars R) (s • Θ ⊓ W.restrictScalars R) =
        signedLength (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) +
          WithZero.log (Ring.ordFrac R s) * Module.finrank K W :=
  signedLength_inf_smul_inf_of_le_span (Submodule.IsLattice.fg K M) (Submodule.IsLattice.fg K Θ)
    (by rw [Submodule.IsFullLattice.span_eq_top]; exact le_top)
    (by rw [Submodule.IsFullLattice.span_eq_top]; exact le_top) hs

theorem signedLength_inf_smul_inf_zpow {ϖ : R} (hϖ : Irreducible ϖ) (M Θ : Submodule R V)
    [Submodule.IsFullLattice K M] [Submodule.IsFullLattice K Θ] (W : Submodule K V) (u : Rˣ) (n : ℤ) :
    signedLength (M ⊓ W.restrictScalars R)
        ((u • algebraMap R K ϖ ^ n) • Θ ⊓ W.restrictScalars R) =
      signedLength (M ⊓ W.restrictScalars R) (Θ ⊓ W.restrictScalars R) +
        n * Module.finrank K W := by
  have hs : u • algebraMap R K ϖ ^ n ≠ 0 := by
    rw [ne_eq, smul_eq_zero_iff_eq]
    exact zpow_ne_zero n (by simpa using hϖ.ne_zero)
  rw [(signedLength_inf_smul_inf M Θ W hs).2.2, log_ordFrac_units_smul_zpow hϖ]

end FractionField

end GlobalTheory
end

noncomputable section

open Module
open scoped TensorProduct NumberField

namespace GlobalTheory.BadCount.RankRead

theorem finrank_iInf_ker_semilinear {L M W X ι κ : Type} [Field L] [Field M] [AddCommGroup W] [Module L W] [AddCommGroup X]
    [Module M X] [Finite ι] [Finite κ] {σ : L →+* M} (Φ : W →ₛₗ[σ] X) (b : Basis κ L W) (hb : LinearIndependent M fun k => Φ (b k))
    (a : ι → W →ₗ[L] W) (a' : ι → X →ₗ[M] X) (h : ∀ i w, a' i (Φ w) = Φ (a i w)) :
    finrank L (⨅ i, LinearMap.ker (a i) : Submodule L W) =
      finrank M ((⨅ i, LinearMap.ker (a' i)) ⊓ Submodule.span M (Set.range Φ) : Submodule M X) := by
  haveI := Module.Finite.of_basis b
  letI : Algebra L M := σ.toAlgebra
  letI : Module L X := Module.compHom X σ
  haveI : IsScalarTower L M X := ⟨fun x y z => mul_smul (σ x) y z⟩
  let U := Submodule.span M (Set.range Φ)
  let f : W →ₗ[L] U :=
    { toFun := fun w => ⟨Φ w, Submodule.subset_span ⟨w, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add Φ x y)
      map_smul' := fun x y => Subtype.ext (map_smulₛₗ Φ x y) }
  have hU : U = Submodule.span M (Set.range fun k => Φ (b k)) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩))
    rintro _ ⟨w, rfl⟩
    haveI := Fintype.ofFinite κ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr w, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis κ M U := (Basis.span hb).map (LinearEquiv.ofEq _ _ hU.symm)
  have hc : ∀ k, c k = f (b k) := fun k => Subtype.ext (by simp [c, f])
  have hf : IsBaseChange M f := by
    refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis M b).equiv c (Equiv.refl _)) fun m => ?_
    have : ((((Algebra.TensorProduct.basis M b).equiv c (Equiv.refl _)).toLinearMap.restrictScalars L) ∘ₗ
        TensorProduct.mk L M W 1) = f := b.ext fun k => by
      rw [← hc]
      simp [← Algebra.TensorProduct.basis_apply]
    exact LinearMap.congr_fun this m
  have hm : ∀ i, ∀ x ∈ U, a' i x ∈ U := fun i => Submodule.span_le (p := U.comap (a' i)) |>.2 (by
    rintro _ ⟨w, rfl⟩
    exact Submodule.subset_span ⟨_, (h i w).symm⟩)
  rw [← GlobalTheory.finrank_iInf_ker_of_isBaseChange L M W U ι f a (fun i => (a' i).restrict (hm i)) hf
    (fun i w => Subtype.ext (h i w)), ← Submodule.finrank_map_subtype_eq U]
  refine congrArg (fun N : Submodule M X => finrank M N) (Submodule.ext fun x => ?_)
  simp only [Submodule.mem_map, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_inf]
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact ⟨fun i => congrArg Subtype.val (hy i), y.2⟩,
    fun ⟨h1, h2⟩ => ⟨⟨x, h2⟩, fun i => Subtype.ext (h1 i), rfl⟩⟩

def twistExt {F M V Γ : Type} [Field F] [Field M] [Algebra F M] [AddCommGroup V] [Module F V] [Group Γ]
    (τ : Representation F Γ V) (χ : Γ →* Mˣ) : Representation M Γ (M ⊗[F] V) where
  toFun γ := ((χ γ : Mˣ) : M) • (τ γ).baseChange M
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' γ δ := by
    rw [map_mul, map_mul, LinearMap.baseChange_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistExt_tmul {F M V Γ : Type} [Field F] [Field M] [Algebra F M] [AddCommGroup V] [Module F V] [Group Γ]
    (τ : Representation F Γ V) (χ : Γ →* Mˣ) (γ : Γ) (m : M) (v : V) :
    twistExt τ χ γ (m ⊗ₜ[F] v) = ((χ γ : Mˣ) : M) • (m ⊗ₜ[F] τ γ v) := rfl

theorem finrank_eq {K L F M C W V G G' Γ : Type} [Field K] [Field L] [Field F] [Field M] [Algebra K L] [Algebra F M]
    [AddCommGroup C] [Module K C] [AddCommGroup W] [Module L W] [Module K W] [IsScalarTower K L W] [AddCommGroup V] [Module F V]
    [Group G] [Fintype G] [Group G'] [Group Γ] [Finite Γ] {j : K →+* F} (σ : L →+* M)
    (hσ : ∀ a, σ (algebraMap K L a) = algebraMap F M (j a)) (ε : C →ₗ[K] W) (π : C →ₛₗ[j] V) {n : ℕ} (b : Fin n → C)
    (b₁ : Submodule.span K (Set.range b) = ⊤) (b₂ : LinearIndependent L fun k => ε (b k))
    (b₃ : Submodule.span L (Set.range fun k => ε (b k)) = ⊤) (b₄ : LinearIndependent F fun k => π (b k))
    (ρ : G →* (W →ₗ[L] W)) (chi : G →* Lˣ) (τ : Representation F Γ V) (θ : Γ →* G) (c : G ≃* G') (s : G' →* Γ)
    (hs : ∀ g, θ (s (c g)) = g) (hρ : ∀ γ f, ∃ f', ρ (θ γ) (ε f) = ε f' ∧ τ γ (π f) = π f')
    (hinv : ∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span F (Set.range π))
    (P : Subgroup G) (lam : P →* Lˣ) (Q : Subgroup Γ) (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ P) (lamb : Q →* Mˣ)
    (hlam : ∀ γ : Q, ((lamb γ : Mˣ) : M) = σ (lam ⟨θ γ, (hQ _).1 γ.2⟩ : Lˣ))
    (S : Submodule L W) (hS : ∀ w, w ∈ S ↔ ∀ p : P, ρ p w = ((chi p * lam p : Lˣ) : L) • w)
    (eC : G → L) (e : MonoidAlgebra M G') (he : ∀ g, σ (eC g) = e.coeff (c g)) :
    finrank L S = finrank M (eig (twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹) Q lamb) ∧
    finrank L (S ⊓ LinearMap.ker (∑ g, (eC g * ((chi g)⁻¹ : Lˣ)) • ρ g) : Submodule L W) =
      finrank M (eig (twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹) Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom ((twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹).comp s :
          Representation M G' (M ⊗[F] V)) e) : Submodule M (M ⊗[F] V)) := by
  set R := twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹ with hR
  let bW : Basis (Fin n) L W := Basis.mk b₂ b₃.ge
  let Φ : W →ₛₗ[σ] M ⊗[F] V :=
    { toFun := fun w => ∑ k, σ (bW.repr w k) • ((1 : M) ⊗ₜ[F] π (b k))
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun x y => by simp [Finset.smul_sum, mul_smul] }
  have hΦb : ∀ k, Φ (bW k) = (1 : M) ⊗ₜ[F] π (b k) := fun k => by
    show ∑ l, σ (bW.repr (bW k) l) • _ = _
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Finsupp.single_eq_of_ne hl]) (by simp)]
    simp
  have hΦ : ∀ f, Φ (ε f) = (1 : M) ⊗ₜ[F] π f := fun f => by
    have hf : f ∈ Submodule.span K (Set.range b) := b₁ ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; rw [← hΦb, Basis.mk_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), TensorProduct.tmul_add]
    | smul t x _ hx =>
      rw [map_smul, ← algebraMap_smul L, map_smulₛₗ, hx, map_smulₛₗ, hσ, algebraMap_smul, TensorProduct.tmul_smul]
  have hind : LinearIndependent M fun k => Φ (bW k) := by
    simp only [hΦb]
    exact Module.Flat.linearIndependent_one_tmul b₄
  have hRΦ : ∀ γ w, R γ (Φ w) = Φ ((((chi (θ γ))⁻¹ : Lˣ) : L) • ρ (θ γ) w) := fun γ w => by
    rw [← bW.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨f', h1, h2⟩ := hρ γ (b k)
    rw [hΦb, Basis.mk_apply, h1, hΦ, hR, twistExt_tmul, h2, smul_comm]
    simp
  have hE : eig R Q lamb ≤ Submodule.span M (Set.range Φ) := fun x hx => by
    have h0 := GlobalTheory.GaloisDescent.span_image_iInf (TensorProduct.isBaseChange F V M)
      fun γ : θ.ker => LinearMap.ker (τ γ - LinearMap.id)
    have h1 : x ∈ Submodule.span M (TensorProduct.mk F M V 1 ''
        (⨅ γ : θ.ker, LinearMap.ker (τ γ - LinearMap.id) : Submodule F V)) := by
      rw [h0, Submodule.mem_iInf]
      intro γ
      have hγ : θ γ = 1 := γ.2
      have hq : (γ : Γ) ∈ Q := (hQ _).2 (hγ ▸ P.one_mem)
      rw [GlobalTheory.GaloisDescent.span_image_ker (TensorProduct.isBaseChange F V M) (TensorProduct.isBaseChange F V M) _
        ((τ γ).baseChange M - LinearMap.id) (fun v => by simp [TensorProduct.tmul_sub])]
      have := (mem_eig R Q lamb x).1 hx ⟨γ, hq⟩
      rw [hlam, show (⟨θ γ, (hQ _).1 hq⟩ : P) = 1 from Subtype.ext hγ] at this
      simpa [hR, twistExt, hγ, sub_eq_zero] using this
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨v, hv, rfl⟩
    have hv' := hinv v fun γ hγ => sub_eq_zero.1 ((Submodule.mem_iInf _).1 hv ⟨γ, hγ⟩)
    clear hv
    induction hv' using Submodule.span_induction with
    | mem _ h => obtain ⟨f, rfl⟩ := h; exact Submodule.subset_span ⟨_, hΦ f⟩
    | zero => simp
    | add x y _ _ hx hy =>
      change (TensorProduct.mk F M V 1) (x + y) ∈ Submodule.span M (Set.range Φ)
      rw [map_add]
      exact add_mem hx hy
    | smul t x _ hx => rw [map_smul, ← algebraMap_smul M]; exact Submodule.smul_mem _ _ hx
  let a : Q → W →ₗ[L] W := fun γ => (((chi (θ γ))⁻¹ : Lˣ) : L) • ρ (θ γ) - ((lam ⟨θ γ, (hQ _).1 γ.2⟩ : Lˣ) : L) • LinearMap.id
  let a' : Q → M ⊗[F] V →ₗ[M] M ⊗[F] V := fun γ => R γ - ((lamb γ : Mˣ) : M) • LinearMap.id
  have ha : ∀ γ w, a' γ (Φ w) = Φ (a γ w) := fun γ w => by
    simp only [a, a', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hRΦ, map_sub, map_smulₛₗ, hlam]
  have hSa : S = ⨅ γ, LinearMap.ker (a γ) := by
    ext w
    have key : ∀ (g : G) (x : Lˣ), (((chi g)⁻¹ : Lˣ) : L) • ρ g w - (x : L) • w = 0 ↔ ρ g w = ((chi g * x : Lˣ) : L) • w :=
      fun g x => by rw [sub_eq_zero, ← Units.smul_def, inv_smul_eq_iff, Units.smul_def, smul_smul, Units.val_mul]
    rw [hS, Submodule.mem_iInf]
    refine ⟨fun h γ => (key _ _).2 (h ⟨θ γ, (hQ _).1 γ.2⟩), fun h p => ?_⟩
    have := (key _ _).1 (h ⟨s (c p), (hQ _).2 (by rw [hs]; exact p.2)⟩)
    simpa only [hs] using this
  have hEa : eig R Q lamb = ⨅ γ, LinearMap.ker (a' γ) := rfl
  refine ⟨by rw [hSa, finrank_iInf_ker_semilinear Φ bW hind a a' ha, ← hEa, inf_eq_left.2 hE], ?_⟩
  have h2 := finrank_iInf_ker_semilinear Φ bW hind (fun o : Option Q => o.elim (∑ g, (eC g * ((chi g)⁻¹ : Lˣ)) • ρ g) a)
    (fun o => o.elim (Representation.asAlgebraHom (R.comp s : Representation M G' (M ⊗[F] V)) e) a') (by
      rintro (_ | γ) w
      · haveI := Fintype.ofEquiv G c.toEquiv
        simp only [Option.elim]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
          LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
        refine (Fintype.sum_equiv c.toEquiv _ _ fun g => ?_).symm
        rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul, map_smulₛₗ, he]
        exact congrArg _ (by rw [MonoidHom.comp_apply, hRΦ]; simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hs])
      · exact ha γ w)
  rw [iInf_option, iInf_option] at h2
  simp only [Option.elim] at h2
  rw [hSa, inf_comm]
  refine h2.trans (congrArg (fun N : Submodule M (M ⊗[F] V) => finrank M N) ?_)
  rw [← hEa, inf_assoc, inf_eq_left.2 hE, inf_comm]

theorem rkK_inf {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL]
    [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL]
    [IsScalarTower (𝓞 Ks) Ks WL] {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (hK : A.IsKsForm) (hM : A.MKFull) (S : Submodule LL WL) :
    Formalism.HN.rkK (Submodule.span (𝓞 LL) (A.MK : Set WL) ⊓ S.restrictScalars (𝓞 LL)) = finrank LL S := by
  obtain ⟨n, b, h1, -, -, -, h5⟩ := hK
  have h : S ≤ Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL) := by
    refine le_top.trans (h5.ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨k, rfl⟩
    exact Submodule.span_mono Submodule.subset_span (Submodule.span_le_restrictScalars Ks LL _ (hM.2 ▸ h1 k))
  rw [Formalism.HN.rkK, GlobalTheory.span_inf_restrictScalars_eq LL h]

end GlobalTheory.BadCount.RankRead
