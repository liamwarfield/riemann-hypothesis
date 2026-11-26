module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionBoundOfWeightHyp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesLatticeTrivialQuotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExpStarZeroNear
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryBcrisOfDualExponentialZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightGoodReductionAtPrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCase
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Cocycle
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.ConnCoc

section General

variable {G Qp LL O : Type} [Group G] [TopologicalSpace G] [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem cocycle (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) (g h : G) :
    f (g * h) = f g + actT Y.L g (f h) := by
  apply Subtype.ext
  apply hι
  have e : ((f g + actT Y.L g (f h) : ↥Y.L.T) : Y.V) = (f g : Y.V) + Y.ρ g (f h : Y.V) := rfl
  rw [e, map_add (f := _), ι.equiv, hf, hf, hf, map_sub, map_mul, Module.End.mul_apply]
  abel

theorem continuous (Y Yt : LocLat G Qp LL O) (ι : LatHom Y.L Yt.L) (hι : Function.Injective ι.f)
    (yt : Yt.V) (f : G → ↥Y.L.T) (hf : ∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) :
    Continuous fun g => (f g : Y.V) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι.f (LinearMap.ker_eq_bot.2 hι)
  have : ContinuousSMul LL Y.V := IsModuleTopology.toContinuousSMul LL Y.V
  have hc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have e : (fun g => (f g : Y.V)) = fun g => r (Yt.ρ g yt) + (- r yt) := by
    funext g
    rw [← sub_eq_add_neg, ← map_sub, ← hf]
    exact (LinearMap.congr_fun hr _).symm
  rw [e]
  exact (hc.comp (Yt.cont yt)).add continuous_const

end General

theorem locConst {l : ℕ} [Fact l.Prime] {G V : Type} [TopologicalSpace G] [AddCommGroup V]
    [Module ℚ_[l] V] [TopologicalSpace V] (T : Set V) {m : ℕ} (w : Module.Basis (Fin m) ℚ_[l] V)
    (hw : ∀ x : V, x ∈ T ↔ ∀ i, ‖w.repr x i‖ ≤ 1) (hc : Continuous w.equivFun)
    (F : G → V) (hF : Continuous F) (n : ℕ) (g : G) :
    ∀ᶠ h in nhds g, ∃ y ∈ T, F h - F g = (l ^ n : ℕ) • y := by
  have hl : ((l : ℚ_[l]) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ i, ∀ᶠ h in nhds g,
      ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ < 1 := by
    intro i
    have c : Continuous fun h =>
        ‖((l : ℚ_[l]) ^ n)⁻¹ * (w.equivFun (F h) i - w.equivFun (F g) i)‖ :=
      (continuous_const.mul (((continuous_apply i).comp (hc.comp hF)).sub continuous_const)).norm
    apply c.continuousAt.eventually_lt continuousAt_const
    simp
  filter_upwards [Filter.eventually_all.2 key] with h hh
  refine ⟨((l : ℚ_[l]) ^ n)⁻¹ • (F h - F g), (hw _).2 fun i => ?_, ?_⟩
  · have := (hh i).le
    simpa [Module.Basis.equivFun_apply] using this
  · rw [← Nat.cast_smul_eq_nsmul ℚ_[l], smul_smul, Nat.cast_pow, mul_inv_cancel₀ hl, one_smul]

theorem conn : ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (LL : FinExt l) (Y Yt : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom Y.L Yt.L), Function.Injective ι.f → ∀ (yt : Yt.V) (f : G → ↥Y.L.T), (∀ g, ι.f (f g : Y.V) = Yt.ρ g yt - yt) → (∀ g h, f (g * h) = f g + actT Y.L g (f h)) ∧ ∀ (n : ℕ) (g : G), ∀ᶠ h in nhds g, ∃ y : ↥Y.L.T, f h - f g = (l ^ n : ℕ) • y := by
  intro l _ G _ _ LL Y Yt ι hι yt f hf
  refine ⟨cocycle Y Yt ι hι yt f hf, fun n g => ?_⟩
  obtain ⟨m, w, hw, hc, -⟩ := GlobalTheory.Cyc.LatBasis.exists_basis l G LL Y
  have := locConst (Y.L.T : Set Y.V) w hw hc _ (continuous Y Yt ι hι yt f hf) n g
  filter_upwards [this] with h hh
  obtain ⟨y, hy, e⟩ := hh
  exact ⟨⟨y, hy⟩, Subtype.ext e⟩

end GlobalTheory.ConnCoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLayerIff
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LayerGroup

variable {l : ℕ} [Fact l.Prime]

theorem mem_layer_iff (K : FinExt l) (s : ℕ) (σ : GQ l) :
    σ ∈ Gj K s ↔ (∀ x ∈ K0 K, σ x = x) ∧ ∀ x : Om l, x ^ (l ^ s) = 1 → σ x = x := by

  have key : ∀ x : Om l,
      x ∈ IntermediateField.fixedField (Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l)) ↔ σ x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun h => h σ (Subgroup.mem_zpowers σ), fun h f hf => ?_⟩
    have hst : Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l) ≤
        MulAction.stabilizer (Om l ≃ₐ[ℚ_[l]] Om l) x :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
    exact MulAction.mem_stabilizer_iff.mp (hst hf)
  unfold Gj Ks
  rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
    IntermediateField.mem_fixingSubgroup_iff, ← Subgroup.zpowers_le,
    ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
  exact and_congr Iff.rfl ⟨fun h x hx => (key x).mp (h hx), fun h x hx => (key x).mpr (h x hx)⟩

private theorem absoluteGalois_apply_eq_self_of_mem_maxUnramified (K : FinExt l) {τ : GQ l} (hτ : τ ∈ GK K) {x : Om l} (hx : x ∈ K0 K) :
    τ x = x := by
  unfold K0 at hx
  exact (IntermediateField.mem_fixingSubgroup_iff K.1 τ).mp hτ x (SetLike.le_def.mp inf_le_left hx)

theorem normal_layer (K : FinExt l) (s : ℕ) : ((Gj K s).subgroupOf (GK K)).Normal := by

  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : GQ l) ∈ GK K := g.2
  have hgi : ((g : GQ l))⁻¹ ∈ GK K := inv_mem hg
  rw [mem_layer_iff] at hn ⊢
  obtain ⟨h0, h1⟩ := hn
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change (g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x
    rw [absoluteGalois_apply_eq_self_of_mem_maxUnramified K hgi hx, h0 x hx, absoluteGalois_apply_eq_self_of_mem_maxUnramified K hg hx]
  · change (g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x
    have hy : (((g : GQ l))⁻¹ x) ^ (l ^ s) = 1 := by rw [← map_pow, hx, map_one]
    rw [h1 _ hy]
    exact AlgEquiv.apply_symm_apply (g : GQ l) x

theorem layer_group : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), K.1 ≤ Ks K s → ((Gj K s).subgroupOf (GK K)).Normal ∧ ((Gj K s).subgroupOf (GK K)).FiniteIndex ∧ IsOpen (((Gj K s).subgroupOf (GK K) : Subgroup ↥(GK K)) : Set ↥(GK K)) ∧ padicValNat l ((Gj K s).subgroupOf (GK K)).index = padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) - padicValNat l (Module.finrank ℚ_[l] ↥K.1) := by
  intro l _ K s h
  have : IsGalois ℚ_[l] (Om l) := IsAlgClosure.isGalois ℚ_[l] (AlgebraicClosure ℚ_[l])
  have : FiniteDimensional ℚ_[l] (Ks K s) := GlobalTheory.Cyc.TwistLift.finite_Ks K s
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  have hle : Gj K s ≤ GK K := IntermediateField.fixingSubgroup_le h

  have hKs : Module.finrank ℚ_[l] (Ks K s) = (Gj K s).index :=
    IntermediateField.finrank_eq_fixingSubgroup_index _ (Ks K s)
  have hK : Module.finrank ℚ_[l] K.1 = (GK K).index :=
    IntermediateField.finrank_eq_fixingSubgroup_index _ K.1
  have hmul : ((Gj K s).subgroupOf (GK K)).index * (GK K).index = (Gj K s).index :=
    Subgroup.relIndex_mul_index hle
  have hKpos : 0 < Module.finrank ℚ_[l] K.1 := Module.finrank_pos
  have hKspos : 0 < Module.finrank ℚ_[l] (Ks K s) := Module.finrank_pos
  have hidx : ((Gj K s).subgroupOf (GK K)).index ≠ 0 := by
    intro h0
    rw [h0, zero_mul, ← hKs] at hmul
    omega
  refine ⟨normal_layer K s, ⟨hidx⟩, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (Ks K s)).preimage continuous_subtype_val
  · rw [hKs, ← hmul, ← hK, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hidx hKpos.ne']
    omega

end GlobalTheory.Cyc.LayerGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContractEquivariant
noncomputable section

namespace GlobalTheory.PushCob

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage TensorProduct

theorem contract_equivariant {R Y Q : Type} [CommRing R] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Q] [Module R Q] (ψ : Y →ₗ[R] R) (A : Y →ₗ[R] Y) (B : Q →ₗ[R] Q) (u t : R)
    (h : ∀ y, ∃ z, ψ (A y) - u * ψ y = t * z) (x : Y ⊗[R] Q) :
    ∃ q : Q, TensorProduct.lid R Q (ψ.rTensor Q (TensorProduct.map A B x)) =
      u • B (TensorProduct.lid R Q (ψ.rTensor Q x)) + t • q := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul y q =>
    obtain ⟨z, hz⟩ := h y
    refine ⟨z • B q, ?_⟩
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul,
      smul_smul, ← add_smul]
    rw [← hz]; congr 1; ring
  | add x x' hx hx' =>
    obtain ⟨q, hq⟩ := hx
    obtain ⟨q', hq'⟩ := hx'
    refine ⟨q + q', ?_⟩
    simp only [map_add (f := _), hq, hq', smul_add]
    abel

theorem actQab_mk {O G WC : Type} [CommRing O] [Group G] [CommRing WC] [Algebra O WC]
    {AA : Subalgebra O WC} {act : G →* (WC ≃ₐ[O] WC)} {ξ : WCˣ} (h : XiOK AA act ξ) (a b : ℤ)
    (g : G) (m : ↥(Mxi AA ξ a)) :
    actQab h a b g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (actM h a g m) := rfl

variable {l : ℕ} [Fact l.Prime]

theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

theorem inclW_zl (z : ℤ_[l]) :
    inclW l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (WCb l) z := (inclWA l).commutes z

theorem mem_Mxi {P : LocPrime l} (AI : LocAinf l P) (k : ℕ) (w : WCb l)
    (hw : w ∈ Mxi (AinfSub l) (xiU AI) (k : ℤ)) : ∃ a : Ainf l, w = inclW l (AI.ξ ^ k * a) := by
  obtain ⟨y, ⟨a, rfl⟩, rfl⟩ := hw
  refine ⟨a, ?_⟩
  rw [LinearMap.mulLeft_apply, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]
  rfl

theorem mem_Mxi_zero {P : LocPrime l} (AI : LocAinf l P) (w : ↥(Mxi (AinfSub l) (xiU AI) 0)) :
    ∃ a : Ainf l, (w : WCb l) = inclW l a := by
  simpa using mem_Mxi AI 0 w w.2

def scaled {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) : Y →ₗ[ℤ_[l]] ℤ_[l] where
  toFun y := ⟨(l : ℚ_[l]) ^ r * ψ y, by
    have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [PadicInt.mem_subring_iff, norm_mul, norm_pow, Padic.norm_p, inv_pow,
      inv_mul_le_iff₀ (by positivity), mul_one]
    exact h y⟩
  map_add' y y' := by
    apply Subtype.ext
    change _ = (l : ℚ_[l]) ^ r * ψ y + (l : ℚ_[l]) ^ r * ψ y'
    rw [← mul_add, ← map_add (f := _)]
  map_smul' z y := by
    apply PadicInt.ext
    change (l : ℚ_[l]) ^ r * ψ (z • y) = (z : ℚ_[l]) * ((l : ℚ_[l]) ^ r * ψ y)
    rw [map_smul, Algebra.smul_def, PadicInt.algebraMap_apply]
    ring

theorem scaled_coe {Y : Type} [AddCommGroup Y] [Module ℤ_[l] Y] (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (r : ℕ)
    (h : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) (y : Y) :
    ((scaled ψ r h y : ℤ_[l]) : ℚ_[l]) = (l : ℚ_[l]) ^ r * ψ y := rfl

theorem push_coboundary : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s e r N : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥(Gj K s) →* (Y →ₗ[ℤ_[l]] Y)) (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]), (∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r) → (∀ (σ : GQ l) (hσ : σ ∈ Gj K s) (y : Y), ‖ψ (ρ ⟨σ, hσ⟩ y) - (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ y‖ ≤ 1) → ∀ (f : ↥(Gj K s) → Y) (c : GQ l → ℚ_[l]), (∀ (σ : GQ l) (hσ : σ ∈ Gj K s), c σ = ψ (f ⟨σ, hσ⟩)) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → IsCob (repQ (D.locA l) (Gj K s) ρ 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ N • (f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) → ∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l, algebraMap ℚ_[l] (D.loc l).R.BdR ((l : ℚ_[l]) ^ N * c σ) - (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈ ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1) := by
  intro D l _ K s e r N Y _ _ ρ ψ hψ hρ f c hc one hone hcob
  obtain ⟨x, hx⟩ := hcob
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (l : ℚ_[l]) ^ r ≠ 0 := pow_ne_zero _ hl
  obtain ⟨m0, hm0⟩ := Submodule.Quotient.mk_surjective _
    (TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ x))
  obtain ⟨a0, ha0⟩ := mem_Mxi_zero _ m0
  refine ⟨qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * io (D.locA l) a0, qB_mul_mem _ (io_mem _ _), ?_⟩
  intro σ hσ
  have hn : ‖(((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])‖ ≤ 1 := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, (cyc_basic l _ (D.loc l).χQ_cyc).1, one_zpow]
  set u' : ℚ_[l] := (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) with hu'
  let u : ℤ_[l] := ⟨u', hn⟩
  have hu : (u : ℚ_[l]) = u' := rfl
  obtain ⟨q, hq⟩ := contract_equivariant (scaled ψ r hψ) (ρ ⟨σ, hσ⟩)
    (actQab (act := (D.locA l).actWCbHom.comp (Gj K s).subtype)
      ⟨fun g x hx => (xiOK (D.locA l)).1 (g : GQ l) x hx, (xiOK (D.locA l)).2.1,
        fun g => (xiOK (D.locA l)).2.2 (g : GQ l)⟩ 0 ((e : ℤ) + 1) ⟨σ, hσ⟩) u ((l : ℤ_[l]) ^ r)
    (fun y => ⟨⟨_, hρ σ hσ y⟩, by
      apply Subtype.ext
      change (l : ℚ_[l]) ^ r * ψ (ρ ⟨σ, hσ⟩ y) - u' * ((l : ℚ_[l]) ^ r * ψ y) =
        (((l : ℤ_[l]) ^ r : ℤ_[l]) : ℚ_[l]) * (ψ (ρ ⟨σ, hσ⟩ y) - u' * ψ y)
      push_cast
      ring⟩) x
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := mem_Mxi_zero _ m
  have h1 := congrArg (fun w => TensorProduct.lid ℤ_[l] _ ((scaled ψ r hψ).rTensor _ w))
    (hx ⟨σ, hσ⟩)
  simp only [map_smul, map_sub, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h1
  rw [← hm0] at hq
  have h2 := h1.trans (congrArg₂ (· - ·) hq hm0.symm)
  beta_reduce at h2
  erw [actQab_mk] at h2
  simp only [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    ← Submodule.Quotient.mk_sub] at h2
  rw [Submodule.Quotient.eq, Submodule.mem_comap] at h2
  obtain ⟨a', ha'⟩ := mem_Mxi (D.locA l) (e + 1) _ (by rw [Nat.cast_succ]; exact h2)
  have h3 : algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ N * scaled ψ r hψ (f ⟨σ, hσ⟩)) -
      (algebraMap ℤ_[l] (Ainf l) u * (D.locA l).actW σ a0 +
        algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ r) * a - a0) = (D.locA l).ξ ^ (e + 1) * a' := by
    apply inclW_injective
    rw [← ha']
    have h4 : inclW l ((D.locA l).actW σ a0) = (D.locA l).actWCbHom σ (m0 : WCb l) := by
      rw [ha0, inclW_act]; rfl
    rw [map_sub, map_sub, map_add (f := _), inclW_zl, map_mul (inclW l), map_mul (inclW l), inclW_zl,
      inclW_zl, h4, ← ha0, ← ha]
    change _ = (l : ℤ_[l]) ^ N • scaled ψ r hψ (f ⟨σ, hσ⟩) • (one : WCb l) -
      (u • (D.locA l).actWCbHom σ (m0 : WCb l) + (l : ℤ_[l]) ^ r • (m : WCb l) - (m0 : WCb l))
    rw [hone, smul_smul, ← Algebra.algebraMap_eq_smul_one, Algebra.smul_def, Algebra.smul_def]
  have h5 := congrArg (io (D.locA l)) h3
  rw [map_sub, map_sub, map_add (f := _), io_zl _ (D.locT l), map_mul (io _), map_mul (io _),
    map_mul (io _), map_pow (io _), io_zl _ (D.locT l), io_zl _ (D.locT l), io_act] at h5
  have h6 : io (D.locA l) (D.locA l).ξ ^ (e + 1) * io (D.locA l) a' ∈
      FilB (D.loc l) ((e : ℤ) + 1) := by
    have := FilB_mul (FilB_pow (io_ξ_mem (D.locA l)) (e + 1)) (io_mem (D.locA l) a')
    simpa using this
  refine ⟨a, ?_⟩
  have h7 := qB_mul_mem ((l : ℚ_[l]) ^ r)⁻¹ h6
  rw [← h5] at h7
  convert h7 using 1
  have h8 : qB (D.loc l) ((l : ℚ_[l]) ^ r)⁻¹ * qB (D.loc l) ((l : ℚ_[l]) ^ r) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hlr, map_one]
  rw [map_mul ((D.loc l).actQdR σ), AlgEquiv.commutes, hc σ hσ, ← io_apply, PadicInt.coe_mul,
    scaled_coe, PadicInt.coe_pow, PadicInt.coe_pow, PadicInt.coe_natCast, hu]
  simp only [map_mul]
  linear_combination (-(qB (D.loc l) ((l : ℚ_[l]) ^ N) * qB (D.loc l) (ψ (f ⟨σ, hσ⟩))) + io (D.locA l) a) * h8

end GlobalTheory.PushCob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCocTmulOne
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open Topology Filter

namespace GlobalTheory.TensorOneCoc

theorem isCoc_tmul_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (G : Subgroup (GQ l)) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y] (ρ : ↥G →* (Y →ₗ[ℤ_[l]] Y)) (b : ℤ) (f : ↥G → Y), (∀ g h, f (g * h) = f g + ρ g (f h)) → (∀ (n : ℕ) (g : ↥G), ∀ᶠ h in nhds g, ∃ y : Y, f h - f g = (l ^ n : ℕ) • y) → ∀ one : ↥(Mxi (AinfSub l) (xiU AI) 0), (one : WCb l) = 1 → letI : TopologicalSpace (TensorProduct ℤ_[l] Y (Qab (AinfSub l) (xiU AI) 0 b)) := (Ideal.span {(l : ℤ_[l])}).adicModuleTopology _; IsCoc (repQ AI G ρ 0 b) (fun g => f g ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b)) := by
  intro l _ P AI G Y _ _ ρ b f hf hc one h1
  refine ⟨(GlobalTheory.continuous_adicModule_iff (l : ℤ_[l]) _).2 fun g n => ?_, fun g h => ?_⟩
  · filter_upwards [hc n g] with h ⟨y, e⟩
    refine ⟨y ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b), ?_⟩
    rw [← TensorProduct.sub_tmul, e, TensorProduct.smul_tmul', ← Nat.cast_pow,
      Nat.cast_smul_eq_nsmul]
  · have hq : actQab (xiOK AI) 0 b (g : GQ l)
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b) = Submodule.Quotient.mk one := by
      rw [actQab, Submodule.mapQ_apply]
      congr 1
      apply Subtype.ext
      change AI.actWCbHom (g : GQ l) (one : WCb l) = one
      rw [h1, map_one]
    have : repQ AI G ρ 0 b g (f h ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 b))
        = ρ g (f h) ⊗ₜ[ℤ_[l]] actQab (xiOK AI) 0 b (g : GQ l) (Submodule.Quotient.mk one) := rfl
    beta_reduce
    rw [this, hq, hf, TensorProduct.add_tmul]

end GlobalTheory.TensorOneCoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemHfDOfRestriction
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory

open TensorProduct

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V)

theorem corHf_actVB_tmul (g : G) (v : V) (b : B) :
    actVB PD ρ g (v ⊗ₜ[Qp] b) = ρ g v ⊗ₜ[Qp] PD.actB g b := by
  simp [actVB]

noncomputable def corHfRepVB : Representation LL G (V ⊗[Qp] B) where
  toFun g := actVB PD ρ g
  map_one' := by
    ext v b
    simp [corHf_actVB_tmul]
  map_mul' g h := by
    ext v b
    simp [corHf_actVB_tmul]

def corHfRepO (O : Type) [CommRing O] [Algebra O LL] [Module O V] [IsScalarTower O LL V] :
    Representation O G V where
  toFun g := (ρ g).restrictScalars O
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousConstSMul LL V]

theorem index_smul_mem_HfD [CharZero LL] (L : Lattice (O := O) ρ) (hρ : ∀ g, Continuous (ρ g))
    (hρ' : ∀ x, Continuous fun g => ρ g x) (H : Subgroup G) [H.Normal] [H.FiniteIndex]
    (hH : IsOpen (H : Set G)) (Z f₀ : G → V) (hZ : ContinuousOn Z H)
    (hc : ∀ g ∈ H, ∀ h ∈ H, Z (g * h) = Z g + ρ g (Z h))
    (hX : ∃ X : V ⊗[Qp] B, ∀ h ∈ H, Z h ⊗ₜ[Qp] (1 : B) = actVB PD ρ h X - X)
    (h₀ : ∀ g h, f₀ (g * h) - (f₀ g + ρ g (f₀ h)) ∈ L.T) (hZf : ∀ h ∈ H, Z h - f₀ h ∈ L.T) :
    (fun g => H.index • (Submodule.Quotient.mk (f₀ g) : V ⧸ L.T)) ∈ HfD PD L := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  obtain ⟨F, hF, hFc, ⟨x, hx⟩, hY⟩ := exists_corestriction_cocycle O G V (corHfRepO ρ O) H hH hρ hρ'
    Z hZ hc
  obtain ⟨x', hx'⟩ := hY L.T L.stable f₀ 0 h₀ (by simpa using hZf)
  obtain ⟨X, hX⟩ := hX
  have hmul : ∀ a b y, actVB PD ρ a (actVB PD ρ b y) = actVB PD ρ (a * b) y := by
    intro a b y
    exact (LinearMap.congr_fun ((corHfRepVB PD ρ).map_mul a b) y).symm
  have h1 : ∀ g (v : V), actVB PD ρ g (v ⊗ₜ[Qp] (1 : B)) = ρ g v ⊗ₜ[Qp] (1 : B) := by
    intro g v
    rw [corHf_actVB_tmul, map_one]
  obtain ⟨y, hy⟩ := index_smul_cocycle_eq_coboundary LL G (V ⊗[Qp] B) (corHfRepVB PD ρ) H
    (fun g => F g ⊗ₜ[Qp] (1 : B))
    (by
      intro g h
      change _ = _ + actVB PD ρ g _
      rw [h1, hFc, add_tmul]
      rfl)
    ⟨(∑ q : G ⧸ H, actVB PD ρ q.out X) + x ⊗ₜ[Qp] (1 : B), by
      intro h hh
      change _ = actVB PD ρ h _ - _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hx h hh, finsum_eq_sum_of_fintype, add_tmul, sum_tmul, map_add (f := _), map_sum, h1, sub_tmul]
      have : ∀ q : G ⧸ H, (corHfRepO ρ O q.out (Z (q.out⁻¹ * h * q.out))) ⊗ₜ[Qp] (1 : B) =
          actVB PD ρ h (actVB PD ρ q.out X) - actVB PD ρ q.out X := by
        intro q
        change (ρ q.out _) ⊗ₜ[Qp] (1 : B) = _
        rw [← h1, hX _ (Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out), map_sub, hmul, hmul]
        congr 3
        group
      rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_sub_distrib]
      change _ + (ρ h x ⊗ₜ[Qp] (1 : B) - _) = _
      abel⟩
  have hn : (H.index : LL) ≠ 0 := Nat.cast_ne_zero.mpr Subgroup.FiniteIndex.index_ne_zero
  have hFf : F ∈ finiteCocycles PD ρ := by
    refine ⟨⟨hF, hFc⟩, (H.index : LL)⁻¹ • y, fun g => ?_⟩
    have := hy g
    change _ = actVB PD ρ g y - y at this
    rw [map_smul, ← smul_sub, ← this, ← Nat.cast_smul_eq_nsmul LL, inv_smul_smul₀ hn]
  have e : (fun g => H.index • (Submodule.Quotient.mk (f₀ g) : V ⧸ L.T)) =
      LinearMap.compLeft L.T.mkQ G F -
        (LinearMap.pi fun g => actD L g - LinearMap.id) (Submodule.Quotient.mk x') := by
    funext g
    have := (Submodule.Quotient.mk_eq_zero L.T).mpr (hx' g)
    change L.T.mkQ _ = 0 at this
    rw [map_sub, map_sub, map_sub, map_nsmul] at this
    change H.index • L.T.mkQ (f₀ g) = L.T.mkQ (F g) - (L.T.mkQ (corHfRepO ρ O g x') - L.T.mkQ x')
    rw [← sub_eq_zero, ← neg_eq_zero, ← this]
    abel
  rw [e]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨F, hFf, rfl⟩)
    (Submodule.mem_sup_right ⟨_, rfl⟩)

end General

theorem corHf_exists_mul_eq_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
    (n k : ℕ) (hn : n ≠ 0) (hk : padicValNat l n ≤ k) : ∃ u : O, u * (n : O) = ((l ^ k : ℕ) : O) := by
  have hn' : (n : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have : (n : ℤ_[l]) ∣ (l : ℤ_[l]) ^ k := by
    obtain ⟨m, hm⟩ : l ^ padicValNat l n ∣ n := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have hlm : ¬ l ∣ m := by
      rintro ⟨c, rfl⟩
      apply pow_succ_padicValNat_not_dvd (p := l) hn
      exact ⟨c, by rw [pow_succ, mul_assoc]; simpa only [Nat.padicValNat_def] using hm⟩
    have hu : IsUnit (m : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      exact PadicInt.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hlm)
    have e : (n : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l n * m := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hm
    rw [e, hu.mul_right_dvd]
    exact pow_dvd_pow _ hk
  obtain ⟨c, hc⟩ := this
  refine ⟨algebraMap ℤ_[l] O c, ?_⟩
  have := congrArg (algebraMap ℤ_[l] O) hc
  simp only [map_pow, map_natCast, map_mul] at this
  rw [Nat.cast_pow, this, mul_comm]

theorem corHf_nsmul_mem {O G M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (S : Submodule O (G → M)) (f : G → M) (n m : ℕ) (h : ∃ u : O, u * (n : O) = (m : O))
    (hf : (fun g => n • f g) ∈ S) : (fun g => m • f g) ∈ S := by
  obtain ⟨u, hu⟩ := h
  convert S.smul_mem u hf using 1
  funext g
  rw [Pi.smul_apply, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, smul_smul, hu]


set_option synthInstance.maxHeartbeats 400000 in
theorem pow_smul_mem_HfD_of_restriction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K)) [H.Normal] [H.FiniteIndex], IsOpen (H : Set ↥(GK K)) → ∀ (Z f₀ : ↥(GK K) → V.V), ContinuousOn Z H → (∀ g ∈ H, ∀ h ∈ H, Z (g * h) = Z g + V.ρ g (Z h)) → (∃ X : TensorProduct ℚ_[l] V.V P.R.B, ∀ h ∈ H, Z h ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) V.ρ h X - X) → (∀ g h, f₀ (g * h) - (f₀ g + V.ρ g (f₀ h)) ∈ V.L.T) → (∀ h ∈ H, Z h - f₀ h ∈ V.L.T) → ∀ k : ℕ, padicValNat l H.index ≤ k → (fun g => (l ^ k : ℕ) • (Submodule.Quotient.mk (f₀ g) : V.V ⧸ V.L.T)) ∈ HfD (P.PD K) V.L := by
  intro l _ P K LL V H _ _ hH Z f₀ hZ hc hX h₀ hZf k hk
  haveI : IsTopologicalAddGroup V.V := IsModuleTopology.topologicalAddGroup ↥LL.1 V.V
  haveI : ContinuousSMul ↥LL.1 V.V := IsModuleTopology.toContinuousSMul ↥LL.1 V.V
  exact corHf_nsmul_mem _ _ H.index _
    (corHf_exists_mul_eq_pow l _ _ k Subgroup.FiniteIndex.index_ne_zero hk)
    (index_smul_mem_HfD (P.PD K) V.ρ V.L
      (fun g => IsModuleTopology.continuous_of_linearMap (V.ρ g)) V.cont H hH Z f₀ hZ hc hX h₀ hZf)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBound
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

noncomputable section

namespace GlobalTheory.Cyc.ClassBound

open TensorProduct
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem padicInt_hom_witt_ext_pt {R : Type} [CommRing R] [CharP R l]
    (f g : ℤ_[l] →+* WittVector l R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  ext n
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (n + 1) z)
  have hz : z = c * (l : ℤ_[l]) ^ (n + 1) + ((PadicInt.appr z (n + 1) : ℕ) : ℤ_[l]) := by
    rw [hc]; ring
  have h : f z - g z = (f c - g c) * (l : WittVector l R) ^ (n + 1) := by
    generalize PadicInt.appr z (n + 1) = m at hz
    rw [hz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [h, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self n), WittVector.zero_coeff]

theorem exists_coords {G : Type} [Group G] [TopologicalSpace G] {LL O : Type} [Field LL]
    [Algebra ℚ_[l] LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL] [Algebra ℤ_[l] O]
    (hc : ∀ a : ℤ_[l], algebraMap O LL (algebraMap ℤ_[l] O a) = algebraMap ℚ_[l] LL a)
    (Y V : LocLat G ℚ_[l] LL O) (φ : ↥Y.L.T →ₗ[O] (V.V ⧸ V.L.T)) {n : ℕ}
    (w : Module.Basis (Fin n) ℚ_[l] V.V) {m : ℕ} (u : Module.Basis (Fin m) ℚ_[l] Y.V)
    (hu : ∀ x : Y.V, x ∈ Y.L.T ↔ ∀ i, ‖u.repr x i‖ ≤ 1) :
    letI : Module ℤ_[l] ↥Y.L.T := Module.compHom ↥Y.L.T (algebraMap ℤ_[l] O)
    ∃ (Φ : ↥Y.L.T →+ V.V) (ψ : Fin n → (↥Y.L.T →ₗ[ℤ_[l]] ℚ_[l])) (r : ℕ),
      (∀ y, (Submodule.Quotient.mk (Φ y) : V.V ⧸ V.L.T) = φ y) ∧
      (∀ i y, ψ i y = w.repr (Φ y) i) ∧ ∀ i y, ‖ψ i y‖ ≤ (l : ℝ) ^ r := by
  letI : Module ℤ_[l] ↥Y.L.T := Module.compHom ↥Y.L.T (algebraMap ℤ_[l] O)
  haveI := Y.L.free
  obtain ⟨Φ, hΦ⟩ := Module.projective_lifting_property V.L.T.mkQ φ (Submodule.mkQ_surjective _)
  have hs : ∀ (a : ℤ_[l]) (y : ↥Y.L.T), Φ (a • y) = (a : ℚ_[l]) • Φ y := fun a y => by
    change Φ (algebraMap ℤ_[l] O a • y) = _
    rw [map_smul, ← algebraMap_smul LL, hc, algebraMap_smul]
  let ψ : Fin n → (↥Y.L.T →ₗ[ℤ_[l]] ℚ_[l]) := fun i =>
    { toFun := fun y => w.repr (Φ y) i
      map_add' := fun a b => by simp
      map_smul' := fun a y => by rw [hs, map_smul]; rfl }
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hu1 : ∀ j, u j ∈ Y.L.T := fun j => (hu _).2 fun i => by
    rw [u.repr_self, Finsupp.single_apply]; split_ifs <;> simp
  obtain ⟨r, hr⟩ : ∃ r : ℕ, ∀ i j, ‖ψ i ⟨u j, hu1 j⟩‖ ≤ (l : ℝ) ^ r := by
    obtain ⟨C, hC⟩ := (Set.finite_range fun p : Fin n × Fin m => ‖ψ p.1 ⟨u p.2, hu1 p.2⟩‖).bddAbove
    obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt C hl1
    exact ⟨r, fun i j => (hC ⟨(i, j), rfl⟩).trans hr.le⟩
  refine ⟨Φ.toAddMonoidHom, ψ, r, fun y => congrArg (fun F : _ →ₗ[_] _ => F y) hΦ, fun _ _ => rfl,
    fun i y => ?_⟩
  let a : Fin m → ℤ_[l] := fun j => ⟨u.repr (y : Y.V) j, (hu _).1 y.2 j⟩
  have hy : y = ∑ j, a j • (⟨u j, hu1 j⟩ : ↥Y.L.T) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    conv_lhs => rw [← u.sum_repr (y : Y.V)]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ = algebraMap ℤ_[l] O (a j) • u j
    rw [← algebraMap_smul LL (algebraMap ℤ_[l] O (a j)), hc, algebraMap_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hy, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun j _ => ?_
  rw [map_smul]
  change ‖u.repr (y : Y.V) j * _‖ ≤ _
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((hu _).1 y.2 j)).trans (hr i j)

theorem actVB_sum_tmul {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) {n : ℕ} (w : Module.Basis (Fin n) Qp V) (x : Fin n → B) (g : G)
    (c : Qp) (hc : ∀ v, ρ g v = c • v) (z : Fin n → Qp)
    (hz : ∀ i, algebraMap Qp B (z i) = c • PD.actB g (x i) - x i) :
    w.equivFun.symm z ⊗ₜ[Qp] (1 : B) =
      actVB PD ρ g (∑ i, w i ⊗ₜ[Qp] x i) - ∑ i, w i ⊗ₜ[Qp] x i := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib, Module.Basis.equivFun_symm_apply, sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = ρ g (w i) ⊗ₜ[Qp] PD.actB g (x i) - _
  rw [hc, smul_tmul, smul_tmul, ← tmul_sub, ← hz i, Algebra.algebraMap_eq_smul_one]


set_option maxHeartbeats 1600000 in
theorem mem_HfD_of_coords (P : LocPrime l) (K LL : FinExt l) (s : ℕ) (hK : K.1 ≤ Ks K s)
    (V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (c : GQ l → ℚ_[l])
    (hV : ∀ (g : ↥(GK K)) (x : V.V), V.ρ g x = c g • x) {n : ℕ}
    (w : Module.Basis (Fin n) ℚ_[l] V.V) (hw : ∀ x : V.V, x ∈ V.L.T ↔ ∀ i, ‖w.repr x i‖ ≤ 1)
    (hwc : Continuous w.equivFun.symm) (f₀ : ↥(GK K) → V.V)
    (hf₀ : ∀ g h, f₀ (g * h) - (f₀ g + V.ρ g (f₀ h)) ∈ V.L.T) (z : Fin n → GQ l → ℚ_[l])
    (hz : ∀ i, CocOn (Gj K s) (fun σ y => c σ * y) Set.univ (z i)) (x : Fin n → P.R.B)
    (hx : ∀ i, ∀ σ ∈ Gj K s, algebraMap ℚ_[l] P.R.B (z i σ) = c σ • P.actQ σ (x i) - x i)
    (hzf : ∀ i (g : ↥(GK K)), (g : GQ l) ∈ Gj K s → ‖z i g - w.repr (f₀ g) i‖ ≤ 1) :
    (fun g => (l ^ (padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) -
      padicValNat l (Module.finrank ℚ_[l] ↥K.1)) : ℕ) •
        (Submodule.Quotient.mk (f₀ g) : V.V ⧸ V.L.T)) ∈ HfD (P.PD K) V.L := by
  obtain ⟨hN, hF, hO, hI⟩ := GlobalTheory.Cyc.LayerGroup.layer_group l K s hK
  refine GlobalTheory.pow_smul_mem_HfD_of_restriction l P K LL V ((Gj K s).subgroupOf (GK K)) hO
    (fun g => w.equivFun.symm fun i => z i g) f₀ ?_ ?_ ⟨∑ i, w i ⊗ₜ[ℚ_[l]] x i, ?_⟩ hf₀ ?_ _ hI.le
  · refine hwc.comp_continuousOn (continuousOn_pi.2 fun i => ?_)
    exact (hz i).1.comp continuous_subtype_val.continuousOn fun g hg => hg
  · intro g hg h hh
    rw [hV, ← map_smul, ← map_add (f := _)]
    congr 1
    funext i
    exact (hz i).2.2 g hg h hh
  · intro h hh
    exact actVB_sum_tmul (P.PD K) V.ρ w x h (c h) (hV h) _ fun i => by
      rw [P.PD_actB]; exact hx i h hh
  · intro h hh
    refine (hw _).2 fun i => ?_
    have h1 : ∀ (a : Fin n → ℚ_[l]) (v : V.V),
        w.repr (w.equivFun.symm a - v) i = a i - w.repr v i := fun a v => by
      rw [map_sub w.repr, Finsupp.sub_apply, ← w.equivFun_apply, LinearEquiv.apply_symm_apply]
    exact (congrArg norm (h1 _ _)).le.trans (hzf i h hh)

theorem scalar_step (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K : FinExt l) (s : ℕ)
    (hs : Lev l s) (e r N : ℕ) (c : GQ l → ℚ_[l]) (hb : ∀ σ ∈ Gj K s, ‖c σ‖ ≤ (l : ℝ) ^ r)
    (hc : ∀ σ ∈ Gj K s, ∀ τ ∈ Gj K s, ‖c (σ * τ) - c σ -
      (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * c τ‖ ≤ 1)
    (hl : ∀ σ ∈ Gj K s, ∀ᶠ τ in nhdsWithin σ (Gj K s), ‖c τ - c σ‖ ≤ 1)
    (hr : ∃ b ∈ ((D.loc l).PD (botExt l)).Fil 0, ∀ σ ∈ Gj K s, ∃ a : Ainf l,
      algebraMap ℚ_[l] (D.loc l).R.BdR ((l : ℚ_[l]) ^ N * c σ) -
        (algebraMap ℚ_[l] (D.loc l).R.BdR (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) *
          (D.loc l).actQdR σ b - b) - (D.loc l).ιB ((D.locA l).ιA a) ∈
        ((D.loc l).PD (botExt l)).Fil ((e : ℤ) + 1)) :
    ∃ (z : GQ l → ℚ_[l]) (x : (D.loc l).R.B),
      CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧
      (∀ σ ∈ Gj K s, algebraMap ℚ_[l] (D.loc l).R.B (z σ) =
        (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • (D.loc l).actQ σ x - x) ∧
      ∀ σ ∈ Gj K s, ‖z σ - (l : ℚ_[l]) ^ (N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
        (s + padicValNat l (e + 1))) * c σ‖ ≤ 1 := by
  obtain ⟨z, hz, hzc⟩ := GlobalTheory.Cyc.TwistLift.lift_cocycle D h2 h4 l K s hs e r c hb hc hl
  obtain ⟨b, hb0, hbσ⟩ := hr
  have hl1 : ∀ k : ℕ, ‖(l : ℚ_[l]) ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (Padic.norm_p_lt_one).le
  have hsm : ∀ (k : ℕ) (j : ℤ) (y : (D.loc l).R.BdR), y ∈ ((D.loc l).PD (botExt l)).Fil j →
      (l : (D.loc l).R.BdR) ^ k * y ∈ ((D.loc l).PD (botExt l)).Fil j := fun k j y hy => by
    have := nsmul_mem hy (l ^ k)
    rwa [nsmul_eq_mul, Nat.cast_pow] at this
  have hz1 : CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y)
      Set.univ (fun σ => (l : ℚ_[l]) ^ N * z σ) :=
    ⟨continuousOn_const.mul hz.1, fun _ _ => trivial, fun g hg h hh => by
      simp only [hz.2.2 g hg h hh]; ring⟩
  obtain ⟨z', hz', hz'c⟩ := GlobalTheory.Cyc.ExpScalar.exists_expStar_zero_near D h2 h4 l K s hs e _ hz1
    ⟨(l : (D.loc l).R.BdR) ^ (s + padicValNat l (e + 1)) * b, hsm _ _ _ hb0, fun σ hσ => by
      obtain ⟨a, ha⟩ := hbσ σ hσ
      let u : ℤ_[l] := ⟨_, hzc σ hσ⟩
      have hu : z σ = (u : ℚ_[l]) + (l : ℚ_[l]) ^ (s + padicValNat l (e + 1)) * c σ := by
        simp [u]
      have hι : (D.loc l).ιB ((D.locA l).ιA (algebraMap ℤ_[l] (Ainf l) u)) =
          algebraMap ℚ_[l] _ (u : ℚ_[l]) := by
        have : (D.locA l).ιA (algebraMap ℤ_[l] (Ainf l) u) = algebraMap ℚ_[l] _ (u : ℚ_[l]) := by
          apply (D.locT l).eB.injective
          rw [(D.locT l).ιA, (D.locT l).zB, GlobalTheory.RingIface.zB_eq_aB_zA]
          exact congrArg (Formalism.Per.aB l)
            (padicInt_hom_witt_ext_pt (algebraMap ℤ_[l] (Ainf l)) (Formalism.Per.zA l) u)
        rw [this, AlgHom.commutes]
      refine ⟨(l : Ainf l) ^ (s + padicValNat l (e + 1)) * a +
        (l : Ainf l) ^ N * algebraMap ℤ_[l] (Ainf l) u, ?_⟩
      have := hsm (s + padicValNat l (e + 1)) _ _ ha
      convert this using 1
      simp only [hu, map_add (f := _), map_mul, map_pow, map_natCast, hι]
      ring⟩
  obtain ⟨x, hx⟩ := GlobalTheory.T.coboundary_bcris_of_dualExponential_zero D h2 h4 l K s hs e z' hz'
  refine ⟨z', x, hz'.1, hx, fun σ hσ => ?_⟩
  have h1 : z' σ - (l : ℚ_[l]) ^ (N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
        (s + padicValNat l (e + 1))) * c σ =
      (z' σ - (l : ℚ_[l]) ^ ((e + 2) * s + padicValNat l e + e / (l - 1) + 1) *
        ((l : ℚ_[l]) ^ N * z σ)) +
      (l : ℚ_[l]) ^ ((e + 2) * s + padicValNat l e + e / (l - 1) + 1 + N) *
        (z σ - (l : ℚ_[l]) ^ (s + padicValNat l (e + 1)) * c σ) := by ring
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz'c σ hσ) ?_)
  rw [norm_mul]
  exact mul_le_one₀ (hl1 _) (norm_nonneg _) (hzc σ hσ)

theorem scalar_of_isCob (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K : FinExt l) (s : ℕ)
    (hs : Lev l s) (hle : Gj K s ≤ GK K) (e N r : ℕ) (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y]
    (ρ : ↥(GK K) →* (Y →ₗ[ℤ_[l]] Y)) (f : ↥(GK K) → Y) (hf : ∀ g h, f (g * h) = f g + ρ g (f h))
    (hfl : ∀ (n : ℕ) (g : ↥(GK K)), ∀ᶠ h in nhds g, ∃ y : Y, f h - f g = (l ^ n : ℕ) • y)
    (one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0)) (hone : (one : WCb l) = 1)
    (hcob : IsCob (repQ (D.locA l) (Gj K s) (ρ.comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1))
      (fun g => (l : ℤ_[l]) ^ N • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))))
    (ψ : Y →ₗ[ℤ_[l]] ℚ_[l]) (hψr : ∀ y, ‖ψ y‖ ≤ (l : ℝ) ^ r)
    (hψe : ∀ (g : ↥(GK K)) (y : Y), ‖ψ (ρ g y) -
      (((D.loc l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ y‖ ≤ 1) :
    ∃ (z : GQ l → ℚ_[l]) (x : (D.loc l).R.B),
      CocOn (Gj K s) (fun σ y => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * y) Set.univ z ∧
      (∀ σ ∈ Gj K s, algebraMap ℚ_[l] (D.loc l).R.B (z σ) =
        (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • (D.loc l).actQ σ x - x) ∧
      ∀ g : ↥(GK K), (g : GQ l) ∈ Gj K s →
        ‖z g - (l : ℚ_[l]) ^ (N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
          (s + padicValNat l (e + 1))) * ψ (f g)‖ ≤ 1 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c : GQ l → ℚ_[l], ∀ (σ : GQ l) (h : σ ∈ GK K), c σ = ψ (f ⟨σ, h⟩) :=
    ⟨fun σ => if h : σ ∈ GK K then ψ (f ⟨σ, h⟩) else 0, fun σ h => dif_pos h⟩
  have H1 : ∀ σ ∈ Gj K s, ‖c σ‖ ≤ (l : ℝ) ^ r := fun σ hσ => by
    rw [hc σ (hle hσ)]; exact hψr _
  have H2 : ∀ σ ∈ Gj K s, ∀ τ ∈ Gj K s, ‖c (σ * τ) - c σ -
      (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * c τ‖ ≤ 1 := fun σ hσ τ hτ => by
    have h1 : f ⟨σ * τ, hle (mul_mem hσ hτ)⟩ = _ := hf ⟨σ, hle hσ⟩ ⟨τ, hle hτ⟩
    rw [hc σ (hle hσ), hc τ (hle hτ), hc _ (hle (mul_mem hσ hτ)), h1, map_add ψ,
      add_sub_cancel_left]
    exact hψe ⟨σ, hle hσ⟩ _
  have H3 : ∀ σ ∈ Gj K s, ∀ᶠ τ in nhdsWithin σ (Gj K s), ‖c τ - c σ‖ ≤ 1 := fun σ hσ => by
    refine Filter.Eventually.filter_mono (nhdsWithin_mono σ (hle : (Gj K s : Set (GQ l)) ⊆ GK K)) ?_
    have h1 := hfl r ⟨σ, hle hσ⟩
    have h3 : nhdsWithin σ (GK K : Set (GQ l)) =
        Filter.map Subtype.val (nhds (⟨σ, hle hσ⟩ : ↥(GK K))) :=
      nhdsWithin_eq_map_subtype_coe (hle hσ)
    rw [h3, Filter.eventually_map]
    filter_upwards [h1] with τ ⟨y, hy⟩
    rw [hc σ (hle hσ), hc τ τ.2, ← ψ.map_sub]
    have h5 : ψ (f ⟨τ, τ.2⟩ - f ⟨σ, hle hσ⟩) = (l ^ r : ℕ) • ψ y := by
      rw [← map_nsmul, ← hy]
    rw [h5, nsmul_eq_mul, norm_mul, Nat.cast_pow, Padic.norm_p_pow, zpow_neg, zpow_natCast]
    have hl0 : (0 : ℝ) < (l : ℝ) ^ r := by
      have := (Fact.out : l.Prime).pos
      positivity
    rw [inv_mul_le_iff₀ hl0, mul_one]
    exact hψr _
  have H4 := GlobalTheory.PushCob.push_coboundary D l K s e r N Y (ρ.comp (Subgroup.inclusion hle)) ψ hψr
    (fun σ hσ y => hψe ⟨σ, hle hσ⟩ y) (fun g => f (Subgroup.inclusion hle g)) c
    (fun σ hσ => hc σ (hle hσ)) one hone hcob
  obtain ⟨z, x, hz, hx, hzc⟩ := scalar_step D h2 h4 K s hs e r N c H1 H2 H3 H4
  refine ⟨z, x, hz, hx, fun g hg => ?_⟩
  have := hzc g hg
  rwa [hc g g.2] at this


set_option maxHeartbeats 800000 in
theorem mem_HfD_of_isCob (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K LL : FinExt l) (s : ℕ)
    (hs : Lev l s) (hK : K.1 ≤ Ks K s) (hle : Gj K s ≤ GK K) (e N r : ℕ)
    (Y : Type) [AddCommGroup Y] [Module ℤ_[l] Y]
    (ρ : ↥(GK K) →* (Y →ₗ[ℤ_[l]] Y)) (f : ↥(GK K) → Y) (hf : ∀ g h, f (g * h) = f g + ρ g (f h))
    (hfl : ∀ (n : ℕ) (g : ↥(GK K)), ∀ᶠ h in nhds g, ∃ y : Y, f h - f g = (l ^ n : ℕ) • y)
    (one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0)) (hone : (one : WCb l) = 1)
    (hcob : IsCob (repQ (D.locA l) (Gj K s) (ρ.comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1))
      (fun g => (l : ℤ_[l]) ^ N • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))))
    (V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hV : ∀ (g : ↥(GK K)) (x : V.V),
      V.ρ g x = (((D.loc l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • x) {n : ℕ}
    (w : Module.Basis (Fin n) ℚ_[l] V.V) (hw : ∀ x : V.V, x ∈ V.L.T ↔ ∀ i, ‖w.repr x i‖ ≤ 1)
    (hwc : Continuous w.equivFun.symm) (Φ : Y →+ V.V)
    (hΦ : ∀ g y, Φ (ρ g y) - V.ρ g (Φ y) ∈ V.L.T)
    (ψ : Fin n → (Y →ₗ[ℤ_[l]] ℚ_[l])) (hψ : ∀ i y, ψ i y = w.repr (Φ y) i)
    (hψr : ∀ i y, ‖ψ i y‖ ≤ (l : ℝ) ^ r) :
    (fun g => (l ^ (padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) -
      padicValNat l (Module.finrank ℚ_[l] ↥K.1)) : ℕ) •
        (Submodule.Quotient.mk ((l ^ (N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
          (s + padicValNat l (e + 1))) : ℕ) • Φ (f g)) : V.V ⧸ V.L.T)) ∈
      HfD ((D.loc l).PD K) V.L := by
  have hψe : ∀ i (g : ↥(GK K)) (y : Y), ‖ψ i (ρ g y) -
      (((D.loc l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * ψ i y‖ ≤ 1 := fun i g y => by
    have := (hw _).1 (hΦ g y) i
    rwa [map_sub w.repr, Finsupp.sub_apply, hV, map_smul w.repr, Finsupp.smul_apply, smul_eq_mul,
      ← hψ, ← hψ] at this
  choose z x hz hx hzc using fun i => scalar_of_isCob D h2 h4 K s hs hle e N r Y ρ f hf hfl one hone
    hcob (ψ i) (hψr i) (hψe i)
  generalize N + (e + 2) * s + padicValNat l e + e / (l - 1) + 1 +
    (s + padicValNat l (e + 1)) = k at hzc ⊢
  have A1 : ∀ g h, (l ^ k : ℕ) • Φ (f (g * h)) -
      ((l ^ k : ℕ) • Φ (f g) + V.ρ g ((l ^ k : ℕ) • Φ (f h))) ∈ V.L.T := fun g h => by
    rw [hf g h, map_add Φ, map_nsmul (V.ρ g), ← smul_add, ← smul_sub, add_sub_add_left_eq_sub]
    exact nsmul_mem (hΦ _ _) _
  have A2 : ∀ i (g : ↥(GK K)), (g : GQ l) ∈ Gj K s →
      ‖z i g - w.repr ((l ^ k : ℕ) • Φ (f g)) i‖ ≤ 1 := fun i g hg => by
    have := hzc i g hg
    rw [hψ] at this
    rw [map_nsmul w.repr, Finsupp.smul_apply, nsmul_eq_mul, Nat.cast_pow]
    exact this
  exact mem_HfD_of_coords (D.loc l) K LL s hK V
    (fun σ => (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l])) hV w hw hwc
    (fun g => (l ^ k : ℕ) • Φ (f g)) A1 z hz x hx A2

@[reducible] def modQuot {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (T : LocLat G Qp LL O) : Module O (T.V ⧸ T.L.T) :=
  Submodule.Quotient.module _

attribute [local instance high] modQuot

theorem pow_smul_eq_mk {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Submodule O V)
    (l a b : ℕ) (x : V) (y : V ⧸ T) (h : Submodule.Quotient.mk x = y) :
    (l ^ (a + b) : ℕ) • y = (l ^ b : ℕ) • (Submodule.Quotient.mk ((l ^ a : ℕ) • x) : V ⧸ T) := by
  rw [← T.mkQ_apply, map_nsmul, T.mkQ_apply, h, ← mul_nsmul, ← pow_add]

theorem lift_equivariant {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    (Y V : LocLat G Qp LL O) (φ : ↥Y.L.T →ₗ[O] (V.V ⧸ V.L.T))
    (hφ : ∀ g y, φ (actT Y.L g y) = actD V.L g (φ y)) (Φ : ↥Y.L.T →+ V.V)
    (hΦ : ∀ y, (Submodule.Quotient.mk (Φ y) : V.V ⧸ V.L.T) = φ y) (g : G) (y : ↥Y.L.T) :
    Φ (actT Y.L g y) - V.ρ g (Φ y) ∈ V.L.T := by
  refine (Submodule.Quotient.eq _).1 ?_
  have h1 := hφ g y
  rw [← hΦ, ← hΦ] at h1
  exact h1


set_option maxHeartbeats 800000 in
theorem mem_HfD_of_lattice (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h4 : ArchimedeanSignatureMatching D) (K LL : FinExt l) (s : ℕ)
    (hs : Lev l s) (hK : K.1 ≤ Ks K s) (hle : Gj K s ≤ GK K) (e N : ℕ)
    (Y V : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hV : ∀ g x, V.ρ g x =
      ((algebraMap ℚ_[l] ↥LL.1 (((D.loc l).PD K).χ g : ℚ_[l]))⁻¹) ^ e • x)
    (φ : ↥Y.L.T →ₗ[↥(OL LL)] (V.V ⧸ V.L.T)) (hφ : ∀ g y, φ (actT Y.L g y) = actD V.L g (φ y))
    (f : ↥(GK K) → ↥Y.L.T) (hf : ∀ g h, f (g * h) = f g + actT Y.L g (f h))
    (hfl : ∀ (n : ℕ) (g : ↥(GK K)), ∀ᶠ h in nhds g, ∃ y : ↥Y.L.T, f h - f g = (l ^ n : ℕ) • y)
    (one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0)) (hone : (one : WCb l) = 1)
    (hcob : letI := zlMod LL Y
      IsCob (repQ (D.locA l) (Gj K s) ((actTZ LL Y).comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1))
        (fun g => (l : ℤ_[l]) ^ N • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]]
          (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1))))) :
    (fun g => (l ^ cTB l s e (padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) -
      padicValNat l (Module.finrank ℚ_[l] ↥K.1)) N : ℕ) • φ (f g)) ∈ HfD ((D.loc l).PD K) V.L := by
  letI := zlMod LL Y
  choose n w hw hw' hwc using GlobalTheory.Cyc.LatBasis.exists_basis l ↥(GK K) LL V
  choose m u hu hu' huc using GlobalTheory.Cyc.LatBasis.exists_basis l ↥(GK K) LL Y
  choose Φ ψ r hΦ hψ hψr using exists_coords (l := l) (LL := ↥LL.1) (O := ↥(OL LL)) (fun _ => rfl) Y V φ w u hu
  have hV' : ∀ (g : ↥(GK K)) (x : V.V),
      V.ρ g x = (((D.loc l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • x := fun g x => by
    rw [hV, (D.loc l).PD_χ, ← map_inv₀, ← map_pow, algebraMap_smul, zpow_neg, zpow_natCast,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow]
  have hΦ' := lift_equivariant Y V φ hφ Φ hΦ
  have key := mem_HfD_of_isCob D h2 h4 K LL s hs hK hle e N r ↥Y.L.T (actTZ LL Y) f hf hfl one hone
    hcob V hV' w hw hwc Φ hΦ' ψ hψ hψr
  have h3 := fun a b g => pow_smul_eq_mk V.L.T l a b _ _ (hΦ (f g))
  rw [cTB, funext (h3 _ _)]
  exact key


set_option maxHeartbeats 800000 in
theorem class_bound : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBat S E := by
  intro D HW F hA l _ K s LL h S E e M0 h0 Yt Y Z Ve ι π hses _ hZ _ hVe hcr hW yt hyt _ φ hφ f hf
  obtain ⟨-, h2, -, h4, h5, -, h7, -, -⟩ := hA
  have hK : K.1 ≤ Ks K s := h.2.2.1
  have hle : Gj K s ≤ GK K := fun _ hg x => hg ⟨x.1, hK x.2⟩
  let one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0) := ⟨1, 1, (AinfSub l).one_mem, by simp⟩
  have hone : (one : WCb l) = 1 := rfl
  obtain ⟨hc1, hc2⟩ := GlobalTheory.ConnCoc.conn l ↥(GK K) LL Y Yt ι hses.1 yt f hf
  letI := zlMod LL Y
  have hcoc := GlobalTheory.TensorOneCoc.isCoc_tmul_one l (D.loc l) (D.locA l) (Gj K s) ↥Y.L.T
    ((actTZ LL Y).comp (Subgroup.inclusion hle)) ((e : ℤ) + 1)
    (fun g => f (Subgroup.inclusion hle g))
    (fun g g' => hc1 (Subgroup.inclusion hle g) (Subgroup.inclusion hle g'))
    (fun n g => (continuous_inclusion hle).continuousAt.eventually
      (hc2 n (Subgroup.inclusion hle g))) one hone
  have htor := GlobalTheory.T.ses_lattice_trivial_quotient D HW F h5 h7 l K s LL h e Yt Y Z ι π hle hses hZ hcr yt hyt f hf
    one hone
  have hcob := GlobalTheory.T.torsion_bound_of_weight_hyp D HW F h5 h7 l K s LL h Y M0 h0 0 ((e : ℤ) + 1) hle (by omega) hW _
    hcoc htor
  have key := mem_HfD_of_lattice D h2 h4 K LL s ⟨h.1, h.2.1⟩ hK hle e _ Y Ve hVe φ hφ f hc1 hc2
    one hone hcob
  have hl : ell S = l := (D.loc l).PD_p K
  have hs : S.W.s = s := (HW l).W_s K s LL h
  have hg : gK S = padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) -
      padicValNat l (Module.finrank ℚ_[l] ↥K.1) := by
    rw [gK, hl, hs]; rfl
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [cTBY, hg, hl, hs]
  exact key

end GlobalTheory.Cyc.ClassBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionClassBoundStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_extension_class_bound : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; TBat S E := by
  first | exact @GlobalTheory.Cyc.ClassBound.class_bound | exact GlobalTheory.Cyc.ClassBound.class_bound | (intros; apply GlobalTheory.Cyc.ClassBound.class_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCase
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.TheoremTB

theorem tb_assembled : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  intro D HW F hA h5 l _ K s LL h
  exact ⟨GlobalTheory.T.crystalline_extension_class_bound D HW F hA l K s LL h, GlobalTheory.T.weight_good_reduction_at_prime D HW F hA h5 l K s LL h⟩

end GlobalTheory.TheoremTB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCaseStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTorsionClassTheorem_goodCase : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTB.tb_assembled | exact GlobalTheory.TheoremTB.tb_assembled | (intros; apply GlobalTheory.TheoremTB.tb_assembled <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTBRecords

theorem aux_of_blochKato_tateDuality_eulerChar :
    GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
      ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
        LocalSituation.Conclusion4 D HW F := by
  intro hBK hTD hEC D HW F _Cm
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler hTD hEC D HW F
  exact GlobalTheory.T.twistedTorsionClassTheorem_goodCase D HW F hA (GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBK hTD hEC D)

end GlobalTheory.TheoremTBRecords
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEulerStatement
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LocalSituation.Conclusion4 D HW F := by
  first | exact @GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | exact GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar | (intros; apply GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar <;> assumption)
end
