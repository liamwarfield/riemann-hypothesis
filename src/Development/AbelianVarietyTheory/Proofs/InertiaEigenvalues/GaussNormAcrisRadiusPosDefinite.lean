module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDRAndDdRLeFilZeroOfTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocLatV
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentiallyCrystallineModuleEqCrystallineRestric
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedPowOfUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem log_interp (a b c : ℝ) (h : b - a ≠ 0) :
    a * ((b - c) / (b - a)) + b * (1 - (b - c) / (b - a)) = c := by
  field_simp
  ring

theorem gC_pos_of_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ →
    ρ < 1 → 0 < gC l ρ x := by
  intro l _ x hx ρ hρ0 hρ1
  have hN : ∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → IsGauss l r (gC l r) :=
    fun r h0 h1 => isGauss_gC_target l r h0 h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hi0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hi1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hnn : ∀ r, (l : ℝ)⁻¹ ≤ r → r < 1 → 0 ≤ gC l r x := fun r h0 h1 => ((hN r h0 h1).1 x).1
  have h0 : gC l (l : ℝ)⁻¹ x ≠ 0 := GlobalTheory.MemLoc.gauss_ne_zero l (fun r => gC l r) hN x hx
  rcases hρ0.eq_or_lt with h | h
  · subst h
    exact lt_of_le_of_ne (hnn _ le_rfl hi1) h0.symm
  by_contra hneg
  have hz : gC l ρ x = 0 := le_antisymm (not_lt.1 hneg) (hnn ρ hρ0 hρ1)
  obtain ⟨r₁, c, k, hr₁, -, hc, hmon⟩ := GlobalTheory.MemLoc.gauss_slope l (fun r => gC l r) hN x h0
  obtain ⟨ρ', h1', h2'⟩ := exists_between (lt_min hr₁ h)
  have hρ'0 : 0 < ρ' := hi0.trans h1'
  have hρ'r : ρ' < r₁ := h2'.trans_le (min_le_left _ _)
  have hρ'ρ : ρ' < ρ := h2'.trans_le (min_le_right _ _)
  have hρpos : 0 < ρ := hi0.trans h
  have hpos : 0 < gC l ρ' x := by
    have e : gC l ρ' x = c * ρ' ^ k := hmon ρ' h1' hρ'r
    rw [e]
    exact mul_pos hc (zpow_pos hρ'0 k)
  have hL1 : Real.log (l : ℝ)⁻¹ < Real.log ρ' := Real.log_lt_log hi0 h1'
  have hL2 : Real.log ρ' < Real.log ρ := Real.log_lt_log hρ'0 hρ'ρ
  have hd : 0 < Real.log ρ - Real.log (l : ℝ)⁻¹ := by linarith
  have ht0 : 0 ≤ (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) :=
    div_nonneg (by linarith) hd.le
  have ht1 : (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹) < 1 :=
    (div_lt_one hd).2 (by linarith)
  have he : (l : ℝ)⁻¹ ^ ((Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) *
      ρ ^ (1 - (Real.log ρ - Real.log ρ') / (Real.log ρ - Real.log (l : ℝ)⁻¹)) = ρ' := by
    rw [Real.rpow_def_of_pos hi0, Real.rpow_def_of_pos hρpos, ← Real.exp_add,
      log_interp _ _ _ hd.ne', Real.exp_log hρ'0]
  have hcv := GlobalTheory.T.gaussNormAcris_logConvex_in_radius l x (l : ℝ)⁻¹ ρ _ le_rfl h.le hρ1 ht0 ht1.le
  rw [he, hz, Real.zero_rpow (sub_pos.2 ht1).ne', mul_zero] at hcv
  linarith

theorem gC_pos_target : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 →
    0 < gC l ρ x :=
  gC_pos_of_ne_zero

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefiniteStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcrisRadius_pos_definite : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l), x ≠ 0 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → 0 < gC l ρ x := by
  first | exact @GlobalTheory.PMon.Gauss.gC_pos_target | exact GlobalTheory.PMon.Gauss.gC_pos_target | (intros; apply GlobalTheory.PMon.Gauss.gC_pos_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodOfComplete
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

namespace GlobalTheory.Decompl.LAdic

def Good (p : ℕ) (R : Type) [CommRing R] : Prop :=
  (∀ x : R, (p : R) * x = 0 → x = 0) ∧ (∀ x : R, (∀ k : ℕ, ∃ r, x = (p : R) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → R, ∃ s, ∀ k : ℕ, ∃ r, s - ∑ i ∈ Finset.range k, (p : R) ^ i * x i = (p : R) ^ k * r

theorem good_of_complete (p : ℕ) (R : Type) [CommRing R] (h : ∀ x : R, (p : R) * x = 0 → x = 0)
    [hc : IsAdicComplete (Ideal.span {(p : R)}) R] : Good p R := by
  have mem : ∀ (k : ℕ) (x : R), x ∈ (Ideal.span {(p : R)} ^ k • ⊤ : Submodule R R) ↔
      ∃ r, x = (p : R) ^ k * r := by
    intro k x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rfl
  refine ⟨h, fun x hx => ?_, fun x => ?_⟩
  · refine IsHausdorff.haus (I := Ideal.span {(p : R)}) hc.toIsHausdorff x fun k => ?_
    rw [SModEq.zero, mem]
    exact hx k
  · obtain ⟨s, hs⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R)}) hc.toIsPrecomplete
      (f := fun k => ∑ i ∈ Finset.range k, (p : R) ^ i * x i) (by
        intro m n hmn
        rw [SModEq.sub_mem, mem]
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
        refine ⟨-∑ i ∈ Finset.range k, (p : R) ^ i * x (m + i), ?_⟩
        rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
        simp only [pow_add, mul_assoc]
        ring)
    refine ⟨s, fun k => ?_⟩
    have := (hs k).symm
    rwa [SModEq.sub_mem, mem] at this

theorem good_tensor {Z O : Type} [CommRing Z] [CommRing O] [Algebra Z O] {I : Type} [Fintype I]
    (b : Module.Basis I Z O) {W : Type} [CommRing W] [Algebra Z W] (p : ℕ) (h : Good p W) :
    Good p (O ⊗[Z] W) := by
  have hp : ∀ (k : ℕ) (i : I) (x : O ⊗[Z] W),
      crd b i ((p : O ⊗[Z] W) ^ k * x) = (p : W) ^ k * crd b i x := by
    intro k i x
    rw [← Nat.cast_pow, crd_natCast_mul, Nat.cast_pow]
  refine ⟨fun x hx => ext_crd b fun i => ?_, fun x hx => ext_crd b fun i => ?_, fun x => ?_⟩
  · rw [map_zero]
    apply h.1
    rw [← crd_natCast_mul, hx, map_zero]
  · rw [map_zero]
    refine h.2.1 _ fun k => ?_
    obtain ⟨r, hr⟩ := hx k
    exact ⟨crd b i r, by rw [← hp, ← hr]⟩
  · choose s r hs using fun i => h.2.2 fun k => crd b i (x k)
    refine ⟨∑ j, b j ⊗ₜ[Z] s j, fun k => ⟨∑ j, b j ⊗ₜ[Z] r j k, ext_crd b fun i => ?_⟩⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, hp, crd_sum, crd_sum b (fun j => r j k), map_sum, ← hs]
    simp only [hp]

theorem good_witt (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Good p (WittVector p k) :=
  good_of_complete p _ fun x hx => WittVector.eq_zero_of_p_mul_eq_zero x (by rw [mul_comm]; exact hx)

theorem ladic_RW (l : ℕ) [Fact l.Prime] (LL : FinExt l) :
    (∀ x : RW LL, (l : RW LL) * x = 0 → x = 0) ∧
    (∀ x : RW LL, (∀ k : ℕ, ∃ r, x = (l : RW LL) ^ k * r) → x = 0) ∧
    ∀ x : ℕ → RW LL, ∃ s, ∀ k : ℕ, ∃ r,
      s - ∑ i ∈ Finset.range k, (l : RW LL) ^ i * x i = (l : RW LL) ^ k * r :=
  good_tensor (W := WCb l) (basisO LL) l (good_witt l (Cb l))

end GlobalTheory.Decompl.LAdic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem finrank_maxUnramified_eq_cyclotomicLevel (K E : FinExt l) (s : ℕ) (hs : 1 ≤ s) (hE : E.1 = Ks K s)
    (hle : K.1 ≤ E.1) : Module.finrank ℚ_[l] ↥(K0 E) = Module.finrank ℚ_[l] ↥(K0 K) := by
  have h0 : K0 K ≤ K0 E := inf_le_inf_right _ hle
  have h1 : Ks E s = Ks K s := by
    apply le_antisymm
    · refine sup_le ?_ le_sup_right
      rw [← hE]
      exact inf_le_left
    · exact sup_le_sup_right h0 _
  have h2 := finrank_Ks E s hs
  rw [h1, finrank_Ks K s hs] at h2
  have hlp : l.Prime := Fact.out
  have hpos : 0 < (l - 1) * l ^ (s - 1) :=
    Nat.mul_pos (Nat.sub_pos_of_lt hlp.one_lt) (pow_pos hlp.pos _)
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

theorem mem_GKs_iff_mem_Gj (P : LocPrime l) (K : FinExt l) (LL : FinExt l) (n : ℕ)
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (x : ↥(GK K)) :
    x ∈ W.GKs ↔ (x : GQ l) ∈ Gj K W.s := by
  have hχ : IsCyc P.χQ := P.χQ_cyc
  have hcb := (cyc_basic l P.χQ hχ).2.2 K
  have hK0 : (x : GQ l) ∈ (K0 K).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone (inf_le_left : K0 K ≤ K.1) x.2
  rw [W.GKs_def, (hcb x hK0).1 W.s, P.PD_χ, ← DictKs.le_v_iff P LL,
    (algebraMap ℚ_[l] ↥LL.1).map_sub, (algebraMap ℚ_[l] ↥LL.1).map_one]

theorem actVB_inclusion (P : LocPrime l) (K E LL : FinExt l) (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (g : ↥(GK E)) :
    actVB (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) g =
      actVB (P.PD K) T.ρ (Subgroup.inclusion (GK_le hle) g) := by
  unfold actVB
  congr 1
  ext b
  change (P.PD E).actB g b = (P.PD K).actB _ b
  rw [P.PD_actB, P.PD_actB]
  rfl

theorem iInf_ker_eq {R M ι κ : Type} [Ring R] [AddCommGroup M] [Module R M]
    (f : ι → M →ₗ[R] M) (g : κ → M →ₗ[R] M) (h1 : ∀ i, ∃ k, f i = g k) (h2 : ∀ k, ∃ i, f i = g k) :
    ⨅ i, LinearMap.ker (f i) = ⨅ k, LinearMap.ker (g k) := by
  apply le_antisymm
  · refine le_iInf fun k => ?_
    obtain ⟨i, hi⟩ := h2 k
    exact hi ▸ iInf_le _ i
  · refine le_iInf fun i => ?_
    obtain ⟨k, hk⟩ := h1 i
    exact hk ▸ iInf_le _ k

theorem Dcris_eq_iInf (P : LocPrime l) (K E LL : FinExt l) (hle : K.1 ≤ E.1)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (H : Subgroup ↥(GK K))
    (hH : ∀ x : ↥(GK K), x ∈ H ↔ (x : GQ l) ∈ GK E) :
    Dcris (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) =
      ⨅ g : ↥H, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) -
        (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B)) := by
  unfold Dcris
  apply iInf_ker_eq
  · intro g
    refine ⟨⟨Subgroup.inclusion (GK_le hle) g, (hH _).2 g.2⟩, ?_⟩
    exact congrArg (fun f => f - LinearMap.id) (actVB_inclusion P K E LL hle T g)
  · intro g
    refine ⟨⟨(g : ↥(GK K)), (hH _).1 g.2⟩, ?_⟩
    exact congrArg (fun f => f - LinearMap.id) (actVB_inclusion P K E LL hle T _)

set_option maxHeartbeats 1600000 in
theorem isCrys_Ks_of_finrank : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (n : ℕ) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), W.s = s → ∀ (E : FinExt l), E.1 = Ks K s → ∀ (hle : K.1 ≤ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), Module.finrank ↥LL.1 ↥(⨅ g : ↥W.GKs, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B))) = Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 T.V → IsCrys (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) := by
  intro l _ P K s LL n W hs E hE hle T h
  have hG : Gj K W.s = GK E := by
    rw [Gj, hs, ← hE]
    rfl
  have hD := Dcris_eq_iInf P K E LL hle T W.GKs (fun x => by
    rw [mem_GKs_iff_mem_Gj, hG])
  have h1 := finrank_maxUnramified_eq_cyclotomicLevel K E s (hs ▸ W.s_pos) hE hle
  have h2 := congrArg
    (fun D : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.B) => Module.finrank ↥LL.1 ↥D) hD
  rw [← h1] at h
  exact h2.trans h

end GlobalTheory.Cyc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariantsStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystalline_cyclotomicLevel_of_finrank_invariants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s : ℕ) (LL : FinExt l) (n : ℕ) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), W.s = s → ∀ (E : FinExt l), E.1 = Ks K s → ∀ (hle : K.1 ≤ E.1) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), Module.finrank ↥LL.1 ↥(⨅ g : ↥W.GKs, LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - (LinearMap.id : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.B))) = Module.finrank ℚ_[l] ↥(K0 K) * Module.finrank ↥LL.1 T.V → IsCrys (P.PD E) (T.ρ.comp (Subgroup.inclusion (GK_le hle))) := by
  first | exact @GlobalTheory.Cyc.isCrys_Ks_of_finrank | exact GlobalTheory.Cyc.isCrys_Ks_of_finrank | (intros; apply GlobalTheory.Cyc.isCrys_Ks_of_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.CocycleCount

theorem card_linear_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Module (ZMod N) A]
    [Finite A] : Finite (A →ₗ[ZMod N] ZMod N) ∧ Nat.card (A →ₗ[ZMod N] ZMod N) ≤ Nat.card A := by
  have h1 : Finite (A →ₗ[ZMod N] ZMod N) := DFunLike.finite _
  have h2 : Finite (A →+ ZMod N) := DFunLike.finite _
  refine ⟨h1, le_trans ?_ (GlobalTheory.natCard_addMonoidHom_zmod_le N A)⟩
  exact Nat.card_le_card_of_injective (fun f => f.toAddMonoidHom) LinearMap.toAddMonoidHom_injective

theorem card_H2_le (N : ℕ) [NeZero N] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) :
    Finite (ReciprocityTheory.Gal.H2 rho) ∧ Nat.card (ReciprocityTheory.Gal.H2 rho) ≤ Nat.card M := by
  have hT := card_linear_le N M
  have hTf : Finite (ReciprocityTheory.Gal.TDual (ZMod N) M) := hT.1
  have hTc : Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) ≤ Nat.card M := hT.2
  let A : Type := ReciprocityTheory.Gal.H0 ((ReciprocityTheory.Gal.twDual χ rho).comp (MonoidHom.id G))
  have hA := card_linear_le N A
  have hAc : Nat.card A ≤ Nat.card (ReciprocityTheory.Gal.TDual (ZMod N) M) :=
    Nat.card_le_card_of_injective _ Subtype.val_injective
  let E : ReciprocityTheory.Gal.H2 rho ≃ (A →ₗ[ZMod N] ZMod N) :=
    (Equiv.ofBijective _ hb).trans (LinearEquiv.congrRight e).toEquiv
  have := hA.1
  refine ⟨Finite.of_equiv _ E.symm, ?_⟩
  rw [Nat.card_congr E]
  exact hA.2.trans (hAc.trans hTc)

theorem card_cocycles_mul_invariants_discrete (R : Type) [CommRing R] (G : Type) [Group G] [TopologicalSpace G]
    (M : Type) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R G M) (hrho : ReciprocityTheory.Gal.ContAction rho) :
    Nat.card (ReciprocityTheory.Gal.Z1 rho) * Nat.card (ReciprocityTheory.Gal.H0 rho) =
      Nat.card (ReciprocityTheory.Gal.H1 rho) * Nat.card M := by
  have hle : ReciprocityTheory.Gal.B1 rho ≤ ReciprocityTheory.Gal.Z1 rho := by
    rintro _ ⟨m, rfl⟩
    refine ⟨?_, fun g h => ?_⟩
    · exact (hrho.comp (continuous_id.prodMk continuous_const)).sub continuous_const
    · simp only [ReciprocityTheory.Gal.amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have h1 := Submodule.card_eq_card_quotient_mul_card
    ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype)
  have h2 : Nat.card ((ReciprocityTheory.Gal.B1 rho).comap (ReciprocityTheory.Gal.Z1 rho).subtype) =
      Nat.card (ReciprocityTheory.Gal.B1 rho) := Nat.card_congr (Submodule.comapSubtypeEquivOfLe hle).toEquiv
  have hk : LinearMap.ker (ReciprocityTheory.Gal.d0 rho) = ReciprocityTheory.Gal.H0 rho := by
    ext m
    rw [LinearMap.mem_ker, ReciprocityTheory.Gal.mem_riemannRochSpace_iff_regularAt_everywhere, funext_iff]
    simp only [ReciprocityTheory.Gal.amitsur_d0_apply, Pi.zero_apply, sub_eq_zero]
  have h3 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (ReciprocityTheory.Gal.d0 rho))
  have h4 : Nat.card (M ⧸ LinearMap.ker (ReciprocityTheory.Gal.d0 rho)) = Nat.card (ReciprocityTheory.Gal.B1 rho) :=
    Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv
  rw [h4, hk] at h3
  rw [h1, h2, h3]
  ring

def repOfAction (N : ℕ) {G M : Type} [Monoid G] [AddCommGroup M] [Module (ZMod N) M]
    (a : G → M →+ M) (h1 : ∀ m, a 1 m = m) (hmul : ∀ g h m, a (g * h) m = a g (a h m)) :
    Representation (ZMod N) G M where
  toFun g := AddMonoidHom.toZModLinearMap N (a g)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hmul g h)

theorem count_of_euler (N : ℕ) [NeZero N] (G G' : Type) [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (φ : G' ≃* G) (hφ : Continuous φ ∧ Continuous φ.symm)
    (M : Type) [AddCommGroup M] [Module (ZMod N) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M] (χ : G →* (ZMod N)ˣ) (rho : Representation (ZMod N) G M)
    (hrho : ReciprocityTheory.Gal.ContAction rho)
    (e : ReciprocityTheory.Gal.H2 (ReciprocityTheory.Gal.charRep χ) ≃ₗ[ZMod N] ZMod N)
    (hb : Function.Bijective (ReciprocityTheory.Gal.cup20 χ rho (MonoidHom.id _))) (d : ℕ)
    (hEu : Nat.card (ReciprocityTheory.Gal.H1 rho) =
      Nat.card (ReciprocityTheory.Gal.H0 rho) * Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ d)
    (a : G' → M →+ M) (ha : ∀ g m, rho g m = a (φ.symm g) m) :
    {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧
      {c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤
        Nat.card M ^ (d + 2) := by
  obtain ⟨hf2, hc2⟩ := card_H2_le _ _ M _ rho e hb
  have hZ := card_cocycles_mul_invariants_discrete _ _ M rho hrho
  have h0 : 0 < Nat.card (ReciprocityTheory.Gal.H0 rho) := Nat.card_pos
  have h2 : 0 < Nat.card (ReciprocityTheory.Gal.H2 rho) := Nat.card_pos
  have hM : 0 < Nat.card M := Nat.card_pos
  have hZ' : Nat.card (ReciprocityTheory.Gal.Z1 rho) =
      Nat.card (ReciprocityTheory.Gal.H2 rho) * Nat.card M ^ (d + 1) := by
    apply Nat.eq_of_mul_eq_mul_right h0
    rw [hZ, hEu]
    ring
  let E : ↥{c : G' → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)} ≃
      ↥(ReciprocityTheory.Gal.Z1 rho) :=
    { toFun := fun c => ⟨fun g => c.1 (φ.symm g), c.2.1.continuous.comp hφ.2, fun g h => by
        beta_reduce
        rw [ha, map_mul, c.2.2]⟩
      invFun := fun c => ⟨fun g => c.1 (φ g),
        (IsLocallyConstant.iff_continuous _).2 (c.2.1.comp hφ.1), fun g h => by
          have := c.2.2 (φ g) (φ h)
          rw [ha, φ.symm_apply_apply, ← map_mul] at this
          exact this⟩
      left_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.symm_apply_apply g))
      right_inv := fun c => Subtype.ext (funext fun g => congrArg c.1 (φ.apply_symm_apply g)) }
  have hfin : Finite (ReciprocityTheory.Gal.Z1 rho) :=
    Nat.finite_of_card_ne_zero (by rw [hZ']; positivity)
  refine ⟨Set.finite_coe_iff.1 (Finite.of_equiv _ E.symm), ?_⟩
  rw [← Nat.card_coe_set_eq, Nat.card_congr E, hZ', pow_succ' _ (_ + 1)]
  exact Nat.mul_le_mul_right _ hc2

theorem cocycles_finite_ncard_le :
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (r : ℕ) (M : Type) [AddCommGroup M] [Finite M] (a : ↥(GK K) → M →+ M), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m : M, l ^ r • m = 0) → (∀ m, IsLocallyConstant fun g => a g m) → {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.Finite ∧ {c : ↥(GK K) → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)}.ncard ≤ Nat.card M ^ (Module.finrank ℚ_[l] ↥K.1 + 2) := by
  intro hT hE l _ K r M _ _ a h1 hmul hr hlc
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  have hr' : ∀ m : M, l ^ (r + 1) • m = 0 := fun m => by
    rw [pow_succ', mul_smul, hr, smul_zero]
  have _ : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let _ : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr'
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ (r + 1))) (Formalism.GaloisCohomology.GK l K.1) M :=
    repOfAction _ (fun g => a (φ.symm g)) (fun m => by rw [map_one, h1])
      (fun g h m => by rw [map_mul, hmul])
  have hrho : ReciprocityTheory.Gal.ContAction rho := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (hlc m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, -, hb⟩ := hT l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  have hEu := hE l K.1 hK (r + 1) M rho (Nat.succ_pos r) hrho
  exact count_of_euler _ _ _ φ hφ M _ rho hrho e hb _ hEu a fun _ _ => rfl

end GlobalTheory.CocycleCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
noncomputable section

namespace GlobalTheory.MirAvg

open Polynomial GlobalTheory.GLq

variable {g : ℕ} [Fact g.Prime]

def mirSet {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h : Gn g r) : Prop :=
  if b then ∀ x : Fin r → ZMod g, ∃ c : ZMod g, (h : Mt g r).mulVec x - x = c • a
  else ∀ x : Fin r → ZMod g, a ⬝ᵥ x = 0 → (h : Mt g r).mulVec x = x

open Classical in
def mirEl {r : ℕ} (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g) (b : Bool) : MonoidAlgebra ℂ (Gn g r) :=
  ∑ h : Gn g r, MonoidAlgebra.single h (if mirSet a b h then ((θ (Matrix.GeneralLinearGroup.det h) : ℂˣ) : ℂ) else 0)

def SeriesKillsAvg : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (r : ℕ) (f : (ZMod g)[X]) (θ : (ZMod g)ˣ →* ℂˣ) (c : ZMod g),
    GlobalTheory.GLp.IsCharLab L θ c → ¬ f.IsRoot c → ¬ f.IsRoot c⁻¹ → ∀ (a : Fin r → ZMod g) (b : Bool), a ≠ 0 →
      eSerC L r f * mirEl θ a b = 0

end GlobalTheory.MirAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.AwayT

theorem away_of_injective {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R)
    (hu : IsUnit (algebraMap R S t))
    (hs : ∀ b : S, ∃ (r : ℕ) (x : R), b * algebraMap R S t ^ r = algebraMap R S x)
    (hi : Function.Injective (algebraMap R S)) : IsLocalization.Away t S :=
  IsLocalization.Away.mk t hu hs fun _ _ h => ⟨0, by rw [hi h]⟩

theorem lift_injective {R P S : Type} [CommRing R] [CommRing P] [CommRing S] [Algebra R P] (x : R)
    [IsLocalization.Away x P] (f : R →+* S) (g : P →+* S) (hg : ∀ a, g (algebraMap R P a) = f a)
    (hf : Function.Injective f) : Function.Injective g := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj x z
  have h1 : f a = 0 := by rw [← hg, ← ha, map_mul, hz, zero_mul]
  have h2 : a = 0 := hf (h1.trans (map_zero f).symm)
  rw [h2, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit (S := P) x).pow n).mul_left_eq_zero.1 ha

variable {l : ℕ} [Fact l.Prime]

theorem plusInj (C : Core l) : C.PlusInj :=
  lift_injective ((l : ℕ) : Per.Acris l) C.j C.jP C.jP_alg (crisP_injective l C.j C.j_cris)

theorem plusToB_injective (C : Core l) : Function.Injective (plusToB l) := fun x y h =>
  plusInj C ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_plusToB, ← C.ι_plusToB, h]))

theorem acris_injective (C : Core l) : Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) :=
  fun x y h => crisP_injective l C.j C.j_cris
    ((BdRField.bdR_isField l).2.1 (by rw [← C.ι_j, ← C.ι_j, h]))

theorem awayT (C : Core l) : C.AwayT :=
  away_of_injective C.t (core_t_unit_fil l C).1 (GlobalTheory.T.bcris_eq_acris_localization_periodT l C) (acris_injective C)

theorem plusAwayT (C : Core l) : C.PlusAwayT := by
  letI := (plusToB l).toAlgebra
  have e : ∀ x : Per.Acris l, algebraMap (BcrisP l) (Per.Bcris l) (algebraMap _ _ x) =
      algebraMap (Per.Acris l) (Per.Bcris l) x := plusToB_alg
  refine away_of_injective _ ?_ (fun b => ?_) (plusToB_injective C)
  · rw [e]
    exact (core_t_unit_fil l C).1
  · obtain ⟨r, x, h⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
    exact ⟨r, algebraMap _ _ x, by rw [e, e]; exact h⟩

theorem away_and_inj (l : ℕ) [Fact l.Prime] (C : Core l) : C.AwayT ∧ C.PlusAwayT ∧ C.PlusInj :=
  ⟨awayT C, plusAwayT C, plusInj C⟩

end GlobalTheory.MemLoc.AwayT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocPrimeVNormalised
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.NormVal

section General

variable {K : Type*} [Field K]

end General

open GlobalTheory.Per.Val

private lemma addValuation_pow_mul_pow_div_pow {F : Type*} [Field F]
    (u : AddValuation F (WithTop ℚ)) {π : F} (hu : u π = 1) {x : F} {t : ℚ} (hx : u x = t)
    (b M N : ℕ) : u (x ^ b * π ^ M / π ^ N) = ((b * t + M - N : ℚ) : WithTop ℚ) := by
  rw [AddValuation.map_div, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_pow,
    AddValuation.map_pow, hx, hu]
  norm_cast
  simp [nsmul_eq_mul]

private lemma le_of_nonneg_imp_nonneg {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ)) {π : F}
    (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y → 0 ≤ w y) {x : F} {t s : ℚ}
    (hvx : v x = t) (hwx : w x = s) : t ≤ s := by
  have hMN : ((t.num.toNat : ℕ) : ℚ) - ((-t.num).toNat : ℕ) = t.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg t.num
  have hbt : (t.den : ℚ) * t = t.num := by rw [mul_comm]; exact Rat.mul_den_eq_num t
  have hy := h (x ^ t.den * π ^ (-t.num).toNat / π ^ t.num.toNat) (by
    rw [addValuation_pow_mul_pow_div_pow v hv hvx]
    exact_mod_cast (by linarith : (0 : ℚ) ≤ t.den * t + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ)))
  rw [addValuation_pow_mul_pow_div_pow w hw hwx] at hy
  have hy' : (0 : ℚ) ≤ t.den * s + ((-t.num).toNat : ℕ) - (t.num.toNat : ℕ) := by exact_mod_cast hy
  have hd : (0 : ℚ) < t.den := by exact_mod_cast t.den_pos
  nlinarith

private lemma addValuation_eq_of_nonneg_iff {F : Type*} [Field F] (v w : AddValuation F (WithTop ℚ))
    {π : F} (hv : v π = 1) (hw : w π = 1) (h : ∀ y, 0 ≤ v y ↔ 0 ≤ w y) (x : F) : v x = w x := by
  by_cases hx : x = 0
  · subst hx; simp
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff v).mp hx)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (mt (AddValuation.top_iff w).mp hx)
  rw [← ht, ← hs]
  have h1 := le_of_nonneg_imp_nonneg v w hv hw (fun y => (h y).mp) ht.symm hs.symm
  have h2 := le_of_nonneg_imp_nonneg w v hw hv (fun y => (h y).mpr) hs.symm ht.symm
  exact congrArg _ (le_antisymm h1 h2)

theorem _root_.GlobalTheory.HWL.NormVal.locPrime_v_normalised : ∀ (l : ℕ) [Fact l.Prime] (P : _root_.Formalism.BasicNotions.LocPrime l) (LL : _root_.Formalism.BasicNotions.Loc.FinExt l), (∀ (x : ↥LL.1) (q : ℚ), P.v LL x = (q : WithTop ℚ) ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ = (l : ℝ) ^ (-(q : ℝ))) ∧ (∀ (x : ↥LL.1) (q : ℚ), (q : WithTop ℚ) ≤ P.v LL x ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ (l : ℝ) ^ (-(q : ℝ))) ∧ ∀ x : ↥LL.1, x ∈ _root_.Formalism.BasicNotions.Loc.OL LL ↔ ‖(x : _root_.Formalism.BasicNotions.Loc.Om l)‖ ≤ 1 := by
  intro l _ P LL
  set w : AddValuation (↥LL.1) (WithTop ℚ) :=
    (_root_.GlobalTheory.Per.Val.vOm l).comap (algebraMap (↥LL.1) (_root_.Formalism.BasicNotions.Loc.Om l)) with hwdef
  have hwx : ∀ x : ↥LL.1, w x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x => rfl
  have hw : w (l : ↥LL.1) = 1 := by
    rw [hwx]
    have : ((l : ↥LL.1) : _root_.Formalism.BasicNotions.Loc.Om l) = (l : _root_.Formalism.BasicNotions.Loc.Om l) := by simp
    rw [this]
    exact _root_.GlobalTheory.Per.Val.vf_l
  have hnn : ∀ y : ↥LL.1, 0 ≤ P.v LL y ↔ 0 ≤ w y := by
    intro y
    rw [_root_.Formalism.BasicNotions.LocPrime.v_O, _root_.GlobalTheory.Per.Val.mem_OL_iff, hwx]
    have := _root_.GlobalTheory.Per.Val.le_vf_iff (y : _root_.Formalism.BasicNotions.Loc.Om l) 0
    simp only [Rat.cast_zero, neg_zero, Real.rpow_zero, WithTop.coe_zero] at this
    exact this.symm
  have key : ∀ x : ↥LL.1, P.v LL x = _root_.GlobalTheory.Per.Val.vf (x : _root_.Formalism.BasicNotions.Loc.Om l) := fun x =>
    (addValuation_eq_of_nonneg_iff (P.v LL) w (P.v_l LL) hw hnn x).trans (hwx x)
  refine ⟨fun x q => ?_, fun x q => ?_, fun x => _root_.GlobalTheory.Per.Val.mem_OL_iff LL x⟩
  · rw [key]; exact _root_.GlobalTheory.Per.Val.vf_eq_iff _ q
  · rw [key]; exact _root_.GlobalTheory.Per.Val.le_vf_iff _ q

end GlobalTheory.HWL.NormVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLattice
namespace GlobalTheory.ExpImage

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage GlobalTheory.MemLoc
open scoped Formalism.Per

theorem dvd_of_isHausdorff {R : Type} [CommRing R] (p : ℕ) (x a : R)
    (H : IsHausdorff (Ideal.span {(p : R ⧸ Ideal.span {x})}) (R ⧸ Ideal.span {x}))
    (h : ∀ n : ℕ, ∃ c : R, x ∣ a - (p : R) ^ n * c) : x ∣ a := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  refine H.haus _ fun n => ?_
  obtain ⟨c, hc⟩ := h n
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hc
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    hc, map_mul, map_pow, map_natCast]
  exact dvd_mul_right _ _

theorem mem_FilB_of_forall_Lat (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (T : LocTied l P AI) (M : ℕ) (b : P.R.BdR) (hb : ∀ n : ℕ, b ∈ Lat AI M n) :
    b ∈ FilB P (M : ℤ) := by
  obtain ⟨-, h2, -⟩ := GlobalTheory.T.deRham_fil_quotient_xi_power_ainf l P AI T (GlobalTheory.ThetaTie.thetaL T) M
  obtain ⟨-, h3⟩ := GlobalTheory.T.fontaineXi_pow_saturated_quotient_complete l AI.ε (GlobalTheory.ThetaTie.isEps AI) M
  obtain ⟨a₀, ha₀⟩ := hb 0
  rw [pow_zero, one_mul] at ha₀
  have hd : AI.ξ ^ M ∣ a₀ := by
    refine dvd_of_isHausdorff l _ _ h3.toIsHausdorff fun n => ?_
    obtain ⟨a, ha⟩ := hb n
    refine ⟨a, (h2 _).1 ?_⟩
    have := sub_mem ha ha₀
    rw [← io_apply, map_sub]
    convert this using 1
    ring
  have := add_mem ha₀ ((h2 a₀).2 hd)
  rwa [← io_apply, sub_add_cancel] at this

end GlobalTheory.ExpImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLatticeStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ) (b : P.R.BdR), (∀ n : ℕ, b ∈ Lat AI M n) → b ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.mem_FilB_of_forall_Lat | exact GlobalTheory.ExpImage.mem_FilB_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.mem_FilB_of_forall_Lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTower
noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem act_root_eq_pow_of_chi_nat {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (u : ℕ)
    (hg : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (m : ℕ) (ζ : Om l) (hζ : ζ ^ (l ^ m) = 1) :
    g ζ = ζ ^ u := by
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m ζ hζ
  rw [hg] at ha
  have h2 : ‖((((u : ℤ) - (a : ℤ) : ℤ)) : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    push_cast; exact ha
  have h3 : ((l : ℤ) ^ m) ∣ ((u : ℤ) - (a : ℤ)) := (Padic.norm_int_le_pow_iff_dvd _ _).mp h2
  have h4 : a ≡ u [MOD l ^ m] := by
    rw [Nat.modEq_iff_dvd]
    push_cast
    exact h3
  rw [hga, pow_eq_pow_mod a hζ, pow_eq_pow_mod u hζ, h4]

theorem actT_εroot_eq_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l)
    (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) →
      ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  intro l _ P AI g u hg j
  have hz : ∀ m, P.ζQ m ^ l ^ m = 1 := by
    intro m
    induction m with
    | zero => simpa using P.ζQ_zero
    | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  refine Perfection.ext fun n => ?_
  have hc : PreTilt.coeff n (AI.εroot j) =
      Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)}) (AI.ζ (n + j)) := by
    rw [← AI.ε_coeff, LocAinf.εroot, PreTilt.coeff_iterate_frobeniusEquiv_symm]
  obtain ⟨y', h1, h2⟩ := AI.actT_coeff g _ n _ hc
  have h3 : y' = AI.ζ (n + j) ^ u := by
    apply Subtype.ext
    rw [h1, SubmonoidClass.coe_pow, AI.ζ_eq, AI.actC_ext,
      act_root_eq_pow_of_chi_nat P g u hg (n + j) _ (hz _)]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  change PreTilt.coeff n _ = PreTilt.coeff n _
  rw [h2, map_pow, hc, h3]
  exact map_pow _ _ _

end GlobalTheory.ExpImage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicActionOnRootTowerStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomic_action_on_root_tower : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (g : GQ l) (u : ℕ), (P.χQ g : ℚ_[l]) = (u : ℚ_[l]) → ∀ j : ℕ, AI.actT g (AI.εroot j) = AI.εroot j ^ u := by
  first | exact @GlobalTheory.ExpImage.actT_εroot_eq_pow | exact GlobalTheory.ExpImage.actT_εroot_eq_pow | (intros; apply GlobalTheory.ExpImage.actT_εroot_eq_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfect
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfect
open scoped NNReal
open Ideal Finset GlobalTheory.Per.AinfComplete

namespace GlobalTheory.WittTeichComplete

private lemma tails_of_isAdicComplete_span {A : Type*} [CommRing A] (y : A)
    [IsAdicComplete (Ideal.span {y}) A] : _root_.GlobalTheory.Per.AinfComplete.Tails y := by
  have hsum := _root_.GlobalTheory.Per.AinfComplete.summ_of_precomplete y
  unfold _root_.GlobalTheory.Per.AinfComplete.Summ at hsum
  unfold _root_.GlobalTheory.Per.AinfComplete.Tails
  intro b
  choose L hL using fun n => hsum (fun k => b (n + k))
  refine ⟨L, fun n => ?_⟩
  have key : ∀ m, y ^ m ∣ L n - y * L (n + 1) - b n := by
    intro m
    have h₁ := Ideal.mem_span_singleton.1 (hL n (m + 1))
    have h₂ := Ideal.mem_span_singleton.1 (hL (n + 1) m)
    have hs : ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i) =
        b n + y * ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
      simp only [pow_zero, one_mul, add_zero]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ, show n + (i + 1) = n + 1 + i by omega]
      ring
    have hd : L n - y * L (n + 1) - b n =
        (L n - ∑ i ∈ Finset.range (m + 1), y ^ i * b (n + i)) -
          y * (L (n + 1) - ∑ i ∈ Finset.range m, y ^ i * b (n + 1 + i)) := by
      rw [hs]; ring
    rw [hd]
    exact dvd_sub ((pow_dvd_pow y (Nat.le_succ m)).trans h₁) (dvd_mul_of_dvd_right h₂ y)
  have h0 := _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus y _ fun m => Ideal.mem_span_singleton.2 (key m)
  exact (sub_eq_zero.1 h0).symm

theorem _root_.GlobalTheory.WittTeichComplete.main : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l]
    [PerfectRing O l] (x : O), x ≠ 0 → IsAdicComplete (Ideal.span {x}) O →
    IsAdicComplete (Ideal.span {WittVector.teichmuller l x}) (WittVector l O) ∧
      IsAdicComplete (Ideal.span {((l : ℕ) : WittVector l O)} ⊔
        Ideal.span {WittVector.teichmuller l x}) (WittVector l O) := by
  intro l _ O _ _ _ _ x _ hc
  haveI := hc
  have hcc : WittVector.constantCoeff (WittVector.teichmuller l x) = x := by
    simp [WittVector.constantCoeff]
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.Per.AinfComplete.witt_complete (WittVector.teichmuller l x)
    (hcc ▸ tails_of_isAdicComplete_span x) (fun r hr => _root_.GlobalTheory.Per.AinfComplete.eq_zero_of_haus x r
      fun n => Ideal.mem_span_singleton.2 (hcc ▸ hr n))
  refine ⟨h₂, ?_⟩
  rwa [Ideal.span_insert] at h₁

end GlobalTheory.WittTeichComplete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorTeichmullerIsAdicCompleteOfPerfectStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (x : O), x ≠ 0 → IsAdicComplete (Ideal.span {x}) O → IsAdicComplete (Ideal.span {WittVector.teichmuller l x}) (WittVector l O) ∧ IsAdicComplete (Ideal.span {((l : ℕ) : WittVector l O)} ⊔ Ideal.span {WittVector.teichmuller l x}) (WittVector l O) := by
  first | exact @GlobalTheory.WittTeichComplete.main | exact GlobalTheory.WittTeichComplete.main | (intros; apply GlobalTheory.WittTeichComplete.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariant
noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem tmul_gen_cancel (hO : Function.Injective (algebraMap O LL)) (T : LocLat G Qp LL O)
    (e : T.V) (he : e ≠ 0) (heT : e ∈ T.L.T) (e₀ : ↥T.L.T) (h₀ : Submodule.span O {e₀} = ⊤)
    {R : Type} [CommRing R] [Algebra O R] (r r' : R)
    (h : (r ⊗ₜ[O] e₀ : TW R T) = r' ⊗ₜ[O] e₀) : r = r' := by
  have hne : (e₀ : T.V) ≠ 0 := by
    intro h0
    have hm : (⟨e, heT⟩ : ↥T.L.T) ∈ Submodule.span O {e₀} := by rw [h₀]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    apply he
    have := congrArg Subtype.val hc
    simp only [Submodule.coe_smul, h0, smul_zero] at this
    exact this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O ↥T.L.T e₀) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro c hc
      have h1 : c • (e₀ : T.V) = 0 := congrArg Subtype.val hc
      rw [← algebraMap_smul LL c, smul_eq_zero] at h1
      rcases h1 with h1 | h1
      · exact hO (by rw [h1, map_zero])
      · exact absurd h1 hne
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h₀]
  let φ := LinearEquiv.ofBijective _ hb
  have hφ : φ.symm e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    simp [φ]
  have := congrArg (fun z => TensorProduct.rid O R (LinearMap.lTensor R φ.symm.toLinearMap z)) h
  simpa [hφ] using this

theorem etTie_io_act (hO : Function.Injective (algebraMap O LL)) {W : LocWach PD LL O v n}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {incl : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW incl φR gR πA) (g : G) (a : LetA O n) :
    incl (E.io (W.γA (W.resΓ g) a)) = gR g (incl (E.io a)) := by
  obtain ⟨e, e₀, h₀, hj, -⟩ := E.one_e
  obtain ⟨e₁, he₁, hT⟩ := W.one_line
  have he₁T : e₁ ∈ W.one.L.T := by rw [hT]; exact Submodule.mem_span_singleton_self e₁
  have hact : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g e₀)
  have h1 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by
    simp [TWact, hact]
  have h2 := E.jD_act W.one g (algebraMap (LetA O n) W.EE a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, hj, TWact_smul, h1, W.γE_ext, E.ioE_ext,
    E.ioE_ext, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at h2
  exact tmul_gen_cancel hO W.one e₁ he₁ he₁T e₀ h₀ _ _ h2

end Generic

set_option synthInstance.maxHeartbeats 400000 in
theorem io_equivariant : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  intro l _ P AI K s LL h W E g a
  exact etTie_io_act Subtype.val_injective E.tie g a

end GlobalTheory.Cyc.Decomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoEquivariantStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.io_equivariant_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))) (E : EtSit P AI K s LL h W) (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), inclR LL (E.tie.io (W.γA (W.resΓ g) a)) = AI.gRW LL (g : GQ l) (inclR LL (E.tie.io a)) := by
  first | exact @GlobalTheory.Cyc.Decomp.io_equivariant | exact GlobalTheory.Cyc.Decomp.io_equivariant | (intros; apply GlobalTheory.Cyc.Decomp.io_equivariant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEll
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEll
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.CycUnram

theorem main : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  intro D i v hv γ hγ
  have hl : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by simpa [placesOver] using hv
  have h1 : cycZ D.host.E D.nd.Om (D.nd.l i) γ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hl (D.nd.plOm.2 v) (q := 1) (fun x hx => by simpa using hγ.2 x hx) n]
    simp
  have h2 : epsU D.nd i γ = 1 := by
    unfold epsU Glob.epsO
    rw [MonoidHom.comp_apply, h1, map_one]
  refine ⟨h2, fun c hc1 hc2 => ?_⟩
  change D.nd.chi i c γ = D.nd.chi i 1 γ
  rw [D.nd.chi_def i c hc1 hc2, MonoidHom.mul_apply, MonoidHom.zpow_apply, MonoidHom.comp_apply, h1, map_one,
    one_zpow, mul_one]

end GlobalTheory.CycUnram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharUnramifiedAwayFromEllStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclotomicChar_unramified_away_from_ell : ∀ (D : D7) (i : D.nd.Loc) (v : HeightOneSpectrum (𝓞 D.host.E)), v ∉ placesOver D.host.E (D.nd.l i) → ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), epsU D.nd i γ = 1 ∧ ∀ c, 1 ≤ c → c ≤ D.R.t → chiU D.nd i c γ = chiU D.nd i 1 γ := by
  first | exact @GlobalTheory.CycUnram.main | exact GlobalTheory.CycUnram.main | (intros; apply GlobalTheory.CycUnram.main <;> assumption)
end
end
