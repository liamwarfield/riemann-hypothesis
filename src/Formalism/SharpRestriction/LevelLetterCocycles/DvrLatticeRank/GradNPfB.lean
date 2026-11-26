module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.DvdCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.ModelKStep
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrobPiNPf

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfB
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem gradNPf_cc_γ₀ (g : W.Gam) (a : PowerSeries O) :
    PowerSeries.constantCoeff (W.γ₀ g a) = PowerSeries.constantCoeff a := by
  exact Formalism.MainNotions.LiftingTheory.constantCoeff_gamma W g a

theorem gradNPf_γA_comm (g h : W.Gam) (a : LetA O n) :
    W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  exact Formalism.MainNotions.LiftingTheory.frame_γA_comm W g h a

theorem gradNPf_cc_f (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hf : W.γA W.gam π' = π' * f) (i : ZMod n) :
    PowerSeries.constantCoeff (f i) = ((W.χΓ W.gam : Oˣ) : O) ^ s' := by
  have hi := congrFun hf i
  have hγi : (W.γA W.gam π') i = W.γ₀ W.gam (π' i) := rfl
  have hπi : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
  have hX : W.γ₀ W.gam PowerSeries.X = PowerSeries.X *
      PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X)) := by
    conv_lhs => rw [PowerSeries.eq_X_mul_shift_add_const (W.γ₀ W.gam PowerSeries.X)]
    rw [(W.γ₀_X W.gam).1, map_zero, add_zero]
  have hh : PowerSeries.constantCoeff (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1)
      (W.γ₀ W.gam PowerSeries.X))) = ((W.χΓ W.gam : Oˣ) : O) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (W.γ₀_X W.gam).2
  rw [hγi, Pi.mul_apply, hπi, map_mul, map_pow, hX, mul_pow] at hi
  have h2 : PowerSeries.X ^ s' * (W.γ₀ W.gam ((w : LetA O n) i) *
      (PowerSeries.mk (fun p => PowerSeries.coeff (p + 1) (W.γ₀ W.gam PowerSeries.X))) ^ s') =
      PowerSeries.X ^ s' * ((w : LetA O n) i * f i) := by
    linear_combination hi
  have h3 := congrArg PowerSeries.constantCoeff (PowerSeries.X_pow_mul_cancel h2)
  rw [map_mul, map_mul, map_pow, hh, gradNPf_cc_γ₀] at h3
  have hwu : IsUnit (PowerSeries.constantCoeff ((w : LetA O n) i)) :=
    (w.isUnit.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)).map PowerSeries.constantCoeff
  exact (hwu.mul_left_cancel h3).symm

theorem gradNPf_fΔ (s' : ℕ) (w : (LetA O n)ˣ) (π' f : LetA O n)
    (hw : π' = (w : LetA O n) * letπ ^ s') (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hf : W.γA W.gam π' = π' * f) : ∀ δ ∈ W.DelF, W.γA δ f = f := by
  intro δ hδ
  have hu : IsUnit (algebraMap (LetA O n) W.EE π') := by
    rw [hw, map_mul, map_pow]
    have hl : IsUnit (algebraMap (LetA O n) W.EE letπ) := by simpa using Formalism.MainNotions.LiftingTheory.wmap_unit W 0
    exact (w.isUnit.map _).mul (hl.pow _)
  apply Formalism.MainNotions.LiftingTheory.lifta_reg W π' _ _ hu
  have h1 : W.γA δ (W.γA W.gam π') = W.γA W.gam π' := by
    rw [Formalism.MainNotions.LiftingTheory.frame_γA_comm, hπΔ δ hδ]
  rw [hf, map_mul, hπΔ δ hδ] at h1
  exact h1

theorem gradNPf_expand (π' a : LetA O n) (hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0)
    (F : ZMod n → PowerSeries O) (hF : ∀ i, a i = PowerSeries.subst (π' i) (F i))
    (c₀ : O) (hc : ∀ i, PowerSeries.constantCoeff (a i) = c₀) :
    ∃ t : LetA O n, a - algebraMap O (LetA O n) c₀ = π' * t := by
  have hS : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i)
  refine ⟨fun i => PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)), ?_⟩
  funext i
  have e1 : a i = π' i * PowerSeries.subst (π' i)
      (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i)) +
      PowerSeries.C (PowerSeries.constantCoeff (F i)) := by
    conv_lhs => rw [hF i, PowerSeries.eq_X_mul_shift_add_const (F i)]
    rw [PowerSeries.subst_add (hS i), PowerSeries.subst_mul (hS i), PowerSeries.subst_X (hS i),
      PowerSeries.subst_C]
    rfl
  have e3 : PowerSeries.constantCoeff (F i) = c₀ := by
    have := congrArg PowerSeries.constantCoeff e1
    rw [hc i, map_add (f := _), map_mul, hπ0 i, zero_mul, zero_add, PowerSeries.constantCoeff_C] at this
    exact this.symm
  rw [e3] at e1
  have hC : algebraMap O (PowerSeries O) c₀ = PowerSeries.C c₀ := by
    rw [PowerSeries.algebraMap_apply]
    rfl
  show a i - algebraMap O (PowerSeries O) c₀ = π' i * PowerSeries.subst (π' i)
    (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (F i))
  rw [hC, e1]
  ring

theorem exists_gam_pi_factor (T : LocLat G Qp LL O) (e s' : ℕ) (hs : 1 ≤ s') (π' : LetA O n)
    (E : ZMod n → Polynomial O) (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' E) (π'₀ : LetA O n)
    (w₀ : (LetA O n)ˣ) (hw₀ : π'₀ = (w₀ : LetA O n) * letπ ^ s')
    (hm : ∀ y ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T y - y = π'₀ • x') :
    ∃ f t : LetA O n, W.γA W.gam π' = π' * f ∧
      f - algebraMap O (LetA O n) (((W.χΓ W.gam : Oˣ) : O) ^ s') = π' * t ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧ (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  have hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π' := fun δ hδ => hR.1 δ hδ
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.2.2.1
  obtain ⟨f, hfdef⟩ : ∃ f : LetA O n, f = 1 + (w' : LetA O n) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := ⟨_, rfl⟩
  have hf : W.γA W.gam π' = π' * f := by
    rw [hfdef]
    linear_combination hw'
  have hfΔ := gradNPf_fΔ W s' w π' f hw hπΔ hf
  obtain ⟨Fs, hFs, -⟩ := hR.2.1 f hfΔ
  have hπ0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := by
    intro i
    have : π' i = (w : LetA O n) i * PowerSeries.X ^ s' := by rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Fs hFs _ (gradNPf_cc_f W s' w π' f hw hf)
  refine ⟨f, t, hf, ht, ?_, hπΔ, ?_⟩
  · rw [hw, map_mul, map_pow]
    exact (w.isUnit.map _).mul (W.EE_π.pow _)
  · intro y hy
    obtain ⟨x', hx', hxe⟩ := hm y hy
    refine ⟨((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) • x', (W.N T).smul_mem _ hx'.1, ?_⟩
    have hπ₀ : π'₀ = ((w₀ : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n)) * π' := by
      rw [hw₀, hw, mul_assoc, ← mul_assoc ((w⁻¹ : (LetA O n)ˣ) : LetA O n), Units.inv_mul, one_mul]
    rw [smul_smul, mul_comm π', ← hπ₀]
    exact hxe

end Local


set_option maxHeartbeats 1000000 in
theorem gradNPf_hyps (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [hpf : Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (hs : 1 ≤ sK l K) :
    ∃ (f t : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x u : ↥(OL LL)),
      IsUnit u ∧ x - 1 = (l : ↥(OL LL)) * u ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * f ∧
      f - algebraMap ↥(OL LL) (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (x ^ sK l K) = π' * t ∧
      IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
      (∀ δ ∈ ((HW l).W K 1 LL hG).DelF, ((HW l).W K 1 LL hG).γA δ π' = π') ∧
      (∀ y ∈ ((HW l).W K 1 LL hG).NΔ T, ∃ d ∈ ((HW l).W K 1 LL hG).N T,
        ((HW l).W K 1 LL hG).γD T ((HW l).W K 1 LL hG).gam y - y = π' • d) ∧
      ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
      ∀ N : ℕ, ∃ a : ↥(OL LL), (l : ↥(OL LL)) ^ (N + padicValNat l N.factorial) =
        a * ∏ y ∈ Finset.Ico 1 (N + 1), ((x ^ sK l K) ^ y - 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, h9W, -⟩ := h1 l K 1 LL hG
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs1 : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, ⟨π'₀, E₀, hr₀, hm₀⟩, -⟩ := h9W T hT hs1 hp
  rw [hpl] at hr₀
  obtain ⟨w₀, hw₀⟩ := hr₀.2.2.1
  obtain ⟨f, t, hf, ht, hEE, hπΔ, hγN⟩ :=
    exists_gam_pi_factor _ T (eK K) (sK l K) hs π' E hR π'₀ w₀ hw₀ hm₀.2
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hRv : ∀ y : ↥LL.1, 0 ≤ (D.loc l).v LL y ↔ ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a = y := by
    intro y
    rw [(D.loc l).v_O LL y]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨a, ha⟩ => ha ▸ a.2⟩
  have hlv : (D.loc l).v LL (l : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hlO : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL))) = 1 := by
    rw [map_natCast]
    exact hlv
  have hxv : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) - 1) = 1 := by
    have := ((HW l).W K 1 LL hG).gam_gen
    rw [hs1, Nat.cast_one] at this
    exact this
  obtain ⟨u, hu, hxu⟩ := gradNPf_sub_one ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv
    (l : ↥(OL LL)) _ hlO hxv
  have hsl : ¬ l ∣ sK l K := by
    apply Nat.not_dvd_of_pos_of_lt hs
    have h2 := hpf.out.two_le
    exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  exact ⟨f, t, (((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ), u, hu, hxu, hf, ht, hEE, hπΔ, hγN,
    ((HW l).W K 1 LL hG).gamK_eq_one hs1 hp,
    fun N => gradNPf_prod ((D.loc l).v LL) (algebraMap ↥(OL LL) ↥LL.1) hι hRv l hl hlv _ u hu hxu
      (sK l K) (by omega) hsl N⟩

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.U3upPfFilCAnti
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem u3upPf_FilC_anti (T : LocLat G Qp LL O) (τ : K →ₐ[Qp] LL) {a a' : ℤ} (h : a' ≤ a) :
    Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a ≤ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ a' := by
  have hs : ∀ k : ℤ, FildR PD T.ρ τ (k + 1) ≤ FildR PD T.ρ τ k := by
    intro k
    refine inf_le_inf_left _ ?_
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul u w => exact ⟨u ⊗ₜ ⟨(w : BdR), PD.Fil_anti k w.2⟩, rfl⟩
    | add z z' hz hz' => rw [map_add (f := _)]; exact Submodule.add_mem _ hz hz'
  have hA : Antitone fun k => FildR PD T.ρ τ k := antitone_int_of_succ_le hs
  unfold Formalism.MainNotions.DeltaInvariantLattices.FilC
  exact sup_le_sup_right (hA h) _

theorem u3upPf_memNL (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' S : ℕ) (up : (K →ₐ[Qp] LL) → Bool) (b : (K →ₐ[Qp] LL) → ℕ) (c : ZMod n)
    (hPt : ∀ ζ τ, Pt c ζ τ → Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c)
    (hup : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true) (f : W.EE)
    (hf : IsCoord W Pt π' Eπ h' S up b c f) (x : W.DD T) (hx : x ∈ NcS W T (c - 1))
    (hFil : ∀ τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true → x ∈ FilL W T Pt c τ (b τ)) :
    f ⊗ₜ mkL W T π' c x hx ∈ NL W T Pt π' Eπ h' c := by
  obtain ⟨a, ha, hea, hΛ, hup0, -, -⟩ := hf
  apply Submodule.subset_span
  refine ⟨1, fun _ => ⟨a, ha⟩, fun _ => x, ⟨fun _ => hx, ?_⟩, ?_⟩
  · rw [Fin.sum_univ_one]
    show TensorProduct.map (LinearMap.mulLeft O (algebraMap (LetA O n) W.EE (Eπ ^ h'))) LinearMap.id
        (f ⊗ₜ mkL W T π' c x hx) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ mkL W T π' c x hx
    rw [TensorProduct.map_tmul, LinearMap.mulLeft_apply, LinearMap.id_apply, hΛ, hea]
  · intro τ ζ hpt i
    have hO := hPt ζ τ hpt
    have hu := hup τ hO
    have hv : valAt W T c ζ x ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (b τ) := hFil τ hO hu ζ hpt
    show (∑ j : Fin 1, serC (W.lev c ζ a) (valAt W T c ζ x) i) ∈ _
    rw [Fin.sum_univ_one]
    unfold serC
    split_ifs with hi
    · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      simp only [Int.toNat_natCast]
      by_cases hlt : k + b τ < h'
      · rw [hup0 τ ζ hpt hu k hlt, zero_smul]
        exact Submodule.zero_mem _
      · apply Submodule.smul_mem
        refine u3upPf_FilC_anti T τ ?_ hv
        push_neg at hlt
        omega
    · exact Submodule.zero_mem _

theorem u3upPf_PiNS_one (T : LocLat G Qp LL O) (π' : LetA O n) {M : ℕ} (hM : 1 ≤ M) {z : W.DD T}
    (hz : z ∈ PiNS W T π' M) : z ∈ PiNS W T π' 1 := by
  obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
  refine Submodule.mem_inf.2 ⟨?_, hz2⟩
  rw [Submodule.restrictScalars_mem] at hz1 ⊢
  unfold Formalism.MainNotions.DeltaInvariantLattices.aN at hz1 ⊢
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz1
  refine Submodule.mem_map.2 ⟨π' ^ (M - 1) • w, (W.N T).smul_mem _ hw, ?_⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hM]

theorem u3upPf_lift {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' M ρ : ℕ) (c : ZMod n)
    (α : FrA W π' Eπ h' M c) (β : FrB W π' Eπ h' M c)
    (hMF : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M) (hW : WKill W F ρ)
    (hNL : NinLam W T₁ Eπ h') (hG1 : GamPi W T₁ π') (hG2 : GamPi W T₂ π')
    (x : LA W T₂ π' c) (hx : x ∈ LamLA W T₂ π' Eπ h' c ⊤) (hxN : x ∈ NL W T₂ Pt π' Eπ h' c)
    (y : W.DD T₂) (hy : y ∈ LamPS W T₂ Eπ h' c)
    (hα : α T₂ ⟨x, hx⟩ = mkP W T₂ π' Eπ h' M c y hy) : LiftsBy W F π' Eπ h' ρ c y := by
  obtain ⟨n₂, hn₂, hn₂N, hα₂⟩ := hMF.1 x hx hxN
  have hd : y - n₂ ∈ PiNS W T₂ π' M := by
    refine (hMF.2.2.1 M hM le_rfl).1 0 (Submodule.zero_mem _) (y - n₂)
      (Submodule.sub_mem _ hy hn₂) ?_ (Submodule.zero_mem _)
    have h0 : (⟨0, Submodule.zero_mem _⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) = 0 := rfl
    rw [h0, map_zero]
    symm
    show Submodule.Quotient.mk ((⟨y, hy⟩ : ↥(LamPS W T₂ Eπ h' c)) - ⟨n₂, hn₂⟩) =
      (0 : QLamP W T₂ π' Eπ h' M c)
    rw [Submodule.Quotient.mk_sub, sub_eq_zero]
    exact hα.symm.trans hα₂
  have hyN : y ∈ NcS W T₂ c := by
    obtain ⟨-, hΔ, hl⟩ := (mem_LamPS W T₂ Eπ h' c y).1 hy
    refine (mem_NcS W T₂ c y).2 ⟨?_, hΔ, hl⟩
    have h1 := PiNS_le_N W T₂ π' M hd
    have h2 := ((mem_NcS W T₂ c n₂).1 hn₂N).1
    have h3 := Submodule.add_mem _ h1 h2
    rwa [sub_add_cancel] at h3
  obtain ⟨n₁, hn₁, hF⟩ := hW c n₂ hn₂N
  refine ⟨(mem_InvS W T₂ π' Eπ h' 1 c y).2 ⟨hy, (Submodule.mem_inf.1 (hG2 c y hyN)).1⟩, n₁,
    (mem_InvS W T₁ π' Eπ h' 1 c n₁).2 ⟨hNL c hn₁, (Submodule.mem_inf.1 (hG1 c n₁ hn₁)).1⟩, ?_⟩
  rw [hF, ← smul_sub]
  exact Submodule.smul_mem _ _ (u3upPf_PiNS_one W T₂ π' hM hd)

end Local

theorem u3upPf_pt_over (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] {K LL : FinExt l}
    (hG : Good K 1 LL) (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) : Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c := by
  obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hpt
  apply AlgHom.ext
  intro z
  have hzK : (z : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) z.2
  rw [AlgHom.comp_apply, hres (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1 z) ⟨z, hzK⟩ rfl]
  exact hemb z ⟨z, hzK⟩ rfl

theorem u3upPf_MK_pos {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL) (h' : ℕ)
    (hh' : 1 ≤ h') : 1 ≤ MK l K h' := by
  have hs := frobpin_sK_pos hl K LL hG
  have h4 : (0 : ℝ) < 4 * (h' : ℝ) := by
    have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
    linarith
  have hs' : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs
  exact Nat.ceil_pos.2 (div_pos h4 hs')

theorem u3upPf_ofR (D : D7) (HW : HWOf D.loc) (hMF : modelFR D HW) (hW : wKillR D HW)
    (hNL : ninLamR D HW) (hGP : gamPiR D HW) : UpSlotProposition D HW := by
  intro l _ hl K LL hG π' E hπ T₁ T₂ F S η m h' up b c α β hfr hN hall
  intro f hf x hx hFil h1 y hy hα
  obtain ⟨hc1, hc2, hon, hj1, hj2, hηb, hbS, hh', -, -⟩ := hN
  have hjI : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)),
      (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) →
      ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro T hj τ a ha
    have hd := hj τ a ha
    have hb := hbS τ
    have hη := hηb τ
    rw [Set.mem_Icc]
    rcases hd with hd | hd
    · unfold deep at hd
      split_ifs at hd <;> (rw [Set.mem_Icc] at hd; constructor <;> omega)
    · rw [Set.mem_Icc] at hd
      constructor <;> omega
  have hM := u3upPf_MK_pos hl K LL hG h' hh'
  have hMF2 := hMF l hl K LL hG π' E hπ h' hh' c α β hfr T₂ hc2 (hjI T₂ hj2)
  have hW' := hW l hl K LL hG π' E hπ T₁ T₂ F h' hc1 hc2 hon (hjI T₁ hj1)
  have hNL1 := hNL l hl K LL hG π' E hπ T₁ h' hc1 (hjI T₁ hj1)
  have hG1 := hGP l hl K LL hG π' E hπ T₁ hc1
  have hG2 := hGP l hl K LL hG π' E hπ T₂ hc2
  have hxN := u3upPf_memNL _ T₂ _ π' _ h' S up b c (fun ζ τ hpt => u3upPf_pt_over D HW hG c ζ τ hpt)
    hall f hf x hx hFil
  exact u3upPf_lift _ F _ π' _ h' _ _ c α β hMF2 hM hW' hNL1 hG1 hG2 _ h1 hxN y hy hα

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLoc
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Coeff

variable {R : Type} [CommRing R]

theorem framepf_coeff_pow_lt (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m j : ℕ)
    (hj : j < m) : PowerSeries.coeff j (f ^ m) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

theorem framepf_coeff_pow_self (f : PowerSeries R) (hf : PowerSeries.constantCoeff f = 0) (m : ℕ) :
    PowerSeries.coeff m (f ^ m) = PowerSeries.coeff 1 f ^ m := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [mul_pow, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, PowerSeries.coeff_succ_X_mul,
    PowerSeries.coeff_zero_eq_constantCoeff_apply]

end Coeff

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

theorem framepf_ιV_inj : Function.Injective (ιV PD (LL := LL) (V := T.V)) := by
  have h : ∀ y, ιV PD (LL := LL) (V := T.V) y =
      ((PD.ι.toLinearMap.restrictScalars Qp).lTensor T.V) y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [ιV]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective (PD.ι.toLinearMap.restrictScalars Qp) := PD.ι_inj
  intro a b hab
  rw [h, h] at hab
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hi hab

theorem framepf_levB_gam (hc : IsCrys PD T.ρ) (g : W.Gam)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ g : O) - 1)) (i : ZMod n) (x : ↥(W.N T))
    (hx : W.γD T g (x : W.DD T) ∈ W.N T) (k : ℤ) :
    Ct.levB T i 1 ⟨W.γD T g (x : W.DD T), hx⟩ k = (algebraMap O LL (W.χΓ g : O)) ^ k • Ct.levB T i 1 x k :=
  Ct.levB_Γ T hc g i 1 1 0 1 (by simpa using IsPrimitiveRoot.one) (by simpa using hv) (by simp) x hx k

theorem framepf_levB_zero (hc : IsCrys PD T.ρ) (i : ZMod n)
    (hv : (0 : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - 1))
    (hχ : ∀ r : ℤ, 1 ≤ r → (algebraMap O LL (W.χΓ W.gam : O)) ^ r ≠ 1)
    (a : LetA O n) (R : ℕ) (ha : ∀ j < R, PowerSeries.coeff j (W.lev i 1 a) = 0)
    (x w : ↥(W.N T)) (hxw : W.γD T W.gam (x : W.DD T) - x = a • (w : W.DD T))
    (hw : ∀ r : ℤ, r < 0 → W.levN T i 1 w r = 0) (r : ℤ) (h1 : 1 ≤ r) (hR : r < R) :
    Ct.levB T i 1 x r = 0 := by
  have hx : W.γD T W.gam (x : W.DD T) ∈ W.N T := W.N_Γ T W.gam x x.2
  have haw : a • (w : W.DD T) ∈ W.N T := (W.N T).smul_mem a w.2
  have hsub : (⟨_, hx⟩ : ↥(W.N T)) - x = ⟨_, haw⟩ := Subtype.ext (by simp [hxw])
  have hlev := congrArg (fun y => Ct.levB T i 1 y r) hsub
  simp only [map_sub, Pi.sub_apply] at hlev
  rw [framepf_levB_gam Ct T hc W.gam hv i x hx r] at hlev
  have hzero : Ct.levB T i 1 ⟨_, haw⟩ r = 0 := by
    refine framepf_ιV_inj (PD := PD) T ?_
    rw [map_zero, ← Ct.levN_eq]
    have : (⟨_, haw⟩ : ↥(W.N T)) = a • w := rfl
    rw [this, W.levN_smul]
    apply finsum_eq_zero_of_forall_eq_zero
    intro j
    by_cases hj : j < R
    · rw [ha j hj, zero_smul]
    · simp only [hw (r - (j : ℤ)) (by omega), smul_zero]
  rw [hzero] at hlev
  have h2 : ((algebraMap O LL (W.χΓ W.gam : O)) ^ r - 1) • Ct.levB T i 1 x r = 0 := by
    rw [sub_smul, one_smul]; exact hlev
  exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (hχ r h1))

theorem framepf_levB_phi (hc : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hQ : ∀ j < m, PowerSeries.coeff j (W.lev i ζ (W.Q ^ m)) = 0)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (i - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (i - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    Ct.levB T i ζ ⟨_, hm⟩ k =
      serC (W.lev i ζ (W.Q ^ m)) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (i - 1) 1 x 0)) k := by
  rw [Ct.levB_φ T hc i ζ hζ x m hm k, hζ1]
  unfold serC
  split_ifs with hk0
  · rw [finsum_eq_single _ k.toNat]
    · have : k - (k.toNat : ℤ) = 0 := by omega
      rw [this, zpow_zero, one_smul]
    · intro j hj
      by_cases hjm : j < m
      · rw [hQ j hjm, zero_smul]
      · by_cases hjk : (j : ℤ) < k
        · rw [hmid (k - (j : ℤ)) (by omega) (by omega), map_zero, smul_zero, smul_zero]
        · have : (j : ℤ) ≠ k := fun h => hj (by omega)
          rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]
  · apply finsum_eq_zero_of_forall_eq_zero
    intro j
    rw [hneg (k - (j : ℤ)) (by omega), map_zero, smul_zero, smul_zero]

theorem framepf_valAt (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hex : ∃ k : ℕ, W.Q ^ k • W.φD T (x : W.DD T) ∈ W.N T) :
    valAt W T c ζ (x : W.DD T) = ιV PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Ct.levB T (c - 1) 1 x 0)) := by
  classical
  unfold valAt
  rw [dite_eq_left hex]
  have hm := Nat.find_spec hex
  have hC := framepf_levB_phi Ct T hc c ζ hζ hζ1 x (Nat.find hex) 1 hm
    (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg
    (fun r h1 h2 => by omega) (Nat.find hex : ℤ) (by omega)
  rw [Ct.levN_eq, hC]
  unfold serC
  rw [if_pos (by omega), map_smul, map_pow, Int.toNat_natCast, framepf_coeff_pow_self _ hQ0, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hQ1), one_smul]

theorem framepf_levN_phi (hc : IsCrys PD T.ρ) (c : ZMod n) (ζ : LL)
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (PD.p ^ j)) (hζ1 : ζ ^ PD.p = 1)
    (hQ0 : PowerSeries.constantCoeff (W.lev c ζ W.Q) = 0) (hQ1 : PowerSeries.coeff 1 (W.lev c ζ W.Q) ≠ 0)
    (x : ↥(W.N T)) (m R : ℕ) (hm : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T)
    (hneg : ∀ r : ℤ, r < 0 → Ct.levB T (c - 1) 1 x r = 0)
    (hmid : ∀ r : ℤ, 1 ≤ r → r < R → Ct.levB T (c - 1) 1 x r = 0) (k : ℤ) (hk : k < m + R) :
    W.levN T c ζ ⟨_, hm⟩ k = serC (W.lev c ζ (W.Q ^ m)) (valAt W T c ζ (x : W.DD T)) k := by
  rw [framepf_valAt Ct T hc c ζ hζ hζ1 hQ0 hQ1 x hneg ⟨m, hm⟩, Ct.levN_eq,
    framepf_levB_phi Ct T hc c ζ hζ hζ1 x m R hm
      (fun j hj => by rw [map_pow]; exact framepf_coeff_pow_lt _ hQ0 _ _ hj) hneg hmid k hk]
  unfold serC
  split_ifs
  · rw [map_smul]
  · rw [map_zero]

end Local

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.InvLiftPfA
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem invLiftPf_quot_Δ (π' : LetA O n) (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π') (k : ℕ) (r₀ : W.DD T) (hr₀N : r₀ ∈ W.N T)
    (hΔ : ∀ δ ∈ W.DelF, W.γD T δ (π' ^ k • r₀) = π' ^ k • r₀) : r₀ ∈ W.NΔ T := by
  show r₀ ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ r₀ = r₀
  refine ⟨hr₀N, fun δ hδ => ?_⟩
  have h1 := hΔ δ hδ
  rw [← algebraMap_smul W.EE (π' ^ k) r₀, W.γD_smul, W.γE_ext] at h1
  have e : Formalism.BasicNotions.letγ (W.γ₀ δ) (π' ^ k) = π' ^ k := by
    change W.γA δ (π' ^ k) = π' ^ k
    rw [map_pow, hπΔ δ hδ]
  rw [e] at h1
  have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
    rw [map_pow]; exact hu.pow k
  exact hu'.smul_left_cancel.mp h1

private theorem PiNS_iff_lemma_3 (π' : LetA O n) (k : ℕ) (x : W.DD T) :
    x ∈ PiNS W T π' k ↔ (∃ y ∈ W.N T, π' ^ k • y = x) ∧ x ∈ DelS W T := by
  unfold PiNS
  rw [Submodule.mem_inf]
  refine and_congr ?_ Iff.rfl
  show x ∈ (W.N T).map (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ k)) ↔ _
  rw [Submodule.mem_map]
  rfl

private theorem DelS_iff_lemma_4 (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold DelS
  simp [Submodule.mem_iInf, sub_eq_zero]

private theorem gamD_smulA_lemma_5 (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  show W.γD T g (a • x) = Formalism.BasicNotions.letγ (W.γ₀ g) a • W.γD T g x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

private theorem cancel_lemma_6 (π' : LetA O n) (hu : IsUnit (algebraMap (LetA O n) W.EE π')) (k : ℕ)
    (u v : W.DD T) (h : π' ^ k • u = π' ^ k • v) : u = v := by
  rw [← algebraMap_smul W.EE (π' ^ k) u, ← algebraMap_smul W.EE (π' ^ k) v] at h
  have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by rw [map_pow]; exact hu.pow k
  exact hu'.smul_left_cancel.mp h

private theorem PiNS_anti_lemma_7 (π' : LetA O n) {a b : ℕ} (hab : a ≤ b) {z : W.DD T}
    (hz : z ∈ PiNS W T π' b) : z ∈ PiNS W T π' a := by
  obtain ⟨⟨y, hy, hyz⟩, hzD⟩ := (PiNS_iff_lemma_3 W T π' b z).mp hz
  refine (PiNS_iff_lemma_3 W T π' a z).mpr ⟨⟨π' ^ (b - a) • y, (W.N T).smul_mem _ hy, ?_⟩, hzD⟩
  rw [← hyz, smul_smul, ← pow_add, show a + (b - a) = b by omega]

theorem invLiftPf_inj (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (hK : W.gamK = W.gam) (M : ℕ)
    (hnz : ∀ y : ℕ, 1 ≤ y → y < M → ∀ r₀ ∈ W.N T, ∀ d ∈ W.N T,
      (c₀ ^ y - 1) • r₀ = π' • d → ∃ e ∈ W.N T, r₀ = π' • e)
    (x : W.DD T) (hx : x ∈ PiNS W T π' 1) (hgx : W.γD T W.gamK x - x ∈ PiNS W T π' M) :
    x ∈ PiNS W T π' M := by
  have hx' := (PiNS_iff_lemma_3 W T π' 1 x).mp hx
  have hxD : x ∈ DelS W T := hx'.2
  have hxΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x := (DelS_iff_lemma_4 W T x).mp hxD
  obtain ⟨x₁, hx₁, hx₁x⟩ := hx'.1
  have hxN : x ∈ W.N T := by rw [← hx₁x]; exact (W.N T).smul_mem _ hx₁
  rw [hK] at hgx
  have key : ∀ y : ℕ, y ≤ M → x ∈ PiNS W T π' y := by
    intro y
    induction y with
    | zero =>
      intro _
      exact (PiNS_iff_lemma_3 W T π' 0 x).mpr ⟨⟨x, hxN, by simp⟩, hxD⟩
    | succ y ih =>
      intro hyM
      rcases Nat.eq_zero_or_pos y with hy0 | hy0
      · subst hy0; exact hx
      · obtain ⟨⟨r₀, hr₀, hr₀x⟩, -⟩ := (PiNS_iff_lemma_3 W T π' y x).mp (ih (by omega))
        have hr₀Δ : r₀ ∈ W.NΔ T :=
          invLiftPf_quot_Δ W T π' hu hπΔ y r₀ hr₀ (fun δ hδ => by rw [hr₀x]; exact hxΔ δ hδ)
        obtain ⟨d, hd, hdγ⟩ := hγN r₀ hr₀Δ
        have hγr : W.γD T W.gam r₀ = r₀ + π' • d := sub_eq_iff_eq_add'.mp hdγ
        obtain ⟨s, hs⟩ : π' ∣ f ^ y - algebraMap O (LetA O n) c₀ ^ y :=
          (Dvd.intro t ht.symm).trans (sub_dvd_pow_sub_pow _ _ _)
        have hfy : f ^ y = algebraMap O (LetA O n) c₀ ^ y + π' * s := by rw [← hs]; ring
        have hg' := PiNS_anti_lemma_7 W T π' hyM hgx
        obtain ⟨⟨e', he', he'x⟩, -⟩ := (PiNS_iff_lemma_3 W T π' (y + 1) _).mp hg'
        have hγx : W.γD T W.gam x - x = π' ^ y • (algebraMap O (LetA O n) (c₀ ^ y - 1) • r₀ +
            π' • (s • r₀ + f ^ y • d)) := by
          rw [← hr₀x, gamD_smulA_lemma_5, map_pow, hf, hγr, mul_pow, hfy, map_sub, map_pow, map_one]
          set a : LetA O n := algebraMap O (LetA O n) c₀ with ha_def
          have e1 : ∀ (A B A' B' : LetA O n), A = A' → B = B' → A • r₀ + B • d = A' • r₀ + B' • d := by
            intro A B A' B' h1 h2; rw [h1, h2]
          calc _ = (π' ^ y * (a ^ y + π' * s) - π' ^ y) • r₀ + (π' ^ y * (a ^ y + π' * s) * π') • d := by
                  rw [smul_add, sub_smul, smul_smul]; abel
            _ = (π' ^ y * (a ^ y - 1) + π' ^ y * (π' * s)) • r₀ +
                  (π' ^ y * (π' * (a ^ y + π' * s))) • d := e1 _ _ _ _ (by ring) (by ring)
            _ = _ := by
              simp only [smul_add, smul_smul, add_smul, add_assoc, mul_add]
        rw [hγx, pow_succ, ← smul_smul] at he'x
        have h1 := cancel_lemma_6 W T π' hu y _ _ he'x
        have h2 : (c₀ ^ y - 1) • r₀ = π' • (e' - (s • r₀ + f ^ y • d)) := by
          rw [← algebraMap_smul (LetA O n) (c₀ ^ y - 1) r₀, smul_sub, h1]
          abel
        obtain ⟨e, he, hre⟩ := hnz y hy0 (by omega) r₀ hr₀ _
          (Submodule.sub_mem _ he' (Submodule.add_mem _ ((W.N T).smul_mem _ hr₀)
            ((W.N T).smul_mem _ hd))) h2
        refine (PiNS_iff_lemma_3 W T π' (y + 1) x).mpr ⟨⟨e, he, ?_⟩, hxD⟩
        rw [← hr₀x, hre, smul_smul, ← pow_succ]
  exact key M le_rfl

theorem invLiftPf_nzd (π' w : LetA O n) (s' : ℕ) (hw : IsUnit w) (hπ : π' = w * letπ ^ s')
    (ℓ : O) (hℓ : ∀ c : O, ℓ * c = 0 → c = 0)
    (r : ℕ) (b : Fin r → W.DD T) (hbN : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (m : ℕ) (r₀ y : W.DD T) (hr₀ : r₀ ∈ W.N T) (hy : y ∈ W.N T)
    (h : ℓ ^ m • r₀ = π' • y) : ∃ e ∈ W.N T, r₀ = π' • e := by
  classical
  have hℓm : ∀ k : ℕ, ∀ c : O, ℓ ^ k * c = 0 → c = 0 := by
    intro k
    induction k with
    | zero => intro c hc; simpa using hc
    | succ k ih => intro c hc; rw [pow_succ, mul_assoc] at hc; exact hℓ _ (ih _ hc)
  obtain ⟨a, ha, -⟩ := huniq r₀ hr₀
  obtain ⟨cc, hc, -⟩ := huniq y hy
  have hmem : ℓ ^ m • r₀ ∈ W.N T := by
    rw [← algebraMap_smul (LetA O n) (ℓ ^ m) r₀]; exact (W.N T).smul_mem _ hr₀
  have e1 : ℓ ^ m • r₀ = ∑ j, (algebraMap O (LetA O n) (ℓ ^ m) * a j) • b j := by
    rw [ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul (LetA O n) (ℓ ^ m), smul_smul]
  have e2 : ℓ ^ m • r₀ = ∑ j, (π' * cc j) • b j := by
    rw [h, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
  have hcoef : (fun j => algebraMap O (LetA O n) (ℓ ^ m) * a j) = fun j => π' * cc j :=
    (huniq _ hmem).unique e1 e2
  have hdiv : ∀ j i, ∃ e : PowerSeries O, a j i = PowerSeries.X ^ s' * e := by
    intro j i
    have h1 : (algebraMap O (LetA O n) (ℓ ^ m) * a j) i = (π' * cc j) i :=
      congrFun (congrFun hcoef j) i
    rw [hπ] at h1
    have h3 : algebraMap O (PowerSeries O) (ℓ ^ m) * a j i =
        (w i * PowerSeries.X ^ s') * cc j i := h1
    have h2 : algebraMap O (PowerSeries O) (ℓ ^ m) * a j i =
        PowerSeries.X ^ s' * (w i * cc j i) := by
      rw [h3]; ring
    have h4 : ∀ d < s', PowerSeries.coeff d (a j i) = 0 := by
      intro d hd
      have h5 : PowerSeries.coeff d (algebraMap O (PowerSeries O) (ℓ ^ m) * a j i) = 0 := by
        rw [h2]; exact PowerSeries.X_pow_dvd_iff.mp (dvd_mul_right _ _) d hd
      rw [← Algebra.smul_def, PowerSeries.coeff_smul, smul_eq_mul] at h5
      exact hℓm m _ h5
    exact PowerSeries.X_pow_dvd_iff.mpr h4
  choose e he using hdiv
  obtain ⟨u, hu⟩ := hw
  have hA : ∀ j, a j = π' * ((↑u⁻¹ : LetA O n) * fun i => e j i) := by
    intro j
    have hx : π' * ((↑u⁻¹ : LetA O n) * fun i => e j i) = letπ ^ s' * fun i => e j i := by
      rw [hπ, ← hu, show ((↑u : LetA O n) * letπ ^ s') * ((↑u⁻¹ : LetA O n) * fun i => e j i)
        = ((↑u : LetA O n) * ↑u⁻¹) * (letπ ^ s' * fun i => e j i) by ring, Units.mul_inv, one_mul]
    rw [hx]
    funext i
    exact he j i
  refine ⟨∑ j, ((↑u⁻¹ : LetA O n) * fun i => e j i) • b j,
    Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbN j), ?_⟩
  rw [Finset.smul_sum, ha]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← hA j]

private theorem letS_mem_lemma (c : ZMod n) (x : W.DD T) :
    x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  unfold letS
  rw [LinearMap.mem_ker]
  simp [sub_eq_zero]

private theorem gam_letE_lemma_2 (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  have e : Formalism.BasicNotions.letγ (W.γ₀ g) (letE c : LetA O n) = letE c := by
    funext i
    show W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i
    unfold letE
    by_cases hi : i = c
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, e, algebraMap_smul]

theorem invLiftPf_lift (π' Eπ : LetA O n) (h' M σ : ℕ) (c : ZMod n)
    (hG : GradN W T π' σ M) (hL : NinLam W T Eπ h') :
    ∀ w ∈ InvS W T π' Eπ h' 1 c, ∃ wb ∈ InvS W T π' Eπ h' M c,
      ((PD.p : ℕ) : O) ^ σ • w - wb ∈ PiNS W T π' 1 := by
  intro w hw
  unfold InvS at hw ⊢
  rw [Submodule.mem_inf, Submodule.mem_comap] at hw
  obtain ⟨hwL, hwγ⟩ := hw
  rw [LinearMap.sub_apply, LinearMap.id_apply] at hwγ
  have hwS : w ∈ letS W T c := by
    have h0 := hwL
    unfold LamPS at h0
    exact (Submodule.mem_inf.mp h0).2
  have hzS : W.γD T W.gamK w - w ∈ letS W T c := by
    rw [letS_mem_lemma] at hwS ⊢
    rw [smul_sub, ← gam_letE_lemma_2, hwS]
  obtain ⟨k, hk, hk2⟩ := hG c (W.γD T W.gamK w - w) (Submodule.mem_inf.mpr ⟨hwγ, hzS⟩)
  obtain ⟨hk1, hkS⟩ := Submodule.mem_inf.mp hk
  refine ⟨((PD.p : ℕ) : O) ^ σ • w - k, ?_, ?_⟩
  · rw [Submodule.mem_inf]
    refine ⟨Submodule.sub_mem _ (Submodule.smul_mem _ _ hwL) (hL c ?_), ?_⟩
    · unfold NcS
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, hkS⟩
      · have h0 := hk1
        unfold PiNS at h0
        have h1 : k ∈ (W.N T).map (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ 1)) := (Submodule.mem_inf.mp h0).1
        obtain ⟨y, hy, hyk⟩ := Submodule.mem_map.mp h1
        rw [← hyk]
        exact (W.N T).smul_mem _ hy
      · have h0 := hk1
        unfold PiNS at h0
        exact (Submodule.mem_inf.mp h0).2
    · rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, map_sub, map_smul]
      convert hk2 using 1
      rw [smul_sub]
      abel
  · rw [sub_sub_cancel]
    exact hk1

end Local

end Formalism.MainNotions.N.Ln34

end
end
