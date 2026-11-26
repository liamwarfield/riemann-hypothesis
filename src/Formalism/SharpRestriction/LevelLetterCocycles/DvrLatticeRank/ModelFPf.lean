module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfG
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.KapPiPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfEqv

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPf
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules Formalism.MainNotions.N.Ln34.ModelFPf

theorem modelflink_pf : ModelFLinkStep := by
  intro D HW F Cm CA CB CK hA hP l _ hl K LL hG π' E hπ h' hh' c α β hfr T hcry hjmp
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  obtain ⟨-, -, -, h4W, h5W, -⟩ := hA.1 l K 1 LL hG
  obtain ⟨h5a, h5b, -⟩ := h5W T (fun _ => h') (fun _ => h') hcry (fun τ _ _ => hjmp τ)
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hπ
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hQ : ((HW l).W K 1 LL hG).Q = (w : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' := by
    rw [Q_eq_q _ hs]
    exact hw
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hM : 1 ≤ MK l K h' := by
    refine Nat.one_le_ceil_iff.2 (div_pos ?_ ?_)
    · have : (1 : ℝ) ≤ h' := by exact_mod_cast hh'
      linarith
    · exact_mod_cast hsK
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  have hπu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE π') := by
    rw [hw0, map_mul, map_pow]
    exact (w0.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  have hpt : ∀ ζ τ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → ζ ^ ((D.loc l).PD K).p = 1 ∧ ζ ≠ 1 := by
    intro ζ τ hPt
    obtain ⟨τs, hIs, -⟩ := hPt
    have hz1 : (D.loc l).ζQ 1 ^ l = 1 := by
      rw [(D.loc l).ζQ_succ 0, (D.loc l).ζQ_zero]
    have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 :=
      le_sup_right (a := K0 K) (IntermediateField.subset_adjoin _ _ (by rw [pow_one]; exact hz1))
    have hy := hIs.2 ⟨_, hmem⟩ rfl
    have hyl : (⟨_, hmem⟩ : ↥(Ks K 1)) ^ l = 1 := Subtype.ext (by simpa using hz1)
    refine ⟨?_, ?_⟩
    · rw [hp, ← hy, ← map_pow, hyl, map_one]
    · intro h1
      rw [← hy] at h1
      have : (⟨_, hmem⟩ : ↥(Ks K 1)) = 1 := τs.toRingHom.injective (by rw [map_one]; exact h1)
      exact (D.loc l).ζQ_one (congrArg Subtype.val this)
  exact modelF_local ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h'
    (MK l K h') (sigA l (sK l K) h') c α β hfr hcry hjmp hs hM hπΔ hEΔ hπu
    (Units.inv_mul w) hQ hu'Δ hu.val_inv_mul (by rw [hgam]; exact hγ) (h5a c)
    (fun y hy => ninLamPf_local ((HW l).W K 1 LL hG) T _ h' w hs hw h5b c hy) (h4W T hcry)
    hpt (hP l hl K LL hG T h' hh' hcry hjmp)

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UniversalLiftRingMembership
noncomputable section

namespace Formalism.MainNotions.N.Ln34.UniversalLiftFrames

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.N.Ln34 Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules PowerSeries

set_option maxHeartbeats 1000000 in
open Formalism.MainNotions.N.Ln34.ModelFPf in
theorem universal_lift_ring_membership (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) :
    Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ ∧ π' ∈ ((HW l).W K 1 LL hG).AΔ ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) ∧
    IsUnit (algebraMap (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) ((HW l).W K 1 LL hG).EE π') ∧
    ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam ∧
    (∃ uE ∈ ((HW l).W K 1 LL hG).AΔ, ∃ uE' ∈ ((HW l).W K 1 LL hG).AΔ, uE' * uE = 1 ∧
      ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') = uE * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') ∧
    (∃ uπ ∈ ((HW l).W K 1 LL hG).AΔ, ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' = π' * uπ) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hp9
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  have hπu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE π') := by
    rw [hw0, map_mul, map_pow]
    exact (w0.isUnit.map _).mul (((HW l).W K 1 LL hG).EE_π.pow _)
  have hEu : IsUnit (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) := by
    have hq := Formalism.MainNotions.LiftingTheory.liftb_q_unit ((HW l).W K 1 LL hG)
    rw [hw, map_mul] at hq
    exact isUnit_of_mul_isUnit_right hq
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  have hnzπ : ∀ a : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)), a * π' = 0 → a = 0 := by
    intro a ha
    apply ((HW l).W K 1 LL hG).EE_inj
    have h1 := congrArg (algebraMap (LetA _ _) ((HW l).W K 1 LL hG).EE) ha
    rw [map_mul, map_zero] at h1
    rw [map_zero]
    exact hπu.mul_left_eq_zero.1 h1
  have hγπ : ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam π' =
      (1 + (w2 : LetA _ _) * Formalism.MainNotions.DeltaInvariantLattices.Eat E π') * π' := by
    rw [sub_eq_iff_eq_add] at hw2
    rw [hw2]
    ring
  exact ⟨hEΔ, hπΔ, hEu, hπu, ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl),
    ⟨u, huΔ, _, hu'Δ, hu.val_inv_mul, hγ⟩,
    ⟨_, u_mem_AΔ ((HW l).W K 1 LL hG) hπΔ hnzπ hγπ, by rw [hγπ]; ring⟩⟩

theorem universal_lift_points (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : adm1 D HW F Cm) {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hp9 : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) :
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) = 0 ∧
    coeff 1 (((HW l).W K 1 LL hG).lev c ζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) ≠ 0 ∧
    constantCoeff (((HW l).W K 1 LL hG).lev c ζ π') ≠ 0 ∧
    ∀ a, ((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gam a) =
      rescale (algebraMap ↥(OL LL) ↥LL.1 ((Formalism.MainNotions.DeltaInvariantLattices.uU ((HW l).W K 1 LL hG) : (↥(OL LL))ˣ) : ↥(OL LL)))
        (((HW l).W K 1 LL hG).lev c ζ a) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hζ : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    rw [hp]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  obtain ⟨-, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, -, -⟩ := hp9
  obtain ⟨e₁, he₁, he₁0⟩ :=
    DescentValuation.u3downPf_lev_E ((HW l).W K 1 LL hG) c ζ hζ (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') w hw
  refine ⟨?_, ?_, DescentValuation.u3downPf_cc_π' ((HW l).W K 1 LL hG) c ζ hζ π' (sK l K) w0 hw0, ?_⟩
  · rw [he₁]
    simp
  · rw [he₁, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact he₁0
  · intro a
    have hg := ((HW l).W K 1 LL hG).gam_gen
    exact ((Cm l).C K 1 LL hG).tie.lev_Γ _ c ζ ζ 1 1 (by rw [pow_one]; exact hζ)
      (le_of_eq (by simpa [hs] using hg.symm)) (pow_one ζ).symm a

theorem embeddings_card_le_degree (D : D7) (HW : HWOf D.loc) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    ∃ τs : Finset (↥K.1 →ₐ[ℚ_[l]] ↥LL.1), (∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → τ ∈ τs) ∧
      τs.card ≤ finrank ↥(K0 K) ↥K.1 := by
  classical
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : Finite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) := by
    apply Nat.finite_of_card_ne_zero
    rw [GenPf.natCard_emb K LL hG]
    exact (Module.finrank_pos (R := ℚ_[l]) (M := ↥K.1)).ne'
  haveI := Fintype.ofFinite (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)
  haveI : FiniteDimensional ↥(K0 K) ↥K.1 := Module.Finite.right ℚ_[l] ↥(K0 K) ↥K.1
  refine ⟨Finset.univ.filter (fun τ => Formalism.MainNotions.DeltaInvariantLattices.OverLetter ((HW l).W K 1 LL hG) τ c),
    fun τ ζ hpt => Finset.mem_filter.2 ⟨Finset.mem_univ _, u3upPf_pt_over D HW hG c ζ τ hpt⟩, ?_⟩
  have h := kapPiPf_card ((HW l).W K 1 LL hG) c
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  exact h

end Formalism.MainNotions.N.Ln34.UniversalLiftFrames
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAsm
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
    (W : LocWach PD LL O v n) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n)
    (h' M σ : ℕ) (c : ZMod n)

structure FramepfData (T : LocLat G Qp LL O) (hh : LcQ W T π' c →ₗ[O] W.DD T)
    (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c) : Prop where
  hγ : ∀ ℓ, W.γD T W.gam (hh ℓ) - hh ℓ ∈ PiNS W T π' M
  hmod : ∀ z hz, hh (mkL W T π' c z hz) - ((PD.p : ℕ) : O) ^ σ • z ∈ PiNS W T π' 1
  hΨ : ∀ e ℓ, Ψ (e ⊗ₜ ℓ) = e • W.φD T (hh ℓ)
  ΨJ : ∀ x ∈ JLA W T π' Eπ h' M c, Ψ x ∈ JP W T π' Eπ h' M c
  ΦJ : ∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c
  βα : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, Φ (Ψ x) - ((PD.p : ℕ) : O) ^ (2 * σ) • x ∈ JLA W T π' Eπ h' M c
  αβ : ∀ y ∈ LamPS W T Eπ h' c, Ψ (Φ y) - ((PD.p : ℕ) : O) ^ (2 * σ) • y ∈ JP W T π' Eπ h' M c
  sat : ∀ x ∈ LamLA W T π' Eπ h' c ⊤, ((PD.p : ℕ) : O) ^ (2 * σ) • x ∈ JLA W T π' Eπ h' M c →
    x ∈ JLA W T π' Eπ h' M c
  inj : ∀ x ∈ PiNS W T π' 1, W.γD T W.gam x - x ∈ PiNS W T π' M → x ∈ PiNS W T π' M
  loc : ∀ τ ζ, Pt c ζ τ → ∀ x y, Ψ x - y ∈ JP W T π' Eπ h' M c →
    ∀ (m : ℕ) (a : Fin m → ↥W.AΔ) (z : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a z →
    ∀ (k : ℕ) (hk : W.Q ^ k • (Eπ ^ h' • y) ∈ W.N T) (i : ℤ), i < k + 4 * h' →
      W.levN T c ζ ⟨_, hk⟩ i =
        (PD.p ^ σ) • serMul (W.lev c ζ (W.Q ^ k)) (expS W T c ζ (fun j => (a j : LetA O n)) z) i

theorem quotientMk_eq_iff_sub_mem {T : LocLat G Qp LL O} {y y' : W.DD T} (hy : y ∈ LamPS W T Eπ h' c)
    (hy' : y' ∈ LamPS W T Eπ h' c) :
    mkP W T π' Eπ h' M c y hy = mkP W T π' Eπ h' M c y' hy' ↔ y - y' ∈ JP W T π' Eπ h' M c :=
  Submodule.Quotient.eq _

theorem framepf_mkLA_eq {T : LocLat G Qp LL O} {x x' : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤)
    (hx' : x' ∈ LamLA W T π' Eπ h' c ⊤) :
    mkLA W T π' Eπ h' M c x hx = mkLA W T π' Eπ h' M c x' hx' ↔ x - x' ∈ JLA W T π' Eπ h' M c :=
  Submodule.Quotient.eq _


set_option maxHeartbeats 1000000 in
theorem framepf_frameA (hK : W.gamK = W.gam) (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (huE : IsUnit (algebraMap (LetA O n) W.EE Eπ)) (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (u : LetA O n) (huΔ : u ∈ W.AΔ) (hφ : W.φA π' ^ M = π' ^ M * Eπ ^ (4 * h') * u)
    {f t t' : LetA O n} (hfΔ : f ∈ W.AΔ) (hf : W.γA W.gamK π' = π' * f)
    (htΔ : t ∈ W.AΔ) (ht : W.γA W.gamK Eπ = Eπ * t)
    (ht'Δ : t' ∈ W.AΔ) (ht' : Eπ = W.γA W.gamK Eπ * t')
    (hex : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤, Ψ x ∈ LamPS W T Eπ h' c) ∧
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      FramepfData W Pt π' Eπ h' M σ c T hh Ψ Φ) :
    FrameA W Pt π' Eπ h' M σ c := by
  have hex' : ∀ T : LocLat G Qp LL O, ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤, Ψ x ∈ LamPS W T Eπ h' c) ∧
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      (IsCrys PD T.ρ → FramepfData W Pt π' Eπ h' M σ c T hh Ψ Φ) := by
    intro T
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨hh, Ψ, Φ, h1, h2, h3⟩ := hex T hT
      exact ⟨hh, Ψ, Φ, h1, h2, fun _ => h3⟩
    · exact ⟨0, 0, 0, fun _ _ => Submodule.zero_mem _, fun _ _ => Submodule.zero_mem _,
        fun h => absurd h hT⟩
  choose hh Ψ Φ hΨL hΦL hD using hex'
  let α : FrA W π' Eπ h' M c := fun T => (Submodule.mkQ _).comp (LinearMap.codRestrict (LamPS W T Eπ h' c)
    (((Ψ T).restrictScalars O).comp (LamLA W T π' Eπ h' c ⊤).subtype) fun x => hΨL T x x.2)
  let β : FrB W π' Eπ h' M c := fun T => (Submodule.mkQ _).comp
    (LinearMap.codRestrict (LamLA W T π' Eπ h' c ⊤)
      (((Φ T).restrictScalars O).comp (LamPS W T Eπ h' c).subtype) fun y => hΦL T y y.2)
  have hα : ∀ T x hx y hy, α T ⟨x, hx⟩ = mkP W T π' Eπ h' M c y hy ↔
      Ψ T x - y ∈ JP W T π' Eπ h' M c := fun T x hx y hy =>
    quotientMk_eq_iff_sub_mem W π' Eπ h' M c (hΨL T x hx) hy
  have hβ : ∀ T y hy x hx, β T ⟨y, hy⟩ = mkLA W T π' Eπ h' M c x hx ↔
      Φ T y - x ∈ JLA W T π' Eπ h' M c := fun T y hy x hx =>
    framepf_mkLA_eq W π' Eπ h' M c (hΦL T y hy) hx
  refine ⟨α, β, fun T hT _ => ?_, fun T₁ T₂ F hT₁ hT₂ _ _ => ?_⟩
  · have D := hD T hT
    have hΨγ := framepf_Ψα_γ π' Eπ h' M c ht'Δ ht' hu huE hΔπ u huΔ hφ (hh T)
      (by rw [hK]; exact D.hγ) (Ψ T) D.hΨ
    refine ⟨fun x hx hJ => ?_, fun y hy hJ => ?_, fun x hx y hy h => ?_, fun y hy x hx h => ?_,
      fun a ha x hx y hy h hax hay => ?_, fun a ha y hy x hx h hay hax => ?_,
      fun x hx y hy h hgx hgy => ?_, fun y hy x hx h hgy hgx => ?_,
      fun τ ζ hpt x hx y hy h => D.loc τ ζ hpt x y ((hα T x hx y hy).1 h)⟩
    · exact (hα T x hx 0 (Submodule.zero_mem _)).2 (by rw [sub_zero]; exact D.ΨJ x hJ)
    · exact (hβ T y hy 0 (Submodule.zero_mem _)).2 (by rw [sub_zero]; exact D.ΦJ y hJ)
    · rw [hβ]
      have h1 := Submodule.sub_mem _ (D.βα x hx) (D.ΦJ _ ((hα T x hx y hy).1 h))
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hα]
      have h1 := Submodule.sub_mem _ (D.αβ y hy) (D.ΨJ _ ((hβ T y hy x hx).1 h))
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hα, framepf_Ψ_smulLA, ← smul_sub]
      exact framepf_JP_smul π' Eπ h' M c ha ((hα T x hx y hy).1 h)
    · rw [hβ, ← algebraMap_smul W.EE a y, map_smul, ← framepf_smulLA_alg, ← map_sub]
      exact framepf_JLA_smul π' Eπ h' M c ha ((hβ T y hy x hx).1 h)
    · rw [hα]
      have h1 := Submodule.sub_mem _
        (framepf_γ_JP π' Eπ h' M c hfΔ hf htΔ ht ((hα T x hx y hy).1 h)) (hΨγ x hx)
      rw [map_sub, sub_sub_sub_cancel_left] at h1
      exact h1
    · rw [hβ]
      have h1 := Submodule.add_mem _
        (framepf_Ψβ_γ π' Eπ h' M c hfΔ hf htΔ ht ht'Δ ht' (Ψ T) (Φ T) _ hΨγ (hΦL T) D.ΦJ D.αβ D.βα
          D.sat y hy hgy)
        (framepf_γ_JLA π' Eπ h' M c hfΔ hf htΔ ht ((hβ T y hy x hx).1 h))
      rw [map_sub, sub_add_sub_cancel] at h1
      exact h1
  · have D₁ := hD T₁ hT₁
    have D₂ := hD T₂ hT₂
    have hFN := W.map_N F hT₁ hT₂
    have hnat := framepf_Ψα_nat F hFN π' Eπ h' M c hu huE hΔπ u huΔ hφ (hh T₁) (hh T₂)
      (framepf_hh_nat F hFN π' c M _ D₂.inj (hh T₁) (hh T₂) D₁.hγ D₂.hγ D₁.hmod D₂.hmod)
      (Ψ T₁) D₁.hΨ (Ψ T₂) D₂.hΨ
    refine ⟨fun x₁ hx₁ x₂ hx₂ y₁ hy₁ hy₂ hov h => ?_, fun y₁ hy₁ hy₂ x₁ hx₁ x₂ hx₂ hov h => ?_⟩
    · rw [hα]
      exact framepf_α_nat F hFN π' Eπ h' M c (Ψ T₁) (Ψ T₂) hnat x₁ hx₁ x₂ y₁ hov
        ((hα T₁ x₁ hx₁ y₁ hy₁).1 h)
    · rw [hβ]
      exact framepf_β_nat F hFN π' Eπ h' M c (Ψ T₁) (Ψ T₂) hnat (Φ T₁) (Φ T₂) _ (hΦL T₁) (hΦL T₂)
        D₂.ΦJ D₁.αβ D₂.βα D₂.sat y₁ hy₁ hy₂ x₁ x₂ hov ((hβ T₁ y₁ hy₁ x₁ hx₁).1 h)

end Local

end Formalism.MainNotions.N.Ln34

end
end
