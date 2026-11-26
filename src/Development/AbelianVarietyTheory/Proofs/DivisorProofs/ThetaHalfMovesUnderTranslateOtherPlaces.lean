module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePolynomialIntegerExponentDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisCoverQuotientFreeFiniteAction
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlaces
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

namespace GlobalTheory.ThetaBaseMove

open Formalism.IndefR.Fin.LevelGroupLemmas

section General

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem heisO_smul' (u : WO S T) (c : ℂ) (g : WO S T → ℂ) : heisO ψ S T u (c • g) = c • heisO ψ S T u g := by
  funext w
  simp only [heisO, Pi.smul_apply, smul_eq_mul]
  ring

theorem theta_smul (c : ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (c • g) := by
  refine ⟨fun γ w => ?_, ?_, hg.cont.const_smul c, fun k L hL h0 w => (hg.smooth k L hL h0 w).const_smul c⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [hg.quasi]; ring
  · obtain ⟨U, hU, h⟩ := hg.level
    exact ⟨U, hU, fun u hu h0 => by rw [heisO_smul', h u hu h0]⟩

theorem isPlaceModel_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)} {f₀ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm)
    (hth : ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ)) (g : GA D S) (h : GA D T) (c : ℂ)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) f₀) (c • (om (g, h)).comp Tm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hΦ x hx
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.trans Φ hΦ x hx, LinearMap.comp_apply,
      hW.om_heis g h x (Tm Φ) (hth Φ hΦ), hfx x (Or.inl hx), heisO_smul']
  · intro Φ hΦ y hy
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, hTm.modul Φ hΦ y hy, LinearMap.comp_apply,
      hW.om_heis g h y (Tm Φ) (hth Φ hΦ), hfx y (Or.inr hy), heisO_smul']
  · rw [LinearMap.smul_apply, LinearMap.comp_apply, hTm.vac]

theorem isThetaAt_move (hW : IsWeilDatumO ψ S T χS χT om) {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hth : ∀ f₀, IsThetaFunO ψ S T f₀ → ∀ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Tm →
      ∀ Φ, IsSBHalf e Λ Φ → IsThetaFunO ψ S T (Tm Φ))
    {b Φ f : WO S T → ℂ} (hb : IsThetaFunO ψ S T b) (g : GA D S) (h : GA D T) {c : ℂ} (hc : c ≠ 0)
    (hfx : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g h x = x)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 b Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (c • om (g, h) b) Φ (c • om (g, h) f) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  refine ⟨⟨_, isPlaceModel_move hW hTm (hth b hb Tm hTm) g h c hfx⟩, fun T' hT' => ?_⟩
  have hfx' : ∀ x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → actO S T g⁻¹ h⁻¹ x = x := fun x hx => by
    conv_lhs => rw [← hfx x hx]
    rw [actO_actO, inv_mul_cancel, inv_mul_cancel, actO_one]
  have k1 : ∀ v, om (g⁻¹, h⁻¹) (om (g, h) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have k2 : ∀ v, om (g, h) (om (g⁻¹, h⁻¹) v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  have hm := isPlaceModel_move hW hT' (hth _ (theta_smul c (hW.om_pres _ _ hb)) T' hT') g⁻¹ h⁻¹ c⁻¹ hfx'
  rw [map_smul, k1, smul_smul, inv_mul_cancel₀ hc, one_smul] at hm
  have e1 : f = _ := hall _ hm
  rw [e1, LinearMap.smul_apply, LinearMap.comp_apply, map_smul, k2, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem actO_fix_of_orth {a e : AE D} {z : GA D S} (hz : SuppAt a S z) (h0 : e * (a + cA D a) = 0) {x : WO S T}
    (hx : IsHalf e x) : actO S T z⁻¹ 1 x = x := by
  rw [actO_eq, inv_inv, mt_one', Matrix.one_mul]
  have : HMul.hMul (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (mt S z - 1) = 0 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← hx k j, ← hz j l]
    linear_combination (x k j * (mt S z - 1) j l) * h0
  rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this

end General

theorem thAt_move : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _hG i t _hV Sa St hSa hSt hd eg ea et fg b Φ f z c hg ha ht hfg hb hz hc hf
  obtain ⟨⟨hψ, hvac⟩, e, he, -⟩ := hC.thP.vP i t
  have hW := (GlobalTheory.OnCmp.kerDat_tuple (i := i) hC.lev hC.thP t).weil
  have hSV := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
  have hSW := GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
  have hsp : SplitSet (R.Q t) := SplitSet.mono ⟨e, he⟩ (by convert Finset.subset_union_right)
  have hth : ∀ {a : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum a P → ∀ f₀, IsThetaFunO R.ψ (Vc D i) (Wc D i) f₀ → ∀ Tm,
      IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D a)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 f₀ Tm →
      ∀ Ψ, IsSBHalf (cA D a) (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) Ψ →
        IsThetaFunO R.ψ (Vc D i) (Wc D i) (Tm Ψ) := by
    intro a P h f₀ hf₀ Tm hTm Ψ hΨ
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSV
    letI := GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSW
    exact GlobalTheory.DiagLiftFix.isTheta_placeModel hψ inferInstance inferInstance (by rw [← map_mul, GlobalTheory.PlaceVec.idemSum_mul_self h])
      (by rw [← map_mul, h.2, map_zero]) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart h)) hf₀ Tm hTm Ψ hΨ
  have hSBg := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart hg))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    R.Pg (fun y => omegaK R.Pg y) fun y y' h => GlobalTheory.PlaceVec.omegaK_congr R.Pg h
  have hSBa := GlobalTheory.PlaceVec.isSBHalf_of_red (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSV) (GlobalTheory.PlaceVec.selfDual_isFullLattice _ _ hSW) (GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart ha))
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i))
    (GlobalTheory.PlaceVec.frMapAdj_add _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_up _ _ _ _) (GlobalTheory.PlaceVec.frMapAdj_down _ _ _ _)
    Sa (fun y => omegaQ Sa (Wc D i).rank (R.xiR t) (-1) y) fun y y' h => GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ h
  have hfgθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) fg := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hfg
    rw [hall Tm hTm]
    exact hth hg _ hvac.theta Tm hTm _ hSBg
  have hbθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) b := by
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hb
    rw [hall Tm hTm]
    exact hth ha _ hfgθ Tm hTm _ hSBa
  have o1 : et * ea = 0 := by
    rw [← idem_eq ht, ← idem_eq ha, idem, idem, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq =>
      hsp.mul_eq_zero (hSt hp) (hSa hq) fun e => Finset.disjoint_left.1 hd hq (e ▸ hp)
  have o2 : et * cA D ea = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← idem_eq ht, ← idem_eq ha, idem, idem, map_sum, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => hsp.mul_conj (hSt hp) (hSa hq)
  have o3 : et * (ea + cA D ea) = 0 := by rw [mul_add, o1, o2, add_zero]
  have o4 : cA D et * (ea + cA D ea) = 0 := by
    have := congrArg (cA D) o3
    rwa [map_mul, map_add, GlobalTheory.LatVac.cA_cA, map_zero, add_comm] at this
  refine isThetaAt_move hW (hth ht) hbθ z⁻¹ 1 hc (fun x hx => ?_) hf
  rcases hx with hx | hx
  · exact actO_fix_of_orth hz o4 hx
  · rw [GlobalTheory.LatVac.cA_cA] at hx
    exact actO_fix_of_orth hz o3 hx

end GlobalTheory.ThetaBaseMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaHalfMovesUnderTranslateOtherPlacesStatement
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_half_moves_under_translate_other_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  first | exact @GlobalTheory.ThetaBaseMove.thAt_move | exact GlobalTheory.ThetaBaseMove.thAt_move | (intros; apply GlobalTheory.ThetaBaseMove.thAt_move <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefMapIntOfPos
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc Matrix

namespace GlobalTheory.Poinc

theorem posDef_map_int_of_pos {n : ℕ} (L : Matrix (Fin n) (Fin n) ℤ) (hs : L.IsSymm)
    (hp : ∀ ξ : Fin n → ℤ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (L *ᵥ ξ)) : (L.map (Int.cast : ℤ → ℝ)).PosDef := by
  set M := L.map (Int.cast : ℤ → ℝ) with hM
  have hH : M.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp [M, hs.apply]
  have hdet : L.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hLv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := hp v hv
    rw [hLv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hint : ∀ z : Fin n → ℤ, (fun i => (z i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (z i : ℝ)) = ((z ⬝ᵥ (L *ᵥ z) : ℤ) : ℝ) := by
    intro z
    simp [M, dotProduct, mulVec]
  have hrat : ∀ t : Fin n → ℚ, 0 ≤ (fun i => (t i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (t i : ℝ)) := by
    intro t
    obtain ⟨⟨D, hD⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) t
    choose z hz using hn
    have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hD
    have hz' : (fun i => (z i : ℝ)) = (D : ℝ) • fun i => (t i : ℝ) := by
      funext i
      have h1 : (z i : ℚ) = D * t i := by simpa [Submonoid.smul_def] using hz i
      have h2 := congrArg (Rat.cast : ℚ → ℝ) h1
      push_cast at h2
      simpa using h2
    have h0 : 0 ≤ z ⬝ᵥ (L *ᵥ z) := by
      rcases eq_or_ne z 0 with h | h
      · simp [h]
      · exact (hp z h).le
    have h3 := hint z
    rw [hz', mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul] at h3
    have h4 : 0 ≤ ((D : ℝ) * D) * ((fun i => (t i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (t i : ℝ))) := by
      rw [mul_assoc, h3]; exact_mod_cast h0
    exact (mul_nonneg_iff_of_pos_left (mul_self_pos.2 hD')).1 h4
  have hpsd : M.PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.2 ⟨hH, fun y => ?_⟩
    rw [star_trivial]
    have hcl : IsClosed {y : Fin n → ℝ | 0 ≤ y ⬝ᵥ (M *ᵥ y)} :=
      isClosed_le continuous_const
        (Continuous.dotProduct continuous_id (Continuous.matrix_mulVec continuous_const continuous_id))
    exact (DenseRange.piMap fun _ => Rat.denseRange_cast).induction_on y hcl fun t => hrat t
  have hdetM : M.det = (L.det : ℝ) := by
    rw [hM]
    exact ((Int.castRingHom ℝ).map_det L).symm
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun x hx => ?_⟩
  refine lt_of_le_of_ne ((posSemidef_iff_dotProduct_mulVec.1 hpsd).2 x) fun h0 => hdet ?_
  have hk : M *ᵥ x = 0 := hpsd.dotProduct_mulVec_zero_iff.1 (by simpa using h0.symm)
  have : M.det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, hk⟩
  rw [hdetM] at this
  exact_mod_cast this

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem exists_supports_int : ∀ (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    IsPolFanOn id φ X → ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone id φ γ →
      ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports id φ d γ a := by
  intro φ X _ _ _ hφ r γ hγ
  classical
  have hstrict := hγ.strict
  unfold IsStrict at hstrict
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hstrict
  let b := Module.finBasis ℤ X
  let S : Fin (Module.finrank ℤ X) → Fin (Module.finrank ℤ X) → LinearMap.BilinForm ℤ X := fun i j =>
    (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord i) (b.coord j) + (LinearMap.mul ℤ ℤ).compl₁₂ (b.coord j) (b.coord i)
  have hS : ∀ i j x y, S i j x y = b.repr x i * b.repr y j + b.repr x j * b.repr y i := by
    intro i j x y; simp [S]
  let L : Matrix (Fin (Module.finrank ℤ X)) (Fin (Module.finrank ℤ X)) ℤ := Matrix.of fun i j => ℓ (S i j)
  have hL : ∀ i j, L i j = ℓ (S i j) := fun _ _ => rfl
  have hexp : ∀ (β : LinearMap.BilinForm ℤ X) x y,
      β x y = ∑ i, ∑ j, b.repr x i * b.repr y j * β (b i) (b j) := by
    intro β x y
    conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hA : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
      ∑ i, ∑ j, β (b i) (b j) * L i j = 2 * ℓ β := by
    intro β hβ
    have hsum : ∑ i, ∑ j, β (b i) (b j) • S i j = (2 : ℤ) • β := by
      refine LinearMap.ext₂ fun x y => ?_
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hS]
      have e : (2 : ℤ) * β x y = β x y + β y x := by rw [hβ y x]; ring
      rw [e, hexp β x y, hexp β y x, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have := congrArg ℓ hsum
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul] at this
    simpa only [hL] using this
  have hsym : L.IsSymm := Matrix.IsSymm.ext fun i j => by simp only [hL, S, add_comm]
  have hpos : ∀ ξ : Fin (Module.finrank ℤ X) → ℤ, ξ ≠ 0 → 0 < ξ ⬝ᵥ (L *ᵥ ξ) := by
    intro ξ hξ
    let l : X →ₗ[ℤ] ℤ := ∑ i, ξ i • b.coord i
    have hl : ∀ i, l (b i) = ξ i := by
      intro i
      simp [l, Finsupp.single_apply]
    have hsymm : ∀ y z, sqForm l y z = sqForm l z y := fun y z => by simp [mul_comm]
    have hmem : sqForm l ∈ balForms id X := mem_balForms_int.2 hsymm
    have hnn : ∀ y, 0 ≤ sqForm l y y := fun y => by simpa using mul_self_nonneg (l y)
    have hne : sqForm l ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have := LinearMap.congr_fun₂ h0 (b i) (b i)
      simp [hl] at this
      exact hi this
    have hφp := hφ.pos _ hmem hnn hne
    have hℓ := h2 _ hmem hnn
    have hℓpos : 0 < ℓ (sqForm l) := by
      have : (0 : ℝ) < ℓ (sqForm l) := lt_of_lt_of_le (mul_pos (by exact_mod_cast hN) hφp) hℓ
      exact_mod_cast this
    have h5 := hA (sqForm l) hsymm
    simp only [sqForm_apply, hl] at h5
    have e : ξ ⬝ᵥ (L *ᵥ ξ) = ∑ i, ∑ j, ξ i * ξ j * L i j := by
      simp only [dotProduct, mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e, h5]
    omega
  obtain ⟨D, m, a, hD, hspan, hsum⟩ := GlobalTheory.T.exists_smul_eq_sum_vecMulVec_spanning_family _ L (posDef_map_int_of_pos L hsym hpos)
  let x : Fin m → X := fun k => b.equivFun.symm (a k)
  have hx : ∀ k i, b.repr (x k) i = a k i := fun k i => by
    show b.equivFun (b.equivFun.symm (a k)) i = a k i
    rw [b.equivFun.apply_symm_apply]
  have hB : ∀ β : LinearMap.BilinForm ℤ X, (∀ y z, β y z = β z y) →
      ∑ k, β (x k) (x k) = 2 * D * ℓ β := by
    intro β hβ
    have hsum' : ∀ i j, (D : ℤ) * L i j = ∑ k, a k i * a k j := by
      intro i j
      have := congrFun (congrFun hsum i) j
      simpa [Matrix.sum_apply, Matrix.vecMulVec_apply] using this
    calc ∑ k, β (x k) (x k) = ∑ k, ∑ i, ∑ j, a k i * a k j * β (b i) (b j) :=
          Finset.sum_congr rfl fun k _ => by rw [hexp β]; simp only [hx]
      _ = ∑ i, ∑ j, β (b i) (b j) * ((D : ℤ) * L i j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hsum' i j, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = D * (2 * ℓ β) := by
          rw [← hA β hβ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = 2 * D * ℓ β := by ring
  have hspanX : Submodule.span ℤ (Set.range x) = ⊤ := by
    have e : Set.range x = (b.equivFun.symm.toLinearMap : (Fin (Module.finrank ℤ X) → ℤ) →ₗ[ℤ] X) '' Set.range a :=
      Set.range_comp _ _
    rw [e, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  have hD0 : (0 : ℝ) < 2 * D := by have : (1 : ℝ) ≤ D := by exact_mod_cast hD
                                   linarith
  refine ⟨2 * D * N, m, x, Nat.one_le_iff_ne_zero.2 (by positivity), ⟨hspanX, ?_, ?_, ?_⟩⟩
  · intro β hβ hp
    rw [hB β (mem_balForms_int.1 hβ)]
    have := h2 β hβ hp
    push_cast
    nlinarith
  · intro j
    rw [hB (γ j) (mem_balForms_int.1 (hγ.mem j))]
    push_cast
    rw [h1 j]
    ring
  · intro β hβ hp he
    rw [hB β (mem_balForms_int.1 hβ)] at he
    push_cast at he
    refine h3 β hβ hp (mul_left_cancel₀ hD0.ne' ?_)
    linear_combination he

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenChartAffineOpenWithin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenChartAffineOpenWithin
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open Matrix

section Alg

theorem exists_factor_idem {L : Type} [Field L] {n m : ℕ} (e : Matrix (Fin n) (Fin n) L) (he : e * e = e)
    (N : Submodule L (Fin n → L)) (hN : ∀ v, v ∈ N ↔ e.mulVec v = v) (hr : Module.finrank L N = m) :
    ∃ (U : Matrix (Fin n) (Fin m) L) (V : Matrix (Fin m) (Fin n) L), U * V = e ∧ V * U = 1 := by
  classical
  let b : Module.Basis (Fin m) L N := Module.finBasisOfFinrankEq L N hr
  have hmem : ∀ v, e.mulVec v ∈ N := fun v => (hN _).2 (by rw [Matrix.mulVec_mulVec, he])
  let P : (Fin n → L) →ₗ[L] N := e.mulVecLin.codRestrict N hmem
  refine ⟨LinearMap.toMatrix' (N.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ P), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (N.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ P) = e.mulVecLin := by
      apply LinearMap.ext
      intro v
      simp [P, LinearMap.codRestrict_apply]
      rfl
    rw [this]
    exact LinearMap.toMatrix'_toLin' e
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ P) ∘ₗ (N.subtype ∘ₗ b.equivFun.symm.toLinearMap) = LinearMap.id := by
      apply LinearMap.ext
      intro a
      have h1 : P (b.equivFun.symm a : N) = b.equivFun.symm a :=
        Subtype.ext ((hN _).1 (b.equivFun.symm a).2)
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Submodule.coe_subtype, h1,
        LinearEquiv.apply_symm_apply, LinearMap.id_coe, id_eq]
    rw [this, LinearMap.toMatrix'_id]

theorem sum_minors_of_factor {T : Type} [CommRing T] {n m : ℕ} (U : Matrix (Fin n) (Fin m) T)
    (V : Matrix (Fin m) (Fin n) T) (h : V * U = 1) :
    ∑ S : Set.powersetCard (Fin n) m,
      ((U * V).submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1 := by
  have h0 := GlobalTheory.det_mul_eq_sum_minors V U
  rw [h, det_one] at h0
  rw [h0]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, det_mul, mul_comm]

theorem det_smul_of_factor {T : Type} [CommRing T] {n m : ℕ} (U : Matrix (Fin n) (Fin m) T)
    (V : Matrix (Fin m) (Fin n) T) (s : Fin m → Fin n) :
    ((U * V).submatrix s s).det • (U * V) =
      (U * V).submatrix id s * ((U * V).submatrix s s).adjugate * (U * V).submatrix s id := by
  rw [Matrix.submatrix_mul _ _ s id s Function.bijective_id, Matrix.submatrix_mul _ _ id id s Function.bijective_id,
    Matrix.submatrix_mul _ _ s id id Function.bijective_id, adjugate_mul_distrib, det_mul]
  simp only [Matrix.submatrix_id_id]
  have e1 : U * V.submatrix id s * ((V.submatrix id s).adjugate * (U.submatrix s id).adjugate) *
      (U.submatrix s id * V) = U * (V.submatrix id s * (V.submatrix id s).adjugate) *
        ((U.submatrix s id).adjugate * U.submatrix s id) * V := by
    simp only [Matrix.mul_assoc]
  rw [e1, mul_adjugate, adjugate_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul, mul_comm]

theorem idem_minors {R L : Type} [CommRing R] [Field L] (φ : R →+* L) (hφ : Function.Injective φ) {n m : ℕ}
    (e : Matrix (Fin n) (Fin n) R) (he : e * e = e) (N : Submodule L (Fin n → L))
    (hN : ∀ v, v ∈ N ↔ (e.map φ).mulVec v = v) (hr : Module.finrank L N = m) :
    (∑ S : Set.powersetCard (Fin n) m, (e.submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1) ∧
      ∀ s : Fin m → Fin n, (e.submatrix s s).det • e = e.submatrix id s * (e.submatrix s s).adjugate *
        e.submatrix s id := by
  obtain ⟨U, V, hUV, hVU⟩ := exists_factor_idem (e.map φ) (by rw [← Matrix.map_mul, he]) N hN hr
  have hdet : ∀ s : Fin m → Fin n, φ (e.submatrix s s).det = ((e.map φ).submatrix s s).det := fun s => by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]
  refine ⟨hφ ?_, fun s => Matrix.map_injective hφ ?_⟩
  · set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one]
    simp only [hdet, ← hUV]
    exact sum_minors_of_factor U V hVU
  · dsimp only
    have h2 := det_smul_of_factor U V s
    rw [hUV] at h2
    have hs : ((e.submatrix s s).det • e).map φ = φ (e.submatrix s s).det • e.map φ := by
      ext i j; simp
    have ha : (e.submatrix s s).adjugate.map φ = ((e.map φ).submatrix s s).adjugate := by
      rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply, Matrix.submatrix_map]
    rw [hs, hdet, h2, Matrix.map_mul, Matrix.map_mul, ← Matrix.submatrix_map, ← Matrix.submatrix_map, ha]

theorem exists_split {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (e : Matrix (Fin n) (Fin n) R)
    (he : e * e = e) (s : Fin m → Fin n)
    (hid : (e.submatrix s s).det • e = e.submatrix id s * (e.submatrix s s).adjugate * e.submatrix s id)
    (φ : R →+* S) (hu : IsUnit (φ (e.submatrix s s).det)) :
    ∃ (u : Matrix (Fin n) (Fin m) S) (w : Matrix (Fin m) (Fin n) S), w * u = 1 ∧ u * w = e.map φ := by
  refine ⟨(e.submatrix id s).map φ,
    (hu.unit⁻¹ : Sˣ).val • ((e.submatrix s s).adjugate * e.submatrix s id).map φ, ?_, ?_⟩
  · have h1 : e.submatrix s id * e.submatrix id s = e.submatrix s s := by
      rw [← Matrix.submatrix_mul _ _ s id s Function.bijective_id, he]
    rw [Matrix.smul_mul, ← Matrix.map_mul, Matrix.mul_assoc, h1, adjugate_mul]
    have hs : ((e.submatrix s s).det • (1 : Matrix (Fin m) (Fin m) R)).map φ =
        φ (e.submatrix s s).det • (1 : Matrix (Fin m) (Fin m) S) := by
      ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hs, smul_smul, IsUnit.val_inv_mul, one_smul]
  · rw [Matrix.mul_smul, ← Matrix.map_mul, ← Matrix.mul_assoc, ← hid]
    have hs : ((e.submatrix s s).det • e).map φ = φ (e.submatrix s s).det • e.map φ := by
      ext i j; simp
    rw [hs, smul_smul, IsUnit.val_inv_mul, one_smul]

end Alg

section Geo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pm_minors (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : MChart Y) (σ : E →+* ℂ) :
    LowRank.pm p M σ * LowRank.pm p M σ = LowRank.pm p M σ ∧
    (∑ S : Set.powersetCard (Fin M.n) (Dw.mult σ),
      ((LowRank.pm p M σ).submatrix (GlobalTheory.subsetEnum S) (GlobalTheory.subsetEnum S)).det = 1) ∧
      ∀ s : Fin (Dw.mult σ) → Fin M.n, ((LowRank.pm p M σ).submatrix s s).det • LowRank.pm p M σ =
        (LowRank.pm p M σ).submatrix id s * ((LowRank.pm p M σ).submatrix s s).adjugate *
          (LowRank.pm p M σ).submatrix s id := by
  obtain ⟨L, _, _, y, h, hy, hi⟩ := LowRank.genIn_id Y M
  obtain ⟨h1, h2⟩ := LowRank.pm_gen p M σ hy h
  have he : LowRank.pm p M σ * LowRank.pm p M σ = LowRank.pm p M σ :=
    Matrix.map_injective hi (Matrix.map_mul.trans h2)
  obtain ⟨Λ⟩ := MChart.nonempty_lift E H Dw l Xo c c.F (RingHom.id c.F) Y M L (ev _ M.U h) y hy
    (spMap_ev _ M.hU h).symm
  let N : Submodule L (Fin M.n → L) := Module.End.eigenspace ((LowRank.pm p M σ).map (ev _ M.U h)).mulVecLin 1
  have hN : ∀ v, v ∈ N ↔ ((LowRank.pm p M σ).map (ev _ M.U h)).mulVec v = v := fun v =>
    Module.End.mem_eigenspace_iff.trans (by rw [one_smul]; rfl)
  exact ⟨he, idem_minors _ hi _ he N hN
    (finrank_chart_eig E H Dw l Xo c c.F (RingHom.id c.F) Y M L _ _ Λ σ N fun v => (hN v).trans (h1 v).symm)⟩

theorem exists_eCh_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : GChart Y)
    (x : Y.X), x ∈ M.U → ∀ W : Y.X.Opens, x ∈ W → ∃ k : ECh Y p, k.M = M ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ W := by
  intro E _ _ _ H Dw l Xo c Y p M x hx W hW
  classical
  have ex : ∀ σ : E →+* ℂ, ∃ s : Fin (Dw.mult σ) → Fin M.n,
      Y.X.evaluation M.U x hx ((LowRank.pm p M.toMChart σ).submatrix s s).det ≠ 0 := fun σ => by
    by_contra h
    push_neg at h
    have := congrArg (Y.X.evaluation M.U x hx) (pm_minors Y p M.toMChart σ).2.1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one, Finset.sum_eq_zero fun S _ => h _] at this
    exact zero_ne_one this
  choose s hs using ex
  let d := fun σ => ((LowRank.pm p M.toMChart σ).submatrix (s σ) (s σ)).det
  have hxf : x ∈ Y.X.basicOpen (∏ σ, d σ) := by
    refine (Y.X.evaluation_ne_zero_iff_mem_basicOpen x hx _).1 ?_
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun σ _ => hs σ
  obtain ⟨g, hg, hxg⟩ := M.hU.exists_basicOpen_le (V := W ⊓ Y.X.basicOpen (∏ σ, d σ)) ⟨x, hW, hxf⟩ hx
  have hle : Y.X.basicOpen g ≤ M.U := Y.X.basicOpen_le g
  have hVf : Y.X.basicOpen g ≤ Y.X.basicOpen (∏ σ, d σ) := hg.trans inf_le_right
  have hf : IsUnit (resG Y.X hle (∏ σ, d σ)) := by
    have h1 : IsUnit (resG Y.X (Y.X.basicOpen_le (∏ σ, d σ)) (∏ σ, d σ)) :=
      RingedSpace.isUnit_res_basicOpen Y.X.toRingedSpace _
    have h2 : resG Y.X hle (∏ σ, d σ) = resG Y.X hVf (resG Y.X (Y.X.basicOpen_le (∏ σ, d σ)) (∏ σ, d σ)) := by
      simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    rw [h2]
    exact h1.map _
  have hu : ∀ σ, IsUnit (resG Y.X hle (d σ)) := fun σ =>
    isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem d (Finset.mem_univ σ))) hf
  choose u w hwu huw using fun σ => exists_split _ (pm_minors Y p M.toMChart σ).1 (s σ)
    ((pm_minors Y p M.toMChart σ).2.2 (s σ)) (resG Y.X hle) (hu σ)
  exact ⟨⟨M, Y.X.basicOpen g, hle, u, w, hwu, huw⟩, rfl, hxg, M.hU.basicOpen g, hg.trans inf_le_left⟩

end Geo

end GlobalTheory.FlagMod.FieldFlag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenChartAffineOpenWithinStatement
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eigenChart_affineOpen_within : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (M : GChart Y) (x : Y.X), x ∈ M.U → ∀ W : Y.X.Opens, x ∈ W → ∃ k : ECh Y p, k.M = M ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ W := by
  first | exact @GlobalTheory.FlagMod.FieldFlag.exists_eCh_le | exact GlobalTheory.FlagMod.FieldFlag.exists_eCh_le | (intros; apply GlobalTheory.FlagMod.FieldFlag.exists_eCh_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledIsoPreservingRigidification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledIsoPreservingRigidification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.RigRescale

variable {X Y : Scheme.{0}}

theorem germ_id_pull (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (f ⁻¹ᵁ U) (pullU f U a) = gm f y U a := by
  rw [gm_pull (𝟙 Y) f y U h a, Category.id_comp]

theorem germ_pull_g (L : LB X) (f : Y ⟶ X) (y : Y) (P P' : PUnit → L.ι)
    (hp : f y ∈ L.U (P PUnit.unit)) (hp' : f y ∈ L.U (P' PUnit.unit)) :
    gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P') ((L.pull f).g P P') =
      gm f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit)) := by
  have hm : y ∈ (L.pull f).U P ⊓ (L.pull f).U P' := ⟨mem_pull.2 hp, mem_pull.2 hp'⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f _ (L.g _ _))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hm _).trans (germ_id_pull f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) ⟨hp, hp'⟩ _)

theorem germ_linCombIso {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X) (y : Y) (P : PUnit → M.ι)
    (Q : PUnit → L.ι) (hp : f y ∈ M.U (P PUnit.unit)) (hq : f y ∈ L.U (Q PUnit.unit)) :
    gm (𝟙 Y) y ((M.pull f).U P ⊓ (L.pull f).U Q)
        ((LB.linCombIso w (K := PUnit) (fun _ => f) (fun _ => 1)).s (P, Q)) =
      gm f y ((LB.div M L).U (P PUnit.unit, Q PUnit.unit)) (w.s (P PUnit.unit, Q PUnit.unit)) := by
  have hm : y ∈ (M.pull f).U P ⊓ (L.pull f).U Q := ⟨mem_pull.2 hp, mem_pull.2 hq⟩
  show gm (𝟙 Y) y _ (∏ _k : PUnit, (res _ (pullU f ((LB.div M L).U (P PUnit.unit, Q PUnit.unit))
    (w.s (P PUnit.unit, Q PUnit.unit)))) ^ (1 : ℤ)) = _
  rw [Fintype.prod_unique, zpow_one]
  exact (gm_res (𝟙 Y) y _ hm _).trans (germ_id_pull f y ((LB.div M L).U (P PUnit.unit, Q PUnit.unit))
    (show f y ∈ M.U (P PUnit.unit) ⊓ L.U (Q PUnit.unit) from ⟨hp, hq⟩) _)

theorem germ_iso_isGen {L M : LB X} (w : LB.Iso L M) (hw : w.IsGen) (f : Y ⟶ X) (y : Y)
    (p p' : M.ι) (q q' : L.ι) (hp : f y ∈ M.U p) (hp' : f y ∈ M.U p') (hq : f y ∈ L.U q)
    (hq' : f y ∈ L.U q') :
    gm f y ((LB.div M L).U (p, q)) (w.s (p, q)) =
      gm f y (M.U p ⊓ M.U p') (M.g p p') * (gm f y (L.U q ⊓ L.U q') (L.g q q'))⁻¹ *
        gm f y ((LB.div M L).U (p', q')) (w.s (p', q')) := by
  have hm : f y ∈ M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q') := ⟨⟨hp, hq⟩, hp', hq'⟩
  have h := (congrArg (gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) (hw (p, q) (p', q'))).trans
    (map_mul (gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q'))) ((LB.div M L).g (p, q) (p', q'))
      (res inf_le_right (w.s (p', q'))))
  have hg : gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')) ((LB.div M L).g (p, q) (p', q')) =
      gm f y (M.U p ⊓ M.U p') (M.g p p') * (gm f y (L.U q ⊓ L.U q') (L.g q q'))⁻¹ := by
    show gm f y _ (res _ (M.g p p') * (res _ (L.g q q'))⁻¹) = _
    rw [map_mul, map_inv]
    exact congrArg₂ (· * ·) (gm_res f y _ hm _) (congrArg _ (gm_res f y _ hm _))
  calc gm f y ((LB.div M L).U (p, q)) (w.s (p, q))
      = gm f y (M.U p ⊓ L.U q ⊓ (M.U p' ⊓ L.U q')) (res inf_le_left (w.s (p, q))) :=
        (gm_res f y _ hm _).symm
    _ = _ := h
    _ = _ := congrArg₂ (· * ·) hg (gm_res f y _ hm _)

theorem germ_gen_isGen (L : LB X) (f : Y ⟶ X) (t : LB.Gen (L.pull f)) (ht : t.IsGen) (y : Y)
    (P P' : PUnit → L.ι) (hp : f y ∈ L.U (P PUnit.unit)) (hp' : f y ∈ L.U (P' PUnit.unit)) :
    gm (𝟙 Y) y ((L.pull f).U P) (t.s P) =
      gm f y (L.U (P PUnit.unit) ⊓ L.U (P' PUnit.unit)) (L.g (P PUnit.unit) (P' PUnit.unit)) *
        gm (𝟙 Y) y ((L.pull f).U P') (t.s P') := by
  have hm : y ∈ (L.pull f).U P ⊓ (L.pull f).U P' := ⟨mem_pull.2 hp, mem_pull.2 hp'⟩
  have h := congrArg (gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P')) (ht P P')
  rw [map_mul] at h
  calc gm (𝟙 Y) y ((L.pull f).U P) (t.s P)
      = gm (𝟙 Y) y ((L.pull f).U P ⊓ (L.pull f).U P') (res inf_le_left (t.s P)) :=
        (gm_res (𝟙 Y) y _ hm _).symm
    _ = _ := h
    _ = _ := by rw [germ_pull_g L f y P P' hp hp']; exact congrArg _ (gm_res (𝟙 Y) y _ hm _)

theorem alg₁ {M : Type*} [CommGroup M] (a b E A B : M) :
    a * A * (a * b⁻¹ * E * (b * B))⁻¹ = A * (E * B)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem alg₂ {M : Type*} [CommGroup M] (A E B : M) : A = E * (A * (E * B)⁻¹) * B := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem proj_comp : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G],
    eSec G ≫ (toUnit G).left = 𝟙 (𝟙_ (Over S)).left := by
  intro S G _
  show (η[G] ≫ toUnit G).left = 𝟙 _
  rw [toUnit_unique (η[G] ≫ toUnit G) (𝟙 _)]
  rfl

theorem exists_isGen_maps_rig {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G]
    (L₁ L₂ : RigLB G) (e : LB.Iso L₁.L L₂.L) (he : e.IsGen) : ∃ e' : LB.Iso L₁.L L₂.L, e'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  let W : (PUnit → L₂.L.ι) × (PUnit → L₁.L.ι) → (𝟙_ (Over S)).left.Opens :=
    fun i => (L₂.L.pull (eSec G)).U i.1 ⊓ (L₁.L.pull (eSec G)).U i.2
  let u : ∀ i, Γ((𝟙_ (Over S)).left, W i)ˣ := fun i =>
    res inf_le_left (L₂.rig.s i.1) *
      ((LB.linCombIso e (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s i *
        res inf_le_right (L₁.rig.s i.2))⁻¹
  have key : ∀ i, ∀ x ∈ W i, gm (𝟙 _) x (W i) (u i) =
      gm (𝟙 _) x ((L₂.L.pull (eSec G)).U i.1) (L₂.rig.s i.1) *
        (gm (eSec G) x ((LB.div L₂.L L₁.L).U (i.1 PUnit.unit, i.2 PUnit.unit))
            (e.s (i.1 PUnit.unit, i.2 PUnit.unit)) *
          gm (𝟙 _) x ((L₁.L.pull (eSec G)).U i.2) (L₁.rig.s i.2))⁻¹ := by
    intro i x hx
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 _) x _ hx _)
      ((map_inv _ _).trans (congrArg _ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
        (germ_linCombIso e (eSec G) x i.1 i.2 (mem_pull.1 hx.1) (mem_pull.1 hx.2))
        (gm_res (𝟙 _) x _ hx _))))))
  obtain ⟨c, hc⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨p, hp⟩ := exists_chart L₂.isLB ((eSec G) x)
      obtain ⟨q, hq⟩ := exists_chart L₁.isLB ((eSec G) x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(fun _ => p, fun _ => q), mem_pull.2 hp, mem_pull.2 hq⟩) u
    (fun i j x hx => by
      rw [key i x hx.1, key j x hx.2,
        germ_gen_isGen L₂.L (eSec G) L₂.rig L₂.rigGen x i.1 j.1 (mem_pull.1 hx.1.1) (mem_pull.1 hx.2.1),
        germ_gen_isGen L₁.L (eSec G) L₁.rig L₁.rigGen x i.2 j.2 (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2),
        germ_iso_isGen e he (eSec G) x _ (j.1 PUnit.unit) _ (j.2 PUnit.unit) (mem_pull.1 hx.1.1)
          (mem_pull.1 hx.2.1) (mem_pull.1 hx.1.2) (mem_pull.1 hx.2.2)]
      exact alg₁ _ _ _ _ _)
  let C := pullU (toUnit G).left ⊤ c
  let e' : LB.Iso L₁.L L₂.L := ⟨fun i => e.s i * res (U := (toUnit G).left ⁻¹ᵁ ⊤) (fun _ _ => trivial) C⟩
  have hC : ∀ i, ∀ x ∈ (LB.div L₂.L L₁.L).U i,
      gm (𝟙 _) x ((LB.div L₂.L L₁.L).U i) (e'.s i) =
        gm (𝟙 _) x ((LB.div L₂.L L₁.L).U i) (e.s i) * gm (𝟙 _) x ((toUnit G).left ⁻¹ᵁ ⊤) C :=
    fun i x hx => (map_mul _ _ _).trans (congrArg _ (gm_res (𝟙 _) x _ hx _))
  refine ⟨e', ?_, ?_⟩
  · rintro ⟨p, q⟩ ⟨p', q'⟩
    apply unit_ext
    intro x hx
    have hE : gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p, q)) (e.s (p, q)) =
        gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p, q) ⊓ (LB.div L₂.L L₁.L).U (p', q'))
            ((LB.div L₂.L L₁.L).g (p, q) (p', q')) *
          gm (𝟙 _) x ((LB.div L₂.L L₁.L).U (p', q')) (e.s (p', q')) :=
      (gm_res (𝟙 _) x _ hx _).symm.trans (((congrArg (gm (𝟙 _) x _) (he (p, q) (p', q'))).trans
        (map_mul _ _ _)).trans (congrArg _ (gm_res (𝟙 _) x _ hx _)))
    exact (gm_res (𝟙 _) x _ hx _).trans ((hC _ x hx.1).trans ((congrArg (· * _) hE).trans
      ((mul_assoc _ _ _).trans ((congrArg _ ((hC _ x hx.2).symm.trans
        (gm_res (𝟙 _) x _ hx _).symm)).trans (map_mul _ _ _).symm))))
  · rintro ⟨P, Q⟩
    apply unit_ext
    intro x hx
    have hx₁ := mem_pull.1 hx.1
    have hx₂ := mem_pull.1 hx.2
    have hcx : gm (𝟙 _) x ⊤ c = gm (𝟙 _) x (W (P, Q)) (u (P, Q)) := by
      rw [← hc (P, Q)]; exact (gm_res (𝟙 _) x _ hx _).symm
    have hσ : gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
        (e'.s (P PUnit.unit, Q PUnit.unit)) =
        gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
          (e.s (P PUnit.unit, Q PUnit.unit)) * gm (𝟙 _) x ⊤ c := by
      refine (map_mul _ _ _).trans (congrArg _ ?_)
      refine (gm_res (eSec G) x _ (show (eSec G) x ∈ L₂.L.U _ ⊓ L₁.L.U _ from ⟨hx₁, hx₂⟩) _).trans ?_
      refine (gm_pull (eSec G) (toUnit G).left x ⊤ trivial c).trans ?_
      rw [proj_comp]
    have hEq : gm (𝟙 _) x (W (P, Q))
        ((LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)).s (P, Q)) =
        gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
            (e.s (P PUnit.unit, Q PUnit.unit)) *
          (gm (𝟙 _) x ((L₂.L.pull (eSec G)).U P) (L₂.rig.s P) *
            (gm (eSec G) x ((LB.div L₂.L L₁.L).U (P PUnit.unit, Q PUnit.unit))
                (e.s (P PUnit.unit, Q PUnit.unit)) *
              gm (𝟙 _) x ((L₁.L.pull (eSec G)).U Q) (L₁.rig.s Q))⁻¹) := by
      rw [germ_linCombIso e' (eSec G) x P Q hx₁ hx₂, hσ, hcx, key (P, Q) x hx]
    exact (gm_res (𝟙 _) x _ hx _).trans ((alg₂ _ _ _).trans
      ((congrArg₂ (· * ·) hEq.symm (gm_res (𝟙 _) x _ hx _).symm).trans (map_mul _ _ _).symm))

end GlobalTheory.RigRescale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledIsoPreservingRigidificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rescaled_iso_preserving_rigidification : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (L₁ L₂ : RigLB G)
    (e : LB.Iso L₁.L L₂.L), e.IsGen → ∃ e' : LB.Iso L₁.L L₂.L, e'.IsGen ∧
      LB.Gen.Maps (LB.linCombIso e' (K := PUnit) (fun _ => eSec G) (fun _ => 1)) L₁.rig L₂.rig := by
  first | exact @GlobalTheory.RigRescale.exists_isGen_maps_rig | exact GlobalTheory.RigRescale.exists_isGen_maps_rig | (intros; apply GlobalTheory.RigRescale.exists_isGen_maps_rig <;> assumption)
end
end
