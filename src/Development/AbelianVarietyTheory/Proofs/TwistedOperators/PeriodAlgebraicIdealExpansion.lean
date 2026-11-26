module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemGfCOfSuppAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftVerticalCuspidalSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongRightGridArrows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongDownGridArrows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicIdealExpansion
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BottomFieldDict

theorem det_X_isHomogeneous {σ : Type*} {a : ℕ} (f : Fin a → Fin a → σ) :
    (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)).det.IsHomogeneous a := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun e _ => ?_)
  have h1 : (∏ i, (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)) (e i) i).IsHomogeneous
      (∑ _i : Fin a, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X ℂ _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
  have h0 : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)).IsHomogeneous 0 := by
    have : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)) = MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : ℂ) := by simp
    rw [this]; exact MvPolynomial.isHomogeneous_C _ _
  simpa using h0.mul h1

theorem minorPol_isHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n) :
    (GlobalTheory.NormSum.minorPol D T).IsHomogeneous (a * ∑ τ, n τ) := by
  unfold GlobalTheory.NormSum.minorPol
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset D.what₂.Tau)
    (fun τ => ∏ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, ((T τ j) : Fin a → Fin d) i, i') :
      MvPolynomial (GL3Theta.Idx D a d) ℂ)).det) (fun τ => ∑ _j : Fin (n τ), a) (fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => det_X_isHomogeneous _))
  convert h using 1
  simp [Finset.mul_sum, mul_comm]

theorem card_of_mem_support {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n)
    {α : TaylorLogMetric.Mono D a d} (hα : α ∈ (GlobalTheory.NormSum.minorPol D T).support) :
    Multiset.card (Finsupp.toMultiset α) = a * ∑ τ, n τ := by
  have h := minorPol_isHomogeneous T (MvPolynomial.mem_support_iff.mp hα)
  rw [Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

theorem minorPol_coeff_isAlgebraic {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : GlobalTheory.NormSum.Tup D a d n)
    (α : GL3Theta.Idx D a d →₀ ℕ) : IsAlgebraic ℚ ((GlobalTheory.NormSum.minorPol D U).coeff α) := by
  have e : GlobalTheory.NormSum.minorPol D U = MvPolynomial.map (algebraMap ℚ ℂ) (∏ τ, ∏ j, (Matrix.of fun i i' : Fin a =>
      (MvPolynomial.X (τ, (U τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℚ)).det) := by
    unfold GlobalTheory.NormSum.minorPol
    simp only [map_prod, RingHom.map_det]
    refine Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun j _ => ?_
    congr 1
    ext1 i i'
    simp
  rw [e, MvPolynomial.coeff_map]
  exact isAlgebraic_algebraMap _

theorem apply_minorPol {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (U : GlobalTheory.NormSum.Tup D a d n)
    (l : MvPolynomial (GL3Theta.Idx D a d) ℂ →ₗ[ℂ] ℂ) (c p ζ : ℂ) (G : TaylorLogMetric.VC D a d → ℂ)
    (h : ∀ k : GL3Theta.Idx D a d →₀ ℕ, l (MvPolynomial.monomial k 1) =
      c * (p ^ (k.sum fun _ e => e) * (ζ * GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) G))) :
    l (GlobalTheory.NormSum.minorPol D U) = c * p ^ (a * ∑ τ, n τ) * (ζ * GL3Theta.applyAt0 D (GlobalTheory.NormSum.minorPol D U) G) := by
  conv_lhs => rw [(GlobalTheory.NormSum.minorPol D U).as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum l, GL3Theta.applyAt0, Finset.mul_sum _ _ ζ, Finset.mul_sum _ _ (c * p ^ (a * ∑ τ, n τ))]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := card_of_mem_support U hα
  rw [Finsupp.card_toMultiset] at hk
  have e : (MvPolynomial.monomial α ((GlobalTheory.NormSum.minorPol D U).coeff α) : MvPolynomial (GL3Theta.Idx D a d) ℂ) =
      (GlobalTheory.NormSum.minorPol D U).coeff α • MvPolynomial.monomial α 1 := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hk' : (α.sum fun _ e => e) = a * ∑ τ, n τ := hk
  rw [e, map_smul, h, GlobalTheory.FockPos.applyAt0_monomial', hk', smul_eq_mul]
  ring

theorem lat_eq_colLat {D : D7} {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) :
    (r.Λ : Set (Fin V.rank → D.host.E)) = (colLat (1 : GL (Fin V.rank) D.host.E) : Set (Fin V.rank → D.host.E)) := by
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, h.2.1, lc_mem_colLat_one]
  simp only [Submodule.mem_one]

theorem lat_eq_inV {D : D7} {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (h : r.IsStd) :
    (r.Λ : Set (Fin V.rank → D.host.E)) = GlobalTheory.MovedDict.inV 1 (StandardLatticesGL3.stdL D V.rank) := by
  ext y
  rw [SetLike.mem_coe, h.2.1]
  simp [GlobalTheory.MovedDict.inV, StandardLatticesGL3.stdL, Submodule.mem_pi, Submodule.mem_one]

end GlobalTheory.BottomFieldDict

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualGridRowMovedLatticeLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualGridRowMovedLatticeLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

theorem mem_spanSingleton_mul_iff {s x : D.host.E} (hs : s ≠ 0) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
    x ∈ FractionalIdeal.spanSingleton _ s * I ↔ x * s⁻¹ ∈ I := by
  rw [FractionalIdeal.mem_singleton_mul]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [mul_comm, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  · intro h
    exact ⟨x * s⁻¹, h, by rw [mul_comm, mul_assoc, inv_mul_cancel₀ hs, mul_one]⟩

theorem tiltSc_ne_zero (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p ≠ 0 := by
  unfold tiltSc
  split_ifs
  · exact inv_ne_zero (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact star_ne_zero.2 (pow_ne_zero _ cmHost_imaginaryGenerator_ne_zero)
  · exact one_ne_zero

theorem tiltSc_mul_star_rev (j : ℕ) (p : Fin (D.R.m - 1 - j)) : tiltSc D j p * star (tiltSc D j p.rev) = 1 := by
  have hx : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  obtain ⟨a, ha⟩ := D.R.m_even
  have hp := p.2
  unfold tiltSc
  by_cases hj : Odd j
  · obtain ⟨b, hb⟩ := hj
    have hj' : Odd j := ⟨b, hb⟩
    rw [if_pos hj', if_pos hj', Fin.val_rev]
    by_cases h1 : 2 * p.1 < D.R.m - 1 - j
    · rw [if_pos h1, if_neg (by omega)]
      have e : D.R.m - 1 - j - 1 - (D.R.m - 1 - j - (p.1 + 1)) = p.1 := by omega
      rw [e, star_star, inv_mul_cancel₀ (pow_ne_zero _ hx)]
    · rw [if_neg h1, if_pos (by omega)]
      have e : D.R.m - 1 - j - (p.1 + 1) = D.R.m - 1 - j - 1 - p.1 := by omega
      rw [e, star_inv₀, mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hx))]
  · rw [if_neg hj, if_neg hj, star_one, one_mul]

theorem rowId_ne_zero_and_dual (j : ℕ) (p : Fin (D.R.m - 1 - j)) :
    rowId D j p ≠ 0 ∧ ∀ x, x ∈ rowId D j p.rev ↔ star x ∈ (rowId D j p)⁻¹ := by
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨h0, hd⟩ := GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj (D.R.m - 1 - j) p
  have hs := tiltSc_ne_zero (D := D) j p
  have hs' := tiltSc_ne_zero (D := D) j p.rev
  refine ⟨mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hs) h0, fun x => ?_⟩
  unfold rowId
  rw [mul_inv, FractionalIdeal.spanSingleton_inv, mem_spanSingleton_mul_iff hs', mem_spanSingleton_mul_iff (inv_ne_zero hs),
    inv_inv, hd, star_mul', star_inv₀]
  have e : (star (tiltSc D j p.rev))⁻¹ = tiltSc D j p := by
    exact inv_eq_of_mul_eq_one_left (tiltSc_mul_star_rev j p)
  rw [e]

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem isSelfDualC_rowN (G : GridData L sc) (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (rowN G j) := by
  unfold rowN
  split_ifs with h
  · refine GlobalTheory.ChiGrid.SumDual.isSelfDualC_lat D _ _ _ _ (G.rowDec j h) _ _ (Or.inr rfl)
      (G.isV (X := .top j) hj (fun _ h' => by cases h')).sd (fun p => (rowId_ne_zero_and_dual j p).1)
      (fun p x => (rowId_ne_zero_and_dual j p).2 x)
  · exact (G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ (fun _ h' => by
      have := D.R.two_le_m
      injection h' with h1; omega)).sd

end GlobalTheory.RowShape

theorem GlobalTheory.RowShape.big_isSelfDualC_rowN :
    Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j ≤ D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G j) :=
  ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ j hj => GlobalTheory.RowShape.isSelfDualC_rowN ch.G j hj⟩⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualGridRowMovedLatticeLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSelfDual_gridRowMovedLattice_largeDepth : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j, j ≤ D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G j) := by
  first | exact @GlobalTheory.RowShape.big_isSelfDualC_rowN | exact GlobalTheory.RowShape.big_isSelfDualC_rowN | (intros; apply GlobalTheory.RowShape.big_isSelfDualC_rowN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelOfSplitPlaceThetaFun
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelOfSplitPlaceThetaFun
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

namespace GlobalTheory.LocMod.Witness

theorem exists_isModel_of_isThetaAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), (∀ x, p.up FS FT x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔ ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation k)) → ∀ f₀ φ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ φ f → ∃ Tm, p.IsModel ψ FS FT Tm ∧ (∀ O, IsOne O → Tm O = f₀) ∧ ∃ Φ : SB (Matrix Y Y' k), (∀ x, Φ.1 x = φ (p.up FS FT x)) ∧ Tm Φ = f := by
  classical
  intro D k _ _ _ _ p ψ hψ S T ΛS ΛT hS hT Y Y' _ _ _ _ FS FT hlat f₀ φ f hf₀ hφ hθ
  obtain ⟨⟨T₀, h₀⟩, hall⟩ := hθ
  have hf : f = T₀ φ := hall T₀ h₀

  have hNk : ∀ N : ℕ, 0 < N → (N : k) ≠ 0 := fun N hN h => by
    have h1 : prH p (N : D.host.E) = 0 := by rw [map_natCast]; exact h
    have h2 : (N : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    exact h2 ((map_eq_zero (prH p)).1 h1)
  obtain ⟨N, hN, hinv, hsupp⟩ := hφ.2
  have hN0 := hNk N hN
  have hA := lat_compact p FS FT hS hT
  have hAo := lat_open p FS FT hS hT
  generalize hAd : ((latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True).comap (upH p FS FT) : AddSubgroup _) = A at hA hAo
  have memA : ∀ x, x ∈ A ↔ p.up FS FT x ∈ (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := fun x => by
    rw [← hAd]; rfl
  have hup_smul : ∀ x : Matrix Y Y' k, p.up FS FT (N • x) = N • p.up FS FT x := fun x => map_nsmul (upH p FS FT) N x
  have hNx : ∀ x : Matrix Y Y' k, (N : k) • x = N • x := fun x => Nat.cast_smul_eq_nsmul k N x

  let g : Matrix Y Y' k → ℂ := fun x => φ (p.up FS FT x)
  have hlc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hU : IsOpen ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) :=
      hAo.preimage ((continuous_const_smul ((N : k)⁻¹)).comp (continuous_id.sub continuous_const))
    have hx : x ∈ ((fun y : Matrix Y Y' k => (N : k)⁻¹ • (y - x)) ⁻¹' (A : Set (Matrix Y Y' k))) := by
      simp only [Set.mem_preimage, sub_self, smul_zero]; exact A.zero_mem
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy' : (N : k)⁻¹ • (y - x) ∈ A := hy
    have e1 : y = x + N • ((N : k)⁻¹ • (y - x)) := by
      rw [← hNx, smul_smul, mul_inv_cancel₀ hN0, one_smul, add_sub_cancel]
    change φ (p.up FS FT y) = φ (p.up FS FT x)
    rw [e1, up_add, hup_smul]
    exact hinv _ ((memA _).1 hy') (up_half p FS FT _) _
  have hcs : HasCompactSupport g := by
    refine HasCompactSupport.intro (hA.image (continuous_const_smul (N : k)⁻¹)) fun x hx => ?_
    by_contra h
    apply hx
    have h1 := hsupp _ h
    rw [← hup_smul, ← memA] at h1
    refine ⟨N • x, h1, ?_⟩
    change (N : k)⁻¹ • (N • x) = x
    rw [← hNx, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let Φ : SB (Matrix Y Y' k) := ⟨g, hlc, hcs⟩

  have hext : ∀ Ψ : SB (Matrix Y Y' k), IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) (ext p FS FT Ψ) :=
    ext_sb p FS FT hS hT
  refine ⟨T₀.comp (ext p FS FT), ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩, fun O hO => ?_, Φ, fun x => rfl, ?_⟩
  · exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ S T _ _ hS hT p.e p.split.1 (GlobalTheory.PlaceCoord.infPart_split p.split)
      _ hf₀ T₀ h₀ _ (hext Ψ)
  · refine Eq.trans (congrArg T₀ ?_) (h₀.trans _ (hext Ψ) _ (up_half p FS FT x))
    funext t
    rw [ext_apply, ext_apply, down_add, down_up, h]
    exact if_congr (half_add (up_half p FS FT x)).symm rfl rfl
  · refine Eq.trans (congrArg T₀ ?_) (h₀.modul _ (hext Ψ) _ hy)
    funext t
    rw [ext_apply, ext_apply, h]
    split_ifs with ht
    · rw [up_down p FS FT ht]
    · rw [mul_zero]
  · have e1 : ext p FS FT O = (1 : ℂ) • halfInd p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) := by
      funext t
      rw [one_smul, ext_apply, halfInd]
      by_cases ht : IsHalf p.e t
      · rw [if_pos ht, hO, Set.indicator_apply]
        refine if_congr ?_ rfl rfl
        rw [and_iff_left ht, ← up_down p FS FT ht, down_up, hlat]
        rfl
      · rw [if_neg ht, if_neg fun h => ht h.2]
    change T₀ (ext p FS FT O) = f₀
    rw [e1]
    exact h₀.vac
  · change T₀ (ext p FS FT Φ) = f
    rw [hf]
    congr 1
    funext t
    rw [ext_apply]
    split_ifs with ht
    · change φ (p.up FS FT (p.down FS FT t)) = φ t
      rw [up_down p FS FT ht]
    · by_contra h
      exact ht (hφ.1 t (Ne.symm h))

end GlobalTheory.LocMod.Witness
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalModelOfSplitPlaceThetaFunStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localModel_of_splitPlaceThetaFun : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y), (∀ x, p.up FS FT x ∈ latO S T (ΛS : Set _) (ΛT : Set _) (fun _ => True) ↔ ∀ a b, x a b ∈ Valuation.integer (ValuativeRel.valuation k)) → ∀ f₀ φ f : WO S T → ℂ, IsThetaFunO ψ S T f₀ → IsSBHalf p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) p.e (latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) 1 f₀ φ f → ∃ Tm, p.IsModel ψ FS FT Tm ∧ (∀ O, IsOne O → Tm O = f₀) ∧ ∃ Φ : SB (Matrix Y Y' k), (∀ x, Φ.1 x = φ (p.up FS FT x)) ∧ Tm Φ = f := by
  first | exact @GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt | exact GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt | (intros; apply GlobalTheory.LocMod.Witness.exists_isModel_of_isThetaAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.RowShape

variable {D : D7}

theorem nLine_gram (D : D7) : (GlobalTheory.SeeSaw.Model.nLine D).gram = -1 := by
  refine Matrix.ext fun i j => ?_
  refine (congrArg Neg.neg (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral 1
    (fun _ => false) 1 0 i j)).trans ?_
  rw [Matrix.neg_apply, Matrix.one_apply]
  by_cases h : i = j <;> simp [h, Formalism.BasicNotions.Examples₂.sgn] <;> first | exact rfl | exact fun e => h e

theorem mem_latPi {S : HSp D} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {y : Fin S.rank → D.host.E} :
    y ∈ latPi S I ↔ ∀ i, y i ∈ I := by
  simp [latPi, Submodule.mem_pi]

theorem isSelfDualC_latPi {S : HSp D} (hg : S.gram = -1) {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hI : I ≠ 0)
    (hII : I * GlobalTheory.SeeSaw.conjFI D I = 1) : IsSelfDualC S (latPi S I) := by
  set J := GlobalTheory.SeeSaw.conjFI D I with hJdef
  have hJ : J ≠ 0 := fun h => hI (by rw [h, mul_zero] at hII; exact absurd hII.symm one_ne_zero)
  have hstar : ∀ x : D.host.E, star x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hmemJ : ∀ x : D.host.E, x ∈ J ↔ star x ∈ I := fun x => by rw [hstar]; exact GlobalTheory.SeeSaw.mem_conjFI
  have hpair : ∀ x y : Fin S.rank → D.host.E, ∑ a, ∑ b, star (x a) * S.gram a b * y b = -∑ a, star (x a) * y a := by
    intro x y
    rw [hg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [Matrix.neg_apply, Matrix.one_apply, Ne.symm hb]
    · simp
  have hIeq : I = J⁻¹ := eq_inv_of_mul_eq_one_left hII
  obtain ⟨a0, ha0, ha00⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hI (by
      ext x
      rw [FractionalIdeal.mem_zero_iff]
      exact ⟨hcon x, fun h => h ▸ Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)⟩)
  refine ⟨⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl _, ?_⟩, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · intro s _ hs
    exact (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp hs
  · rw [hpair]
    have hy' := mem_latPi.1 hy
    have hx' := mem_latPi.1 hx
    have hs : -∑ a, star (x a) * y a ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => ?_)
      rw [← hII, mul_comm]
      exact FractionalIdeal.mul_mem_mul ((hmemJ _).2 (by rw [star_star]; exact hx' a)) (hy' a)
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hs
    exact ⟨b, by rw [RingOfIntegers.coe_eq_algebraMap]; exact hb⟩
  · refine mem_latPi.2 fun i => ?_
    rw [hIeq, FractionalIdeal.mem_inv_iff hJ]
    intro t ht
    have hx : (Pi.single i (star t) : Fin S.rank → D.host.E) ∈ latPi S I := mem_latPi.2 fun k => by
      by_cases hk : k = i
      · subst hk; simpa using (hmemJ t).1 ht
      · rw [Pi.single_eq_of_ne hk]; exact Submodule.zero_mem (I : Submodule (𝓞 D.host.E) D.host.E)
    obtain ⟨b, hb⟩ := h _ hx
    rw [hpair, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)] at hb
    simp only [Pi.single_eq_same, star_star] at hb
    refine (FractionalIdeal.mem_one_iff _).2 ⟨-b, ?_⟩
    rw [map_neg, ← RingOfIntegers.coe_eq_algebraMap, hb, mul_comm]
    ring

theorem conjFI_AAbar (D : D7) : GlobalTheory.SeeSaw.conjFI D D.host.AAbar = D.host.AA := by
  rw [← GlobalTheory.SeeSaw.conjFI_AA]
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_conj_host]

theorem lineId_ne_zero (D : D7) (j : ℕ) : lineId D j ≠ 0 := by
  have hA := GlobalTheory.FinPl.LocGen.AA_ne_zero D
  have hB : D.host.AAbar ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero _).2 hA
  exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

theorem lineId_mul_conj (D : D7) (j : ℕ) : lineId D j * GlobalTheory.SeeSaw.conjFI D (lineId D j) = 1 := by
  have hA := GlobalTheory.FinPl.LocGen.AA_ne_zero D
  have hB : D.host.AAbar ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero _).2 hA
  unfold lineId
  rw [map_mul, map_inv₀, map_pow, map_pow, GlobalTheory.SeeSaw.conjFI_AA, conjFI_AAbar]
  have hA' := pow_ne_zero ((D.R.m - 2 - j) / 2 + 1) hA
  have hB' := pow_ne_zero ((D.R.m - 2 - j) / 2 + 1) hB
  field_simp

theorem coreL_selfDual_split : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ, j + 2 * σ + 2 = D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.lineL D j) ∧
    IsSelfDualC _ (GlobalTheory.RowShape.coreL ch.G j) ∧ ∀ v, GlobalTheory.FinPl.OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (GlobalTheory.RowShape.coreL ch.G j) (ch.G.Λ (.top j)) (GlobalTheory.RowShape.lineL D j) v := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj
  have hL : IsSelfDualC _ (lineL D j) := isSelfDualC_latPi (nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (ch.G.Λ (.top j)) :=
    (ch.G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  exact ⟨hL, GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL,
    fun v => GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v⟩

end GlobalTheory.RowShape
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegLineLatticeAndBesselCoreLatticeSelfDualSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negLineLattice_and_besselCoreLattice_selfDual_split : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ, j + 2 * σ + 2 = D.R.m → IsSelfDualC _ (GlobalTheory.RowShape.lineL D j) ∧
    IsSelfDualC _ (GlobalTheory.RowShape.coreL ch.G j) ∧ ∀ v, GlobalTheory.FinPl.OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (GlobalTheory.RowShape.coreL ch.G j) (ch.G.Λ (.top j)) (GlobalTheory.RowShape.lineL D j) v := by
  first | exact @GlobalTheory.RowShape.coreL_selfDual_split | exact GlobalTheory.RowShape.coreL_selfDual_split | (intros; apply GlobalTheory.RowShape.coreL_selfDual_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorsRowAndColumnPaths
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links Formalism.L2.DIV GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.FlipRun GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf

variable {T : Type}

theorem splitFam_zip {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : (p.comp q).Fam S) (e : (p.comp q).Fam S'),
      splitFam q (Path.Fam.zip φ d e) =
        (Path.Fam.zip φ (splitFam q d).1 (splitFam q e).1, Path.Fam.zip φ (splitFam q d).2 (splitFam q e).2)
  | _, .nil, _, _ => rfl
  | _, .snoc _ q, d, e => by
    show ((splitFam q (Path.Fam.zip φ d.1 e.1)).1, ((splitFam q (Path.Fam.zip φ d.1 e.1)).2, φ _ d.2 e.2)) = _
    rw [splitFam_zip φ q d.1 e.1]
    rfl

theorem getD_zip {S S' S'' : Arrow T → Type} (φ : ∀ a, S a → S' a → S'' a) (t : T) (i : ℕ) :
    ∀ (n : ℕ) (d : (downPath t i n).Fam S) (e : (downPath t i n).Fam S') (j : ℕ) (h : j < n),
      getD t i n (Path.Fam.zip φ d e) j h = φ _ (getD t i n d j h) (getD t i n e j h)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, e, j, h => by
    have hs : splitFam (p := Path.one (.down t i n)) (downPath t i n)
        (Path.Fam.zip (p := downPath t i (n + 1)) φ d e) =
        (Path.Fam.zip φ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1
          (splitFam (p := Path.one (.down t i n)) (downPath t i n) e).1,
         Path.Fam.zip φ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).2
          (splitFam (p := Path.one (.down t i n)) (downPath t i n) e).2) :=
      splitFam_zip φ (p := Path.one (.down t i n)) (downPath t i n) d e
    unfold getD
    split_ifs with hj
    · rw [hs]
      exact getD_zip φ t i n _ _ j hj
    · have hnj : n = j := by omega
      subst j
      change (splitFam (downPath t i n) (Path.Fam.zip φ d e)).1.2 =
        φ _ (splitFam (downPath t i n) d).1.2 (splitFam (downPath t i n) e).1.2
      exact congrArg (fun de => de.1.2) hs

variable {D : D7} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem vecAll_iff {W : G.Weil} (ρ : RealMatch W) (e : AE D) {X : Node} :
    ∀ {Y : Node} (p : Path T X Y) (φ f : PureT G p), VecAll ρ e p φ f ↔
      Path.Fam.All (fun a (x : Sch G a × Sch G a) => IsLocVec W a.pair e (vacOf ρ a) x.1 x.2)
        (Path.Fam.zip (fun _ u v => (u, v)) φ f)
  | _, .nil, _, _ => Iff.rfl
  | _, .snoc _ p, φ, f => and_congr_left' (vecAll_iff ρ e p φ.1 f.1)

theorem getD_loc {W : G.Weil} (ρ : RealMatch W) (e : AE D) (t : T) (i n : ℕ) (φ f : PureT G (downPath t i n))
    (h : VecAll ρ e (downPath t i n) φ f) (j : ℕ) (hj : j < n) :
    IsLocVec W (Arrow.down t i j).pair e (vacOf ρ (.down t i j)) (getD t i n φ j hj) (getD t i n f j hj) := by
  have := getD_all (fun a (x : Sch G a × Sch G a) => IsLocVec W a.pair e (vacOf ρ a) x.1 x.2) t i n _
    ((vecAll_iff ρ e _ φ f).1 h) j hj
  rwa [getD_zip] at this

theorem row_cusp {W : G.Weil} {M : Vol G} {ρ : RealMatch W} {t : T} (hS : CuspStep W M ρ t) {e : AE D}
    (he : IsIdemSum e (locPl G t)) {F : Fn G (.grid 0 D.R.m)} (hF : IsCuspListed W.θ (.grid 0 D.R.m) F) :
    ∀ n, n ≤ D.R.m → ∀ (φ d : PureT G (rowPath T D.R.m n)) (P : PolT G (rowPath T D.R.m n)),
      VecAll ρ e (rowPath T D.R.m n) φ d →
      IsCuspListed W.θ (.grid n D.R.m)
        (liftP W M (rowPath T D.R.m n) (Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d P) F)
  | 0, _, _, _, _, _ => hF
  | n + 1, hn, φ, d, P, h =>
    (hS (.right n D.R.m) (Or.inl ⟨n, D.R.m, by omega, le_rfl, rfl⟩) e he φ.2 d.2 h.2 P.2 _
      (row_cusp hS he hF n (by omega) φ.1 d.1 P.1 h.1)).2

theorem step_cusp (G : GridData L sc) (Wl : G.Weil) (t : T) {M : Vol G} (hM : M.Is t) {θ : InfFam D} (j : ℕ)
    (hj : j + 1 ≤ D.R.m) {V₀ W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec (G.V (.grid D.R.m j)) V₀ ρ)
    (dW : HypDec (G.V (.grid D.R.m (j + 1))) W₀ σ) (Φ : Sch G (.down t D.R.m j)) (F : Fn G (.grid D.R.m (j + 1)))
    (h : IsCuspListed θ (.grid D.R.m j) (liftA Wl M (.down t D.R.m j) Φ F)) :
    IsCuspListed θ (.grid D.R.m j) ((stepAt G Wl t hM j hj dV dW).lift F Φ) := h

end GlobalTheory.ChainHyp

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.RowUnf GlobalTheory.FlipRun GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf

variable {T : Type} {D : D7} {L : LevCh D T} {sc : Consts}

theorem last_cusp (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G) {θ : InfFam D} (j : ℕ)
    (f : Sch G (.down t D.R.m (j + 1)))
    (H : ∀ F' : Fn G (.grid D.R.m (j + 1 + 1)), IsCuspListed θ (.grid D.R.m (j + 1 + 1)) F' →
      IsCuspListed θ (.grid D.R.m (j + 1)) (liftA Wl M (.down t D.R.m (j + 1)) f F')) :
    ∀ (n : ℕ) (h : j + 1 + 1 = n) (F : Fn G (.grid D.R.m n)), IsCuspListed θ (.grid D.R.m n) F →
      IsCuspListed θ (.grid D.R.m (j + 1))
        (liftS (castOm G h (Wl.om (.mu t D.R.m (j + 1)))) (M.ν (.grid D.R.m n)) (M.fd (.grid D.R.m n)) F (castSch G h f)) := by
  intro n h
  subst h
  exact H

theorem chain_props (hP : GlobalTheory.Published.CuspRapidDecay) (G : GridData L sc) (Wl : G.Weil) (hθ : IsInfFam Wl.θ) (t : T)
    {M : Vol G} (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsCuspListed Wl.θ (.grid D.R.m D.R.m) F)
    (hst : ∀ k (hk : k < D.R.m) (F' : Fn G (.grid D.R.m (k + 1))), IsCuspListed Wl.θ (.grid D.R.m (k + 1)) F' →
      IsCuspListed Wl.θ (.grid D.R.m k) (liftA Wl M (.down t D.R.m k) (getD t D.R.m D.R.m d k hk) F')) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)),
      IsCuspListed Wl.θ (.grid D.R.m j) ((chainFrom G Wl t hM σ j hj vN).down (dataFrom G Wl t hM d σ j hj vN) F) ∧
      (chainFrom G Wl t hM σ j hj vN).Rapid (dataFrom G Wl t hM d σ j hj vN) F
  | 0, j, hj, vN => by
    refine ⟨?_, trivial⟩
    exact step_cusp G Wl t hM j (by omega) (besDecAt G j 0 hj) (rowJac G (j + 1) (by omega) 0 (by omega)) _ _ (hst j (by omega) _
      (last_cusp G Wl t M j _ (hst (j + 1) (by omega)) D.R.m (by omega) F hF))
  | σ + 1, j, hj, vN => by
    have hj' : (j + 1 + 1) + 2 * σ + 2 = D.R.m := by omega
    have hrec := chain_props hP G Wl hθ t hM d F hF hst σ (j + 1 + 1) hj'
      (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ hj')).some
    rcases hrec with ⟨h1, h2⟩
    have h3 := step_cusp G Wl t hM (j + 1) (by omega)
      (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
      (getD t D.R.m D.R.m d (j + 1) (by omega)) _ (hst (j + 1) (by omega) _ h1)
    refine ⟨step_cusp G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) _ _
      (hst j (by omega) _ h3), ?_⟩
    exact ⟨rapidDec_of_cuspForm hP hθ h3.1 h3.2.1, rapidDec_of_cuspForm hP hθ h1.1 h1.2.1, h2⟩

end GlobalTheory.ChainHyp

namespace GlobalTheory.ChainHyp

open GlobalTheory.FunObj GlobalTheory.RowChain GlobalTheory.FlipRun GlobalTheory.Grow

end GlobalTheory.ChainHyp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegerIffOfEquiv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open Filter Topology

namespace GlobalTheory.PlaceSplitPt

section Val

variable {K K' : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field K'] [ValuativeRel K'] [TopologicalSpace K'] [IsNonarchimedeanLocalField K']

theorem tendsto_pow_zero {x : K} (h : valuation K x < 1) : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' K).tendsto_right_iff]
  intro γ hγ
  have : MulArchimedean (ValueGroupWithZero K) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 γ hγ)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_mem_nhds : {y : K' | valuation K' y < 1} ∈ 𝓝 (0 : K') :=
  (IsValuativeTopology.hasBasis_nhds_zero' K').mem_iff.2 ⟨1, one_ne_zero, fun _ hy => hy⟩

theorem lt_one_of_map (i : K →+* K') (hi : Continuous i) {x : K} (h : valuation K x < 1) :
    valuation K' (i x) < 1 := by
  have h1 : Tendsto (fun n : ℕ => i x ^ n) atTop (𝓝 0) := by
    have := (hi.tendsto 0).comp (tendsto_pow_zero h)
    simpa [Function.comp_def, map_pow] using this
  obtain ⟨N, hN⟩ := (h1.eventually lt_one_mem_nhds).exists
  by_contra hc
  push_neg at hc
  have : 1 ≤ valuation K' (i x ^ N) := by rw [map_pow]; exact one_le_pow₀ hc
  exact absurd hN (not_lt.2 this)

theorem le_one_of_map (i : K →+* K') (hi : Continuous i) {y : K} (h : valuation K' (i y) ≤ 1) :
    valuation K y ≤ 1 := by
  by_contra hc
  push_neg at hc
  have hy : y ≠ 0 := fun h0 => by simp [h0] at hc
  have h1 : valuation K y⁻¹ < 1 := by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc
  have h2 := lt_one_of_map i hi h1
  rw [map_inv₀, map_inv₀] at h2
  have h0 : (0 : ValueGroupWithZero K') < valuation K' (i y) := by
    rw [zero_lt_iff, Valuation.ne_zero_iff]
    exact (map_ne_zero i).2 hy
  exact absurd h (not_le.2 ((inv_lt_one₀ h0).1 h2))

theorem mem_integer_iff_of_equiv (σ : K ≃+* K') (h1 : Continuous σ) (h2 : Continuous σ.symm) (a : K) :
    a ∈ 𝒪[K] ↔ σ a ∈ 𝒪[K'] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff]
  constructor
  · intro h
    refine le_one_of_map σ.symm.toRingHom h2 ?_
    change valuation K (σ.symm (σ a)) ≤ 1
    rwa [σ.symm_apply_apply]
  · exact le_one_of_map σ.toRingHom h1

end Val

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke GlobalTheory.LocMod

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ι_mul (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]

section Chart

variable {v : Pl D} (p : Place D k) (he : SplitAt D v p.e)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def toFv : k ≃+* Fv D.host.F v where
  toFun a := comp he (p.ι a)
  invFun b := p.π (sec D v p.e b)
  left_inv a := by
    change p.π (sec D v p.e (comp he (p.ι a))) = a
    rw [GlobalTheory.LocMod.SplitCompl.sec_comp, Witness.e_ι, p.π_ι]
  right_inv b := by
    change comp he (p.ι (p.π (sec D v p.e b))) = b
    rw [p.ι_π, map_mul, comp_self, one_mul, GlobalTheory.LocMod.SplitCompl.comp_sec]
  map_mul' x y := by
    change comp he (p.ι (x * y)) = comp he (p.ι x) * comp he (p.ι y)
    rw [ι_mul, map_mul]
  map_add' x y := by
    change comp he (p.ι (x + y)) = comp he (p.ι x) + comp he (p.ι y)
    rw [map_add (f := _), map_add (f := _)]

theorem continuous_toFv : Continuous (toFv p he) := (continuous_comp he).comp p.cont_ι

theorem continuous_toFv_symm : Continuous (toFv p he).symm := p.cont_π.comp continuous_sec

include he in
theorem int_iff (a : k) : a ∈ 𝒪[k] ↔ finPart D (p.ι a) ∈ intAE D := by
  rw [mem_integer_iff_of_equiv (toFv p he) (continuous_toFv p he) (continuous_toFv_symm p he) a,
    GlobalTheory.LocMod.SplitCompl.int_iff_sec he]
  change finPart D (sec D v p.e (comp he (p.ι a))) ∈ intAE D ↔ _
  rw [GlobalTheory.LocMod.SplitCompl.sec_comp, Witness.e_ι]

end Chart

theorem exists_splitPt : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.LocMod.Place D k), ∃ q : GlobalTheory.FinPl.SplitPt D k, GlobalTheory.LocMod.Place.ofSplitPt q = p := by
  intro D k _ _ _ _ p
  obtain ⟨-, -, v, ε, hε, hs⟩ := p.split
  have he : SplitAt D v p.e := splitAt_of p.split hε hs
  exact ⟨⟨v, p.e, p.split, ⟨ε, hε, hs⟩, p.π, p.ι, p.π_ι, p.ι_π, p.cont_π, p.cont_ι, int_iff p he⟩, rfl⟩

end GlobalTheory.PlaceSplitPt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPtAtPlace


set_option maxHeartbeats 1000000 in
theorem exists_splitPt_cpt : ∀ (D : D7) (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → D.host.F = maximalRealSubfield D.host.E → ∃ p : GlobalTheory.FinPl.SplitPt D (Kw w), p.e = e ∧ p.v = w.under (𝓞 D.host.F) ∧ ∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a)) := by
  intro D w e he hF
  obtain ⟨s, hsw⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D w
    (GlobalTheory.OffBad.isSplitPl_of_isSplit D w (GlobalTheory.DivPtLocal.isSplit_of_isIdemAt D w e he))
  subst hsw
  obtain ⟨p, c, hpl, hc, hci, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D s hF
  obtain ⟨q, hq⟩ := GlobalTheory.PlaceSplitPt.exists_splitPt p
  have hqe : q.e = p.e := by rw [← hq]; rfl
  have hqpr : ∀ a, q.pr a = p.π a := fun a => by rw [← hq]; rfl
  have hpe : Formalism.L2.NTheta.IsIdemAt p.e s.w := ⟨p.split, hpl.2.2⟩
  have hee : p.e = e := GlobalTheory.LocMod.PinInhab.idem_unique hpe he
  refine ⟨q, hqe.trans hee, GlobalTheory.LocMod.PinInhab.v_eq_under q (hqe ▸ hpe), fun a => ?_⟩
  rw [hqpr, hπ]
  have key := GlobalTheory.SplitFrameW.cpt_swap D.host.F hF ((GlobalTheory.StdFrames.toAd D).comp (Lev.swapAE D))
    (fun a x => GlobalTheory.StdFrames.toAd_spec D x a) s c hc hci (GlobalTheory.NJoin.tensCast hF (finPart D a))
  rw [← key]
  have hcast : GlobalTheory.NJoin.tensCast hF = GlobalTheory.Mem.R3.swapCast hF := rfl
  rw [hcast, RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.SplitPtAtPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmSplitPoint_at_place_over_split : ∀ (D : D7) (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → D.host.F = maximalRealSubfield D.host.E → ∃ p : GlobalTheory.FinPl.SplitPt D (Kw w), p.e = e ∧ p.v = w.under (𝓞 D.host.F) ∧ ∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a)) := by
  first | exact @GlobalTheory.SplitPtAtPlace.exists_splitPt_cpt | exact GlobalTheory.SplitPtAtPlace.exists_splitPt_cpt | (intros; apply GlobalTheory.SplitPtAtPlace.exists_splitPt_cpt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentMemHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentMemHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LineCompLat

variable {D : D7}

theorem rat_mulVec_tmul {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (t : AF D.host.F) (x : Fin n → D.host.E) :
    rat M *ᵥ (fun l => t ⊗ₜ[D.host.F] (1 * x l)) = fun k => t ⊗ₜ[D.host.F] (1 * (M *ᵥ x) k) := by
  funext k
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, one_mul, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  change ((1 : AF D.host.F) ⊗ₜ[D.host.F] M k l) * (t ⊗ₜ[D.host.F] x l) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem rat_mulVec_latV {S S' : HSp D} {L : Lat S} {L' : Lat S'} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin S'.rank) (Fin S.rank) D.host.E) (hM : ∀ x ∈ L, M *ᵥ x ∈ L')
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) : rat M *ᵥ y ∈ latV S' L' P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [rat_mulVec_tmul]
    exact AddSubgroup.subset_closure ⟨α, hαi, hα, 1, rfl, M *ᵥ x, hM x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem mxAt_mul_left {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} (B : Mx D k m) {A : Mx D m n} (hA : MxAt P A) :
    MxAt P (B * A) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hA l j)

theorem mxAt_mul_right {P : GlobalTheory.FinPl.Pl D → Prop} {k m n : ℕ} {A : Mx D k m} (hA : MxAt P A) (C : Mx D m n) :
    MxAt P (A * C) := fun i j => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hA i l)

end GlobalTheory.LineCompLat

open GlobalTheory.LineCompLat

theorem GlobalTheory.AscFin.BoxBF.lineComp_mem_latO : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
  intro D hD T L μ0 hL sc G W Mv hM F hF ρ h u hu
  obtain ⟨hsd0, hloc, hsdM, horth⟩ := (GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W Mv hM F hF).2.1 ρ h
  have sdV : IsSelfDualC (negSp (G.V (.grid (2 * ρ + 1 + 1) 0))) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) :=
    isSelfDualC_neg (G.sp.V_is (2 * ρ + 1 + 1) 0 (by omega) h (by omega)).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (G.sp.V_is (2 * ρ + 1) 0 (by omega) (by omega) (by omega)).sd
  have sdC : IsSelfDualC (G.V (.core (2 * ρ + 1))) (G.Λ (.core (2 * ρ + 1))) :=
    (G.sp.P_is (2 * ρ + 1) (by omega)).sd
  have hU1 : (F.dJ ρ h).j0 * u * (F.dB ρ h).p0 ∈ latRow G (2 * ρ + 1) := hu
  have hU := hU1.1
  dsimp only [GridData.pS, GridData.pT, GridData.latS, GridData.latT] at hU
  clear hU1 hu
  have hu' : u = (F.dJ ρ h).p0 * ((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) * (F.dB ρ h).j0 := by
    simp only [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [OrthDec.resS_apply]
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hsdM sdC _ _).2 ⟨?_, fun z hz => ?_⟩
  · rw [hu']
    exact mxAt_mul_right (mxAt_mul_right (mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hU)) _) _
  have h1 : (F.oB ρ h).jB *ᵥ z ∈ latV (F.V₀ ρ) (lat0 F ρ h) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local hsdM.1 hsd0.1 (F.oB ρ h).jB (fun v _ y hy => ?_) hz
    refine ((horth v) _).2 ⟨?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, OrthDec.pA_jB, Matrix.zero_mulVec]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, OrthDec.pB_jB, Matrix.one_mulVec]; exact hy
  have h2 : (F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z) ∈
      latV (negSp (G.V (.grid (2 * ρ + 1 + 1) 0))) (G.Λ (.grid (2 * ρ + 1 + 1) 0)) fun _ => True :=
    rat_mulVec_latV (F.dB ρ h).i₀ (fun x hx => hx) h1
  have h3 := GlobalTheory.FinPl.LatMem.latO_maps sdV hU h2
  have h4 : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) ∈
      latA _ (G.Λ (.core (2 * ρ + 1))) fun _ => True := by
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latA (F.dJ ρ h).p0 (fun y hy => ?_) h3
    refine GlobalTheory.FinPl.FlatVacuum.mulVec_latV_of_local sdW.1 sdC.1 (F.dJ ρ h).p0 (fun v _ y' hy' => ?_) hy
    exact (((hloc v).2 y').1 hy').2.2
  have e : (F.dJ ρ h).p0 *ᵥ (((F.dJ ρ h).j0 * u * (F.dB ρ h).p0) *ᵥ ((F.dB ρ h).j0 *ᵥ ((F.oB ρ h).jB *ᵥ z))) =
      (u * (F.oB ρ h).jB) *ᵥ z := by
    simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
    rw [Matrix.mul_assoc u, HypDec.p0_j0, Matrix.mul_one]
  rw [← e]
  exact h4
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentMemHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_step_line_component_mem_hom_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F ρ h).Γ₀, ((F.oB ρ h).resS (G.V (.core (2 * ρ + 1))) u).2 ∈ latO (negSp F.Lz) (G.V (.core (2 * ρ + 1))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) : Set _) (G.Λ (.core (2 * ρ + 1)) : Set _) fun _ => True := by
  first | exact @GlobalTheory.AscFin.BoxBF.lineComp_mem_latO | exact GlobalTheory.AscFin.BoxBF.lineComp_mem_latO | (intros; apply GlobalTheory.AscFin.BoxBF.lineComp_mem_latO <;> assumption)
end
end
