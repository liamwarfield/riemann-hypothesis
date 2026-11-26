module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAlgebraicIdealExpansion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVacuumCombinationLocalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CombinationProducesDatumAllLocalModels
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CombinationProducesDatumAllLocalModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.FlatPlace.CombAll

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']

theorem exists_form (p : Place D k) {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {y : WO S T}
    (hy : IsHalf (cA D p.e) y) : ∃ b : Matrix Y Y' k, ∀ t, p.π (hO S T (p.up FS FT t) y) = ∑ r, ∑ q, b r q * t r q := by
  set N : Matrix (Fin S.rank) (Fin T.rank) k := (y.map fun a => p.π (cA D a)).transpose with hN
  have hyN : y = N.transpose.map fun a => cA D (p.ι a) := by
    ext i j
    simp only [hN, Matrix.transpose_transpose, Matrix.map_apply, p.ι_π, map_mul, Formalism.L2.Theta.cA_cA]
    exact (hy i j).symm
  refine ⟨(FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β).transpose, fun t => ?_⟩
  rw [hyN, GlobalTheory.LocSympl.pi_hO_up]
  rw [show (S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * (FT.β * t * FS.γ) =
      ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) * FS.γ by
    simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  rw [show FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D)) * FT.β * t) =
      (FS.γ * ((S.gram⁻¹).map (p.π.comp (incA D)) * N * T.gram.map (p.π.comp (incA D))) * FT.β) * t by
    simp only [Matrix.mul_assoc]]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem exists_heis (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (O : SB (Matrix Y Y' k)) {u : WO S T}
    (hu : IsHalf (p.e + cA D p.e) u) :
    ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O) := by
  obtain ⟨⟨ψk, hψk⟩, hcn, -, -, -⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ hψ
  obtain ⟨hcont, hne⟩ := hcn ψk hψk
  obtain ⟨d, hd⟩ := exists_hasConductor_of_continuous ψk hcont hne
  have h1 := p.split.1
  have h1' : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, h1]
  set x := p.down FS FT u with hx
  set y : WO S T := cA D p.e • u with hyd
  have hy : IsHalf (cA D p.e) y := fun i j => by
    simp only [hyd, Matrix.smul_apply, smul_eq_mul]
    rw [← mul_assoc, h1']
  have hux : p.up FS FT x = p.e • u := by
    rw [hx]
    unfold Place.down Place.up
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, FT.βγ, Matrix.one_mul, Matrix.mul_assoc, FS.βγ, Matrix.mul_one]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact p.ι_π _
  have hsum : y + p.up FS FT x = u := by
    rw [hux]
    ext i j
    simp only [hyd, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← add_mul, add_comm]
    exact hu i j
  obtain ⟨b, hb⟩ := exists_form p FS FT hy
  let Φx : SB (Matrix Y Y' k) := ⟨fun t => O.1 (t + x), GlobalTheory.LocComb.trans_mem_SB O.2 x⟩
  let Φm : SB (Matrix Y Y' k) := ⟨fun t => GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t, GlobalTheory.LocComb.modul_mem_SB hd Φx.2 b⟩
  refine ⟨ψ (-symplOH S T y (p.up FS FT x)) • Φm, fun Tm h => ?_⟩
  have e1 : Tm Φx = heisO ψ S T (p.up FS FT x) (Tm O) := h.trans x O Φx fun _ => rfl
  have e2 : Tm Φm = heisO ψ S T y (Tm Φx) := h.modul y hy Φx Φm fun t => by
    show GlobalTheory.LocMod.Inhab.pairing ψk t b * Φx.1 t = _
    rw [GlobalTheory.LocSympl.psi_sympl_up p FS FT ψ ψk hψk t y, hb t]
    rfl
  have e3 := GlobalTheory.PlaceModel.heisL_heisL S T ψ y (p.up FS FT x) (Tm O)
  change heisO ψ S T y (heisO ψ S T (p.up FS FT x) (Tm O)) =
    ψ (symplOH S T y (p.up FS FT x)) • heisO ψ S T (y + p.up FS FT x) (Tm O) at e3
  rw [map_smul, e2, e1, e3, smul_smul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_smul, hsum]

end GlobalTheory.FlatPlace.CombAll

namespace GlobalTheory.FlatPlace

theorem isCombAt_of_one : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, IsHalf (p.e + cA D p.e) u) → ∀ T₀, p.IsModel ψ FS FT T₀ → ∀ O Ξ : SB (Matrix Y Y' k), IsOne O → T₀ O ≠ 0 → T₀ Ξ = comb ψ S T c (T₀ O) → p.IsCombAt ψ FS FT c Ξ.1 := by
  intro D k _ _ _ _ p ψ hψ S T Y Y' _ _ _ _ FS FT c hc T₀ hT₀ O Ξ hO hT₀O hΞ
  classical
  have hA : ∀ u : c.support, ∃ Φ : SB (Matrix Y Y' k), ∀ Tm, p.IsModel ψ FS FT Tm → Tm Φ = heisO ψ S T u (Tm O) :=
    fun u => CombAll.exists_heis p ψ hψ FS FT O (hc u u.2)
  choose Φ hΦ using hA
  let Ξ' : SB (Matrix Y Y' k) := ∑ u : c.support, c u • Φ u
  have hΞ' : ∀ Tm, p.IsModel ψ FS FT Tm → Tm Ξ' = comb ψ S T c (Tm O) := fun Tm h => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Ξ', map_sum, map_smul, fun u => hΦ u Tm h]
    rw [GlobalTheory.HeisComb.comb_eq_sum, Finsupp.sum]
    exact Finset.sum_coe_sort c.support (fun u => c u • heisO ψ S T u (Tm O))
  have hinj : Ξ = Ξ' := by
    by_contra hne
    have h0 : Ξ - Ξ' ≠ 0 := sub_ne_zero.2 hne
    have e1 : T₀ (Ξ - Ξ') = ((0 : ℂ) • T₀) (Ξ - Ξ') := by
      rw [map_sub, hΞ, hΞ' T₀ hT₀, sub_self, LinearMap.smul_apply, zero_smul]
    have e2 := (GlobalTheory.LocModU.localModel_uniq_transport_exist D k p Y Y' S T FS FT ψ hψ).1 T₀ ((0 : ℂ) • T₀) hT₀
      (GlobalTheory.LocMod.Witness.isModel_smul p hT₀ 0) _ h0 e1
    apply hT₀O
    rw [e2, zero_smul, LinearMap.zero_apply]
  refine ⟨hc, fun Tm h Φ₀ Φ' h1 h2 => ?_⟩
  have e2 : Φ' = Ξ' := by rw [← hinj]; exact Subtype.ext h2
  have e3 : Φ₀ = O := Subtype.ext (h1.trans hO.symm)
  rw [e2, e3, hΞ' Tm h]

end GlobalTheory.FlatPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CombinationProducesDatumAllLocalModelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.combination_produces_datum_all_localModels : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (c : WO S T →₀ ℂ), (∀ u ∈ c.support, IsHalf (p.e + cA D p.e) u) → ∀ T₀, p.IsModel ψ FS FT T₀ → ∀ O Ξ : SB (Matrix Y Y' k), IsOne O → T₀ O ≠ 0 → T₀ Ξ = comb ψ S T c (T₀ O) → p.IsCombAt ψ FS FT c Ξ.1 := by
  first | exact @GlobalTheory.FlatPlace.isCombAt_of_one | exact GlobalTheory.FlatPlace.isCombAt_of_one | (intros; apply GlobalTheory.FlatPlace.isCombAt_of_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVacuumCombinationLocalModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

theorem GlobalTheory.FlatPlace.eventually_combination_of_lattice : Big fun ch => LatP ch → CombP ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  intro hLat t w hw p hp j hj d c hde hc
  have hr : (Pair.top t j : Pair T).InRange D.R.m := hj
  obtain ⟨f₀, hf₀⟩ := exists_isVac ch.W hL hr
  have hf0 : f₀ ≠ 0 := by
    intro h0
    obtain ⟨⟨q, hq⟩, hn⟩ := hf₀.2.norm
    have := hn q hq
    rw [h0] at this
    simp [nrm2] at this
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  have hth := hc.2.2 f₀ hf₀.2.theta hf₀.2.lat
  have sdS := (node_isV ch.G hL (X := .top j) hj.le).sd
  have sdT := (node_isV ch.G hL (X := .top (j + 1)) hj).sd
  have hsb := d.sb
  have hth' : FinDatum.IsTheta ch.W d _ _ f₀ _ := hth
  unfold FinDatum.IsTheta at hth'
  rw [hde] at hsb hth'
  obtain ⟨Tm, hTm, hO, Φ, hΦ, hTΦ⟩ := GlobalTheory.T.exists_localModel_of_splitPlaceThetaFun D (Kw w) p ch.W.ψ hψ _ _ _ _ sdS sdT _ _
    (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) ((hLat t w hw p hp j hj).2) f₀ d.fn _
    hf₀.2.theta hsb hth'
  obtain ⟨O, hO1, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Kw w) (Y := Fin (topRank (locGrid ch.G t w) (j + 1))) (Y' := Fin (topRank (locGrid ch.G t w) j))
  have hhalf := hc.2.1
  rw [hde] at hhalf
  refine ⟨Φ, hΦ, GlobalTheory.T.combination_produces_datum_all_localModels D (Kw w) p ch.W.ψ hψ _ _ _ _ _ _ c hhalf Tm hTm O Φ hO1 ?_ ?_⟩
  · rw [hO O hO1]; exact hf0
  · rw [hTΦ, hO O hO1]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVacuumCombinationLocalModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeVacuumCombination_localModel : Big fun ch => LatP ch → CombP ch := by
  first | exact @GlobalTheory.FlatPlace.eventually_combination_of_lattice | exact GlobalTheory.FlatPlace.eventually_combination_of_lattice | (intros; apply GlobalTheory.FlatPlace.eventually_combination_of_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLastVectorMemHomLatticeIffIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLastVectorMemHomLatticeIffIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct nonZeroDivisors

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.RowShape.LastBF

open GlobalTheory.GoodPos GlobalTheory.FinPl.LatMem

variable {D : D7}

theorem mem_completedHomLattice_iff_selfDual_source {S T : HSp D} {LS : Lat S} (LT : Lat T) (hS : IsSelfDualC S LS) (P : Pl D → Prop) (u : WO S T) :
    u ∈ latO S T (LS : Set _) (LT : Set _) P ↔
      MxAt P u ∧ ∀ y ∈ latV S LS P, Matrix.mulVec (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) y ∈ latA T LT P := by
  refine ⟨fun hu => ⟨latO_mxAt hu, fun y hy => latO_maps hS hu hy⟩, fun ⟨hP, hmap⟩ => ?_⟩
  obtain ⟨m, s, s', hs, hs', hdual⟩ := exists_dualBasis S hS
  let yv : Fin m → Fin S.rank → AE D := fun i l => pairA D.host.F 0 (indP D.host.F P) ⊗ₜ[D.host.F] (1 * s i l)
  have hyv : ∀ i, yv i ∈ latV S LS P := fun i =>
    AddSubgroup.subset_closure ⟨indP D.host.F P, indicatorAdele_mem_integralAdeles' _ _, indicatorAdele_supported _ _, 1, rfl, s i, hs i, rfl⟩
  have hu : u = ∑ i, rowMul S T (s' i) (u *ᵥ yv i) := by
    ext k j
    simp only [Matrix.sum_apply, rowMul, Matrix.of_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, yv]
    simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← TensorProduct.tmul_sum, hdual]
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]; exact (mul_indP (hP k j)).symm
    · intro l _ hl; rw [if_neg hl, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hu]
  exact sum_mem fun i _ => rowMul_mem (hs' i) (hmap _ (hyv i))

theorem last_of_line {V₀ W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (z : Fin V₀.rank → D.host.E) {M : Lat V₀} (LW : Lat W)
    (hM : IsSelfDualC V₀ M) {x : Pl D} {m : (AE D)ˣ} (r : Fin ρ) (hr : r.1 + 1 = ρ)
    (hW : ∀ t ∈ idAt D (· = x), colMul d.jY r t ∈ latA W LW (· = x) ↔
      incA D D.host.xi0 * cA D (m : AE D) * t ∈ intAt D (· = x))
    (hz : ∀ a ∈ idAt D (· = x), a • ratV z ∈ latV V₀ M (· = x) ↔ ((m⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) :
    ∀ a ∈ idAt D (· = x),
      d.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (M : Set _) (LW : Set _) (· = x) ↔ a ∈ intAt D (· = x) := fun a ha => by
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V₀ M x hM
  have hmx : MxAt (· = x) (d.incAdj V₀ (a • yZero V₀ ρ z)) :=
    mxAt_mul _ (mxAt_smul _ (mxAt_mul' _ (mxAt_adj fun i j => Ideal.mul_mem_right _ _ ha)))
  rw [mem_completedHomLattice_iff_selfDual_source LW hM, and_iff_right hmx]
  have h1 := hz _ (Ideal.mul_mem_left _ (m : AE D) ha)
  rw [Units.inv_mul_cancel_left,
    hsd.2.2 (((m : AE D) * a) • ratV z) fun i => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ha)] at h1
  rw [← h1]
  refine forall₂_congr fun y hy => ?_
  rw [incAdj_yZero_mulVec d _ hr, hW _ (Ideal.mul_mem_left _ _ (GlobalTheory.IwaPlace.LocSD.hermAt_mem_idAt (hsd.1 y hy) _)),
    ← herm_conj V₀ y (((m : AE D) * a) • ratV z), int_conj, mul_smul]
  have e1 := herm_smul V₀ 1 m y (a • ratV z)
  rw [one_smul] at e1
  rw [e1]
  have e3 : incA D D.host.xi0 * incA D D.host.xi0⁻¹ = 1 := (xiU D).mul_inv
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D m * GlobalTheory.IwaPlace.hermAt V₀ y (a • ratV z)) * e3

theorem const_mem_latPi {S : HSp D} (i₀ : Fin S.rank) (I : FI D) (v : Pl D) (s : AE D) :
    (fun _ => s) ∈ latV S (latPi S I) (· = v) ↔ s ∈ idV I v := by
  constructor
  · intro hy
    have key : ∀ y ∈ latV S (latPi S I) (· = v), y i₀ ∈ idV I v := fun y hy => by
      induction hy using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨α, hα, h0, a, rfl, z, hz, rfl⟩ := hy
        exact AddSubgroup.subset_closure ⟨α, hα, h0, z i₀, mem_latPi.1 hz i₀, by simp only [one_mul]⟩
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | neg a _ ha => exact neg_mem ha
    exact key _ hy
  · intro hs
    induction hs using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, h0, z, hz, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨α, hα, h0, 1, rfl, fun _ => z, mem_latPi.2 fun _ => hz,
        funext fun i => by rw [one_mul]⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha

theorem AA_mul_rowId (j τ : ℕ) (hj : j + 2 * (τ + 1) + 2 = D.R.m) (p : Fin (D.R.m - 1 - (j + 1))) (hp : p.1 = τ + 1) :
    D.host.AA * rowId D (j + 1) p = FractionalIdeal.spanSingleton _ (star (D.host.xi0 ^ τ)) * lineId D j := by
  have hodd : Odd (j + 1) := by
    obtain ⟨k, hk⟩ := D.R.m_even
    exact ⟨k - τ - 2, by omega⟩
  unfold rowId tiltSc lineId stairId
  rw [if_pos hodd, if_neg (by omega), show D.R.m - 1 - (j + 1) - 1 - p.1 = τ by omega,
    show D.R.m - 1 - (j + 1) - p.1 = τ + 1 by omega, show (D.R.m - 2 - j) / 2 = τ + 1 by omega, hp,
    pow_succ D.host.AA (τ + 1)]
  ring

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem last_rowN (G : GridData L sc) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (v : Pl D) (hσ : 0 < σ) :
    ∀ a ∈ idAt D (· = v),
    (rowJac G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (G.V (.grid D.R.m (j + 1)))
        (coreL G j : Set _) (rowN G (j + 1) : Set _) (· = v) ↔ a ∈ intAt D (· = v) := by
  obtain ⟨τ, rfl⟩ : ∃ τ, σ = τ + 1 := ⟨σ - 1, by omega⟩
  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hL : IsSelfDualC _ (lineL D j) :=
    isSelfDualC_latPi (GlobalTheory.RowShape.nLine_gram D) (lineId_ne_zero D j) (lineId_mul_conj D j)
  have hX : IsSelfDualC _ (G.Λ (.top j)) :=
    (G.isV (X := .top j) (show j ≤ D.R.m by omega) (fun _ h => by cases h)).sd
  have hM : IsSelfDualC _ (coreL G j) := GlobalTheory.Core.Rk.SumBox.selfDual_sumLatO D _ _ _ _ _ _ hX hL
  have ho : OrthAt (GlobalTheory.OrthSumExists.orthDecHsum D (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (coreL G j) (G.Λ (.top j)) (lineL D j) v := GlobalTheory.Core.Rk.SumSplit.orthAt_sumLatO D _ _ _ _ _ _ v
  obtain ⟨g, hg, hgen⟩ := GlobalTheory.IdVGen.idV_gen D v (lineId D j) (lineId_ne_zero D j)
  have hx : D.host.xi0 ^ (τ + 1) ≠ 0 := pow_ne_zero _ hξ
  have hm0 : g * (D.host.xi0 ^ (τ + 1))⁻¹ ≠ 0 := mul_ne_zero hg (inv_ne_zero hx)
  have hline : ∀ a ∈ idAt D (· = v),
      a • ratV (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ∈
        latV (GlobalTheory.SeeSaw.Model.nLine D) (lineL D j) (· = v) ↔
      (((inU _ hm0)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = v) := fun a ha => by
    refine (const_mem_latPi (S := GlobalTheory.SeeSaw.Model.nLine D) (0 : Fin 1) (lineId D j) v
      (a * incA D (D.host.xi0 ^ (τ + 1)))).trans ?_
    rw [hgen, and_iff_left (Ideal.mul_mem_right _ _ ha), inU_inv, mul_inv, inv_inv, RingHom.map_mul, mul_assoc, mul_comm a]
  have hU := line_norm (GlobalTheory.SeeSaw.Model.isLineVec_nLine hx) hL hline
  have hN : star (fun _ : Fin (GlobalTheory.SeeSaw.Model.nLine D).rank => D.host.xi0 ^ (τ + 1)) ⬝ᵥ
      (GlobalTheory.SeeSaw.Model.nLine D).gram *ᵥ (fun _ => D.host.xi0 ^ (τ + 1)) =
      -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) := by
    rw [GlobalTheory.RowShape.nLine_gram, neg_mulVec, one_mulVec, dotProduct_neg]
    exact congrArg Neg.neg (Fin.sum_univ_one (fun _ : Fin 1 => star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)))
  rw [hN] at hU
  refine last_of_line _ _ _ hM (m := inU _ hm0) (Fin.last τ) rfl (fun t ht => ?_)
    (fun a ha => (orth_line _ ho _ a).symm.trans (hline a ha))
  have hc : colMul (rowJac G (j + 1) (by omega) (τ + 1) (by omega)).jY (Fin.last τ) t =
      fun k => t * incA D ((G.rowDec (j + 1) (by omega)).a k
        (Fin.castLE (by omega : τ + 1 ≤ D.R.m - 1 - (j + 1)) (Fin.last τ)).rev) := by
    funext k
    rfl
  have hs : star (D.host.xi0 ^ τ) ≠ 0 := star_ne_zero.2 (pow_ne_zero _ hξ)
  rw [hc, rowN, dite_eq_left (by omega), (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2,
    AA_mul_rowId j τ hj _ (by simp only [Fin.val_rev, Fin.val_castLE, Fin.val_last]; omega),
    idV_spanSingleton_mul_iff D v _ _ hs t, and_iff_left ht, hgen, and_iff_left (Ideal.mul_mem_left _ _ ht),
    hU _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ ht)), inU_val]
  have e : g * (D.host.xi0 ^ (τ + 1))⁻¹ * -(star (D.host.xi0 ^ (τ + 1)) * D.host.xi0 ^ (τ + 1)) *
      (g⁻¹ * (star (D.host.xi0 ^ τ))⁻¹) = D.host.xi0 := by
    rw [pow_succ D.host.xi0 τ, star_mul, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg]
    have := pow_ne_zero τ hξ
    field_simp
  have e' := congrArg (incA D) e
  rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul (incA D) g⁻¹] at e'
  refine iff_of_eq (congrArg (· ∈ _) ?_)
  linear_combination (cA D (incA D (g * (D.host.xi0 ^ (τ + 1))⁻¹)) * t) * e'

end GlobalTheory.RowShape.LastBF

theorem GlobalTheory.RowShape.big_last_rowN : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) :=
  ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ j σ hj v hσ =>
    GlobalTheory.RowShape.LastBF.last_rowN ch.G j σ hj v hσ⟩⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLastVectorMemHomLatticeIffIntegralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLastVector_mem_homLattice_iff_integral : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ j σ (hj : j + 2 * σ + 2 = D.R.m) v, 0 < σ → ∀ a ∈ GlobalTheory.FinPl.idAt D (· = v),
    (rowJac ch.G (j + 1) (by omega) σ (by omega)).incAdj (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D))
      (a • yZero (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ
        (vecB (GlobalTheory.OrthSumExists.orthDecHsum D (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) fun _ => D.host.xi0 ^ σ)) ∈
      latO (GlobalTheory.Doubling.hsum (ch.G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) (ch.G.V (.grid D.R.m (j + 1)))
        (GlobalTheory.RowShape.coreL ch.G j : Set _) (GlobalTheory.RowShape.rowN ch.G (j + 1) : Set _) (· = v) ↔ a ∈ GlobalTheory.FinPl.intAt D (· = v) := by
  first | exact @GlobalTheory.RowShape.big_last_rowN | exact GlobalTheory.RowShape.big_last_rowN | (intros; apply GlobalTheory.RowShape.big_last_rowN <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsetPlaceVectorsAndSteps
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsetPlaceVectorsAndSteps
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SubsetVecs

open GlobalTheory.FinPl.PutIn

variable {D : D7} {S T : HSp D} {ι : Type} [DecidableEq ι]

def prodD (a : ι → AE D) (Ψ : ι → WO S T → ℂ) (s : Finset ι) (y : WO S T) : ℂ :=
  if IsHalf (∑ w ∈ s, a w) y then ∏ w ∈ s, Ψ w (a w • y) else 0

theorem sum_mul_zero {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) {s : Finset ι} {w : ι} (hw : w ∉ s) :
    (∑ v ∈ s, a v) * a w = 0 := by
  rw [Finset.sum_mul]
  exact Finset.sum_eq_zero fun v hv => ho v w fun h => hw (h ▸ hv)

theorem prodD_empty (a : ι → AE D) (Ψ : ι → WO S T → ℂ) (Λ : AddSubgroup (WO S T)) :
    prodD a Ψ ∅ = halfInd 0 Λ := by
  funext y
  unfold prodD halfInd
  rw [Finset.sum_empty, Finset.prod_empty]
  by_cases h : IsHalf (0 : AE D) y
  · rw [if_pos h, if_pos ⟨(GlobalTheory.VecProd.isHalf_zero_iff y).1 h ▸ Λ.zero_mem, h⟩]
  · rw [if_neg h, if_neg fun h' => h h'.2]

theorem prodD_insert {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (Ψ : ι → WO S T → ℂ) {s : Finset ι} {w : ι}
    (hw : w ∉ s) : prodD a Ψ (insert w s) = tens (a w) (prodD a Ψ s) (Ψ w) := by
  funext y
  have h0 := sum_mul_zero ho hw
  have hiff : IsHalf (a w + ∑ v ∈ s, a v) y ↔ IsHalf (∑ v ∈ s, a v) (y - a w • y) :=
    GlobalTheory.VecProd.isHalf_add_iff h0 y
  have hp : ∏ v ∈ s, Ψ v (a v • (y - a w • y)) = ∏ v ∈ s, Ψ v (a v • y) :=
    Finset.prod_congr rfl fun v hv => by
      rw [smul_sub, smul_smul, ho v w fun h => hw (h ▸ hv), zero_smul, sub_zero]
  rw [tens_apply]
  unfold prodD
  rw [Finset.sum_insert hw, Finset.prod_insert hw, hp]
  by_cases h : IsHalf (a w + ∑ v ∈ s, a v) y
  · rw [if_pos h, if_pos (hiff.1 h), mul_comm]
  · rw [if_neg h, if_neg fun h' => h (hiff.2 h'), zero_mul]

theorem prodD_congr (a : ι → AE D) {Ψ Ψ' : ι → WO S T → ℂ} {s : Finset ι} (h : ∀ w ∈ s, Ψ w = Ψ' w) :
    prodD a Ψ s = prodD a Ψ' s := by
  funext y
  unfold prodD
  rw [Finset.prod_congr rfl fun w hw => congrFun (h w hw) _]

theorem prodD_sb {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (hi : ∀ w, a w * a w = a w)
    {Λ : AddSubgroup (WO S T)} (hΛ : ∀ w, ∀ u ∈ Λ, a w • u ∈ Λ) {Ψ : ι → WO S T → ℂ}
    (hΨ : ∀ w, IsSBHalf (a w) Λ (Ψ w)) (s : Finset ι) : IsSBHalf (∑ w ∈ s, a w) Λ (prodD a Ψ s) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prodD_empty a Ψ Λ, Finset.sum_empty]
    exact GlobalTheory.isSBHalf_halfInd _ _
  | insert w s hw ih =>
    rw [prodD_insert ho Ψ hw, Finset.sum_insert hw, add_comm]
    exact Factor.isSBHalf_tens (sum_mul_zero ho hw) (hi w) (hΛ w) ih (hΨ w)

theorem prodD_ind {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0) (hi : ∀ w, a w * a w = a w)
    {Λ : AddSubgroup (WO S T)} (hΛ : ∀ w, ∀ u ∈ Λ, a w • u ∈ Λ) (s : Finset ι) :
    prodD a (fun w => halfInd (a w) Λ) s = halfInd (∑ w ∈ s, a w) Λ := by
  induction s using Finset.induction_on with
  | empty => rw [prodD_empty a _ Λ, Finset.sum_empty]
  | insert w s hw ih =>
    rw [prodD_insert ho _ hw, Finset.sum_insert hw, add_comm, ih]
    have h := HalfOff.tens_vac (sum_mul_zero ho hw) (hi w) Λ (hΛ w)
    rwa [one_smul, one_smul] at h

theorem exists_chain [Fintype ι] {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a : ι → AE D} (ho : ∀ v w, v ≠ w → a v * a w = 0)
    (hi : ∀ w, a w * a w = a w) (hinf : ∀ w, infPart D (a w) = 0) {Ψ : ι → WO S T → ℂ}
    (hΨ : ∀ w, IsSBHalf (a w) (latO S T ΛS ΛT fun _ => True) (Ψ w)) {f₀ f : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) (∑ w, a w) (latO S T ΛS ΛT fun _ => True) 1 f₀
      (prodD a Ψ Finset.univ) f) :
    ∃ V : Finset ι → WO S T → ℂ, V ∅ = f₀ ∧ V Finset.univ = f ∧ (∀ s, IsThetaFunO ψ S T (V s)) ∧
      ∀ s w, w ∉ s → IsThetaAt ψ (symplO S T) (heisO ψ S T) (a w) (latO S T ΛS ΛT fun _ => True) 1 (V s) (Ψ w)
        (V (insert w s)) := by
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hf
  have hΛ : ∀ w, ∀ u ∈ (latO S T ΛS ΛT fun _ => True), a w • u ∈ (latO S T ΛS ΛT fun _ => True) :=
    fun w u hu => GlobalTheory.CosetRow.smul_mem_latO_idem _ _ (hi w) hu
  let mix : Finset ι → ι → WO S T → ℂ := fun s w =>
    if w ∈ s then Ψ w else halfInd (a w) (latO S T ΛS ΛT fun _ => True)
  have hmix : ∀ s w, IsSBHalf (a w) (latO S T ΛS ΛT fun _ => True) (mix s w) := fun s w => by
    by_cases h : w ∈ s
    · simp only [mix, if_pos h]; exact hΨ w
    · simp only [mix, if_neg h]; exact GlobalTheory.isSBHalf_halfInd _ _
  have hV0 : Tm (prodD a (mix ∅) Finset.univ) = f₀ := by
    rw [prodD_congr a (Ψ' := fun w => halfInd (a w) (latO S T ΛS ΛT fun _ => True))
      (fun w _ => if_neg (Finset.notMem_empty w)), prodD_ind ho hi hΛ]
    have h := hTm.vac
    rwa [one_smul] at h
  have hstep : ∀ s w, w ∉ s → IsThetaAt ψ (symplO S T) (heisO ψ S T) (a w) (latO S T ΛS ΛT fun _ => True) 1
      (Tm (prodD a (mix s) Finset.univ)) (Ψ w) (Tm (prodD a (mix (insert w s)) Finset.univ)) := by
    intro s w hw
    have hne : w ∉ Finset.univ.erase w := Finset.notMem_erase w _
    have hu : (Finset.univ : Finset ι) = insert w (Finset.univ.erase w) :=
      (Finset.insert_erase (Finset.mem_univ w)).symm
    have e1 : prodD a (mix s) Finset.univ = tens (a w) (prodD a (mix s) (Finset.univ.erase w))
        (halfInd (a w) (latO S T ΛS ΛT fun _ => True)) := by
      conv_lhs => rw [hu]
      rw [prodD_insert ho _ hne]
      simp only [mix, if_neg hw]
    have e2 : prodD a (mix (insert w s)) Finset.univ = tens (a w) (prodD a (mix s) (Finset.univ.erase w)) (Ψ w) := by
      conv_lhs => rw [hu]
      rw [prodD_insert ho _ hne, prodD_congr a (Ψ := mix (insert w s)) (Ψ' := mix s) fun v hv => by
        have hvw : v ≠ w := Finset.ne_of_mem_erase hv
        simp only [mix, Finset.mem_insert, hvw, false_or]]
      simp only [mix, if_pos (Finset.mem_insert_self w s)]
    have hTm' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) ((∑ v ∈ Finset.univ.erase w, a v) + a w)
        (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm := by
      rwa [Finset.sum_erase_add _ _ (Finset.mem_univ w)]
    have hM := Factor.isPlaceModel_tensR D ψ S T _ (a w) _ _ _ f₀ Tm (sum_mul_zero ho hne) (hi w) (hΛ w)
      (fun _ _ => Iff.rfl) (prodD_sb ho hi hΛ (hmix s) (Finset.univ.erase w)) hTm'
    rw [e1, e2]
    exact ⟨⟨_, hM⟩, fun T' hT' => GlobalTheory.PlaceVec.placeModel_unique hψ hS hT (hi w) (hinf w) hM hT' (hΨ w)⟩
  refine ⟨fun s => Tm (prodD a (mix s) Finset.univ), hV0, ?_, fun s => ?_, hstep⟩
  · rw [hall Tm hTm]
    exact congrArg Tm (prodD_congr a fun w hw => if_pos hw)
  · induction s using Finset.induction_on with
    | empty => beta_reduce; rw [hV0]; exact h₀
    | insert w s hw ih => exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (hstep s w hw) ih

theorem idemAt_of_single {a : AE D} {w : Pl D.host.E} (h : IsIdemSum a {w}) : Formalism.L2.NTheta.IsIdemAt a w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  rw [Finset.sum_singleton]
  exact hes w (Finset.mem_singleton_self w)

theorem sum_eq {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) {a : P → AE D}
    (ha : ∀ w, IsIdemSum (a w) {w.1}) : ∑ w, a w = e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [← Finset.sum_coe_sort P es]
  exact Finset.sum_congr rfl fun w _ => by
    rw [GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (idemAt_of_single (ha w)), GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hes w.1 w.2)]

theorem orth {a b : AE D} {v w : Pl D.host.E} (ha : IsIdemSum a {v}) (hb : IsIdemSum b {w}) (h : v ≠ w) : a * b = 0 := by
  have h1 := cpt_of_isIdemAt (idemAt_of_single ha)
  have h2 := cpt_of_isIdemAt (idemAt_of_single hb)
  refine ae_ext ?_ fun Q => ?_
  · rw [map_mul, GlobalTheory.PlaceVec.idemSum_infPart ha, zero_mul, map_zero]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hQ : Q = v
    · rw [h2.2 Q (hQ ▸ h), mul_zero]
    · rw [h1.2 Q hQ, zero_mul]

theorem map_cpt_smul {a : AE D} {w : Pl D.host.E} (ha : IsIdemSum a {w}) {m n : ℕ} (y : Mx D m n) :
    ((a • y).map fun x => cpt w (toEAf D x)) = y.map fun x => cpt w (toEAf D x) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [map_mul, map_mul, (cpt_of_isIdemAt (idemAt_of_single ha)).1, one_mul]

theorem subset_vectors : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∃ V : Finset (locPl ch.G t) → SchDown ch.G t, V ∅ = (fun j : Fin D.R.m => ch.rm.vT D.R.m j) ∧ V Finset.univ = fd ∧ (∀ S j, IsThetaFunO ch.W.ψ _ _ (V S j)) ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S j) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S) j) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t e he φ hφ fd hfd eL heL
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hAA : ∀ w ∈ locPl ch.G t, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧
      ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1) := by
    intro w hw
    have hb := GlobalTheory.FunObj.Good.badInt_notMem hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hch.guard t) hw
    have h2q := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
    have hN := fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
    refine ⟨fun a ha => ?_, ⟨_, GlobalTheory.HostClear.absNorm_mem_AA D, ?_⟩⟩
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_le_one_of_mem h2q (Or.inl ha)
    · rw [GlobalTheory.FunObj.Good.valued_alg]
      exact GlobalTheory.FunObj.Good.valuation_nat hN
  have ho : ∀ v w, v ≠ w → eL v * eL w = 0 := fun v w h => orth (heL v) (heL w) fun h' => h (Subtype.ext h')
  have hi : ∀ w, eL w * eL w = eL w := fun w => GlobalTheory.PlaceVec.idemSum_mul_self (heL w)
  have hinf : ∀ w, infPart D (eL w) = 0 := fun w => GlobalTheory.PlaceVec.idemSum_infPart (heL w)
  have hsum := sum_eq he heL
  have key : ∀ j : Fin D.R.m, ∃ V : Finset (locPl ch.G t) → Sch ch.G (.down t D.R.m j), V ∅ = ch.rm.vT D.R.m j ∧
      V Finset.univ = fd j ∧ (∀ S, IsThetaFunO ch.W.ψ _ _ (V S)) ∧
      ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S)) := by
    intro j
    have hS : IsSelfDualC (ch.G.pS (.mu t D.R.m j)) (ch.G.latS (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m j) ⟨le_rfl, j.2.le⟩).sd
    have hT : IsSelfDualC (ch.G.pT (.mu t D.R.m j)) (ch.G.latT (.mu t D.R.m j)) :=
      (node_isV ch.G hL (X := .grid D.R.m ((j : ℕ) + 1)) ⟨le_rfl, j.2⟩).sd
    have hβS := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ)) le_rfl j.2.le
    have hβT := ch.S.B.isFrame_β hL (i := D.R.m) (j := (j : ℕ) + 1) le_rfl j.2
    have hmem : GlobalTheory.SplitFlip.Edge.theta D.R.m j ∈ GlobalTheory.SplitFlip.oppositePath D.R.m := by
      simp [GlobalTheory.SplitFlip.oppositePath]
    let Ψ : locPl ch.G t → WO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j)) → ℂ := fun w y =>
      if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0
    have hΨ : ∀ w, IsSBHalf (eL w) (latO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j))
        (ch.G.latS (.mu t D.R.m j) : Set _) (ch.G.latT (.mu t D.R.m j) : Set _) fun _ => True) (Ψ w) := by
      intro w
      have hin : ∀ v : ({w.1} : Finset (Pl D.host.E)), v.1 ∈ locPl ch.G t := fun v => by
        rw [Finset.mem_singleton.1 v.2]; exact w.2
      have hSB := GlobalTheory.VecsLast.isSBHalf_frames hS hT hβS hβT (heL w) (fun v hv => hAA v (hin ⟨v, hv⟩))
        (fun v => GlobalTheory.VecsLast.coordHom ch.S.B t v.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩)
        (fun v z => GlobalTheory.VecsLast.coordHom_int_iff ch.S.B t v.1 (X := (D.R.m, (j : ℕ) + 1)) (Y := (D.R.m, (j : ℕ))) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z)
        (fun v => depthAt ch.G v.1) (fun v => φ ⟨v.1, hin v⟩ (.theta D.R.m j))
        (fun v => (GlobalTheory.VecsLast.natDatum_props (hφ ⟨v.1, hin v⟩ _ hmem)).1)
        (fun v => (GlobalTheory.VecsLast.natDatum_props (hφ ⟨v.1, hin v⟩ _ hmem)).2)
      haveI : Subsingleton ({w.1} : Finset (Pl D.host.E)) :=
        ⟨fun a b => Subtype.ext ((Finset.mem_singleton.1 a.2).trans (Finset.mem_singleton.1 b.2).symm)⟩
      convert hSB using 1
      funext y
      rw [Fintype.prod_subsingleton _ ⟨w.1, Finset.mem_singleton_self _⟩]
      rfl
    have hprod : prodD eL Ψ Finset.univ = fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0 := by
      funext y
      unfold prodD
      rw [hsum]
      refine if_congr Iff.rfl (Finset.prod_congr rfl fun w _ => ?_) rfl
      refine (if_pos (Factor.half_of_idem (hi w) y)).trans ?_
      exact congrArg (fun z => φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ z)) (map_cpt_smul (heL w) y)
    obtain ⟨V, h1, h2, h3, h4⟩ := exists_chain ch.W.ψ_std ch.W.θ_is hS hT ho hi hinf hΨ
      (ch.rm.vT_is t D.R.m j le_rfl j.2).2.theta (f := fd j) (by rw [hsum, hprod]; exact (hfd j).2)
    exact ⟨V, h1, h2, h3, fun S w hw => ⟨hΨ w, h4 S w hw⟩⟩
  choose V h1 h2 h3 h4 using key
  exact ⟨fun S j => V j S, funext h1, funext h2, fun S j => h3 j S, fun S w hw j => h4 j S w hw⟩

end GlobalTheory.SubsetVecs

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsetPlaceVectorsAndStepsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subset_place_vectors_and_steps : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∃ V : Finset (locPl ch.G t) → SchDown ch.G t, V ∅ = (fun j : Fin D.R.m => ch.rm.vT D.R.m j) ∧ V Finset.univ = fd ∧ (∀ S j, IsThetaFunO ch.W.ψ _ _ (V S j)) ∧ ∀ (S : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∉ S → ∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) (eL w) (V S j) (fun y => if IsHalf (eL w) y then φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (V (insert w S) j) := by
  first | exact @GlobalTheory.SubsetVecs.subset_vectors | exact GlobalTheory.SubsetVecs.subset_vectors | (intros; apply GlobalTheory.SubsetVecs.subset_vectors <;> assumption)
end
end
