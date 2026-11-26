module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatIntegrableAaVacOfConductor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToDoubledFirstFactorBigCellInertPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelGridRationalLeftInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkGeneratedCuspFormsOfType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledFirstFactorMemDoubledLatticeStabilizer
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisOFinsetSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffField
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffField
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.MovedField

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.FunObj Formalism.L2.Host ValuativeRel

variable {D : D7}

theorem exists_zpow_unit (w : Pl D.host.E) (x : (Kw w)ˣ) :
    ∃ n : ℤ, Valued.v (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := by
  have h0 : Valued.v (x : Kw w) ≠ 0 := by simp
  have hu : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := unif_spec w
  have hx : Valued.v (x : Kw w) = WithZero.exp (WithZero.log (Valued.v (x : Kw w))) := (WithZero.exp_log h0).symm
  refine ⟨WithZero.log (Valued.v (x : Kw w)), ?_⟩
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hx, hu, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  simp

theorem natCast_cpow_half (N : ℕ) (m : ℤ) :
    (N : ℂ) ^ ((((m : ℝ) / 2 : ℝ)) : ℂ) = ((Real.sqrt N : ℝ) : ℂ) ^ m := by
  rw [show (N : ℂ) = ((N : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.ofReal_zpow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  ring

theorem sqrt_absNorm_ne_zero (w : Pl D.host.E) : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ≠ 0 := by
  have h : (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 w.ne_bot)
  exact_mod_cast (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm h)))

theorem apow_half_mem {w : Pl D.host.E} {K : Subfield ℂ}
    (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) (z : ℤ) : apow x ((z : ℂ) / 2) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have h1 : valuation (Kw w) (((x * unifAt w ^ n : (Kw w)ˣ)) : Kw w) = 1 := (Good.isEquiv_Kw w).eq_one_iff_eq_one.2 hn
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, apow_mul, apow_of_valuation_eq_one h1, one_mul, apow_zpow, (isUnif_unifAt w).apow_eq,
    GlobalTheory.LFun.SatBoundGL.resCard_completion]
  have e1 : -(((-n : ℤ) : ℂ) * ((z : ℂ) / 2)) = ((((n * z : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [e1, natCast_cpow_half]
  exact zpow_mem hs _

theorem loc_mem_of_unrAt {w : Pl D.host.E} {K : Subfield ℂ} {χ : HChar D.host.E} (hu : χ.UnrAt w)
    (hv : χ.valTw (1 / 2) w ∈ K) (hs : ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) ∈ K) (x : (Kw w)ˣ) :
    ((χ.loc w x : ℂˣ) : ℂ) ∈ K := by
  obtain ⟨n, hn⟩ := exists_zpow_unit w x
  have hx : x = (x * unifAt w ^ n) * unifAt w ^ (-n) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [hx, map_mul, hu _ hn, one_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  refine zpow_mem ?_ _
  have e1 : -(((1 / 2 : ℝ)) : ℂ) = ((((-1 : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hval : χ.valTw (1 / 2) w = ((χ.loc w (unifAt w) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ)⁻¹ := by
    rw [HChar.valTw, e1, natCast_cpow_half, zpow_neg_one]
    rfl
  have : ((χ.loc w (unifAt w) : ℂˣ) : ℂ) = χ.valTw (1 / 2) w * ((Real.sqrt (Ideal.absNorm w.asIdeal) : ℝ) : ℂ) := by
    rw [hval, inv_mul_cancel_right₀ (sqrt_absNorm_ne_zero w)]
  rw [this]
  exact mul_mem hv hs

theorem units_prod_mem {α : Type*} (K : Subfield ℂ) (f : α → ℂˣ) :
    ∀ l : List α, (∀ a ∈ l, ((f a : ℂˣ) : ℂ) ∈ K) → (((l.map f).prod : ℂˣ) : ℂ) ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons, Units.val_mul]
    exact mul_mem (h a List.mem_cons_self) (units_prod_mem K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem list_prod_mem' {α : Type*} (K : Subfield ℂ) (f : α → ℂ) :
    ∀ l : List α, (∀ a ∈ l, f a ∈ K) → (l.map f).prod ∈ K
  | [], _ => by simp [one_mem]
  | a :: l, h => by
    rw [List.map_cons, List.prod_cons]
    exact mul_mem (h a List.mem_cons_self) (list_prod_mem' K f l fun b hb => h b (List.mem_cons_of_mem _ hb))

end GlobalTheory.MovedField


open GlobalTheory.MovedField GlobalTheory.SplitFlip GlobalTheory.SplitWeil Formalism.L2.Host in
theorem GlobalTheory.MovedField.moved_mem : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b _ _ _ hF t Φ _ β _ w S hS z
  set K : Subfield ℂ := D.what₂.embLL.fieldRange with hKdef
  have hK : ∀ y : ℂ, y ∈ Set.range D.what₂.embLL ↔ y ∈ K := fun y => by
    rw [Set.mem_range, hKdef, RingHom.mem_fieldRange]
  have hsq : ((Real.sqrt (Ideal.absNorm (w : Pl D.host.E).asIdeal) : ℝ) : ℂ) ∈ K :=
    (hK _).1 (hF.sqrt w.1 (.inr ⟨t, w.2⟩))

  have hmu : ∀ j (x : (Kw w.1)ˣ), (((locGrid ch.G t w).mu j x : ℂˣ) : ℂ) ∈ K := fun j x => by
    change ((GlobalTheory.FunObj.muBase R.toLevCh j).loc w.1 x : ℂ) *
      ((R.xiH t).loc w.1 x : ℂ) ∈ K
    refine mul_mem ?_ ((hK _).1 (hF.chars.xi t _ x))
    rcases j with _ | j
    · exact one_mem K
    · rw [GlobalTheory.FunObj.muBase]
      split_ifs with hj
      · exact (hK _).1 (hF.chars.mu0 ⟨j, hj⟩ _ x)
      · exact one_mem K
  have hchi : ∀ i, 1 ≤ i → i ≤ D.R.m → ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).chi i x : ℂˣ) : ℂ) ∈ K :=
    fun i h1 h2 x => (hK _).1 (hF.chars.chi i h1 h2 _ x)
  have heta : ∀ x : (Kw w.1)ˣ, (((locGrid ch.G t w).eta x : ℂˣ) : ℂ) ∈ K := fun x => by
    have hu := R.toLevCh.C.isEta.unr w.1
    obtain ⟨y, hy⟩ := hF.chars.eta w.1 hu
    exact loc_mem_of_unrAt hu (hy ▸ (hK _).1 ⟨y, rfl⟩) hsq x

  have hkap : ∀ e ∈ oppositePath D.R.m, ∀ X (x : (Kw w.1)ˣ), (((locGrid ch.G t w).kappa e X x : ℂˣ) : ℂ) ∈ K := by
    intro e he X x
    rw [Grid.kappa, MonoidHom.div_apply, MonoidHom.pow_apply, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
    refine div_mem ?_ (pow_mem (heta x) _)
    rcases GlobalTheory.FunObj.mem_oppositePath.1 he with ⟨i, hi, rfl⟩ | ⟨j, -, rfl⟩
    · exact hchi _ (by show 1 ≤ D.R.m - i; omega) (by show D.R.m - i ≤ D.R.m; omega) x
    · exact hmu _ x
  have hap : ∀ (x : (Kw w.1)ˣ) (n : ℕ), apow x ((n : ℂ) / 2) ∈ K ∧ apow x (-(n : ℂ) / 2) ∈ K := fun x n =>
    ⟨by simpa using apow_half_mem hsq x n, by simpa using apow_half_mem hsq x (-n)⟩
  have hedge : ∀ g, ∀ e ∈ oppositePath D.R.m, (locGrid ch.G t w).edgeFactor .one g e ∈ K := by
    intro g e he
    rw [Grid.edgeFactor, Units.val_inv_eq_inv_val]
    exact mul_mem (mul_mem (mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))) (hap _ _).1) (hap _ _).2
  have hchar : ∀ g, ((((charFactor (locGrid ch.G t w) g)⁻¹ : ℂˣ)) : ℂ) ∈ K := by
    intro g
    rw [Units.val_inv_eq_inv_val]
    refine inv_mem (units_prod_mem K _ _ fun e he => ?_)
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
    exact mul_mem (hkap e he _ _) (inv_mem (hkap e he _ _))
  rw [hK]
  simp only [moved, Grid.pathAct]
  refine mul_mem ?_ (mul_mem (list_prod_mem' K _ _ (hedge _)) ((hK _).1 (hS _)))
  split
  · exact one_mem K
  · exact hchar _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.MovedField Formalism.L2.Host in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorFactor_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : GlobalTheory.RowTest.Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  exact @_root_.GlobalTheory.MovedField.moved_mem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberParameterInvOfChainParameterInv
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberParameterInvOfChainParameterInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainInv

variable {D : D7}

theorem conjP_eq_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem under_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  rw [← conjP_eq_conjPl]
  exact GlobalTheory.GridPlaces.under_conjP w

theorem absNorm_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr
    (Ideal.quotientEquiv w.asIdeal (Formalism.DivisionValues.conjPl w).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem not_isSplit_of_conjPl_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hc : Formalism.DivisionValues.conjPl w = w) :
    ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) := by
  intro hs
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E), R.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → R = w :=
    fun R hR => (GlobalTheory.GridPlaces.eq_or_eq_conjP hR).elim id fun h => h.trans ((conjP_eq_conjPl w).trans hc)
  exact hPQ ((key P hP).trans (key Q hQ).symm)

theorem val_conjPl_of_resEta (χ : (AE D)ˣ →* Circle) (n : ℕ) (hr : Formalism.L2.Theta.ResEta D χ n)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hu : GlobalTheory.LFun.UnrAt χ w) (hu' : GlobalTheory.LFun.UnrAt χ (Formalism.DivisionValues.conjPl w)) :
    GlobalTheory.LFun.val (F := D.host.F) χ (Formalism.DivisionValues.conjPl w) = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  have h2 := (GlobalTheory.AdelicU.isCMExt_host D).2.2.1
  by_cases hc : Formalism.DivisionValues.conjPl w = w
  · have hns := not_isSplit_of_conjPl_eq hc
    rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt (GlobalTheory.VacCoef.isUnram_host D (w.under (𝓞 D.host.F))) with hs | ⟨w0, hw0⟩
    · exact absurd hs hns
    · obtain rfl : w0 = w := GlobalTheory.LFun.eq_of_not_isSplit hns (GlobalTheory.LFun.under_eq_of_isInertAt hw0) rfl
      have hv := GlobalTheory.LFun.ResEta.val_of_isInertAt h2 hr hw0 hu
      rw [hc, hv, ← inv_pow, inv_neg_one]
  · exact eq_inv_of_mul_eq_one_right (GlobalTheory.LFun.ResEta.val_mul_val h2 hr (Ne.symm hc) rfl (under_conjPl w) hu hu')

theorem val_step_conjPl (c : Com D) (hc : c.Is) (k : ℕ) (hk : k < D.R.m) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) :
    GlobalTheory.LFun.val (F := D.host.F) (c.chS (k + 1)) (Formalism.DivisionValues.conjPl w) =
                 (GlobalTheory.LFun.val (F := D.host.F) (c.chS (k + 1)) w)⁻¹ ∧
      GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) (Formalism.DivisionValues.conjPl w) =
        (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)) w)⁻¹ := by
  have hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    intro h
    apply hw
    rw [GlobalTheory.LFun.above, Set.mem_setOf_eq] at h ⊢
    rwa [under_conjPl] at h
  have hμ : GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) (Formalism.DivisionValues.conjPl w) =
      (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)) w)⁻¹ :=
    val_conjPl_of_resEta _ 0 (hc.chars.2.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)).2 w
      (hc.unr ⟨k, hk⟩ w hw) (hc.unr ⟨k, hk⟩ _ hw')
  have hη : GlobalTheory.LFun.val (F := D.host.F) c.η (Formalism.DivisionValues.conjPl w) = (GlobalTheory.LFun.val (F := D.host.F) c.η w)⁻¹ :=
    val_conjPl_of_resEta _ 1 hc.chars.2.2.1 w (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w)
      (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 _)
  unfold Com.chS Com.chT Lift.chrStep
  split_ifs <;> simp only [GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv, hμ, hη, mul_inv, inv_inv, and_self]

theorem range_reflect (t : ℕ) : (Multiset.range t).map (fun i => t - 1 - i) = Multiset.range t := by
  refine (Multiset.Nodup.ext ?_ (Multiset.nodup_range t)).2 fun a => ?_
  · refine (Multiset.nodup_range t).map_on fun x hx y hy h => ?_
    rw [Multiset.mem_range] at hx hy
    omega
  · simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨b, hb, rfl⟩; omega
    · intro ha; exact ⟨t - 1 - a, by omega, by omega⟩

theorem seg_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) (z : ℂˣ) (t : ℕ) :
    GlobalTheory.LFun.seg (Formalism.DivisionValues.conjPl w) z⁻¹ t = (GlobalTheory.LFun.seg w z t).map (·⁻¹) := by
  have hN : ∀ y, GlobalTheory.LFun.npowU (Formalism.DivisionValues.conjPl w) y = GlobalTheory.LFun.npowU w y := fun y =>
    Units.ext (by simp only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, absNorm_conjPl])
  simp only [GlobalTheory.LFun.seg, hN, Multiset.map_map, Finset.range_val]
  conv_rhs => rw [← range_reflect t, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  simp only [Function.comp_apply, mul_inv]
  congr 1
  refine Units.ext ?_
  simp only [GlobalTheory.LFun.coe_npowU, Units.val_inv_eq_inv_val, GlobalTheory.LFun.npow]
  rw [← Complex.cpow_neg]
  congr 1
  push_cast [Nat.cast_sub (show i ≤ t - 1 by omega), Nat.cast_sub (show 1 ≤ t by omega)]
  ring

theorem chainPar_conjPl (c : Com D) (hc : c.Is) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))))
    (hB : B' (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹)) :
    ∀ k ≤ D.R.m, chainPar c B' k (Formalism.DivisionValues.conjPl w) = (chainPar c B k w).map (·⁻¹) := by
  intro k hk
  induction k with
  | zero => exact hB
  | succ k ih =>
    obtain ⟨hS, hT⟩ := val_step_conjPl c hc k (by omega) w hw
    rw [chainPar_succ, chainPar_succ]
    simp only [stepPar]
    rw [ih (by omega), hS, hT, seg_conjPl, Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp only [Function.comp_apply, mul_inv, inv_inv]

theorem conjPl_inv_of_chainPar : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ (B : GlobalTheory.LFun.Fam D.host.E),
    ∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))),
    chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) →
      B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by
  intro D c hc j hj B w hw h
  classical
  let B' : GlobalTheory.LFun.Fam D.host.E := Function.update B (Formalism.DivisionValues.conjPl w) ((B w).map (·⁻¹))
  have hB : B' (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by simp [B']
  have h1 := chainPar_conjPl c hc B B' w hw hB j hj
  have h2 := chainPar_inj_at D c j B B' (Formalism.DivisionValues.conjPl w) (h.trans h1.symm)
  rw [h2, hB]

end GlobalTheory.ChainInv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberParameterInvOfChainParameterInvStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstMemberParameter_inv_of_chainParameter_inv : ∀ (D : D7) (c : Com D), c.Is → ∀ j ≤ D.R.m, ∀ (B : GlobalTheory.LFun.Fam D.host.E), ∀ w ∉ (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))), chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) → B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := by
  first | exact @GlobalTheory.ChainInv.conjPl_inv_of_chainPar | exact GlobalTheory.ChainInv.conjPl_inv_of_chainPar | (intros; apply GlobalTheory.ChainInv.conjPl_inv_of_chainPar <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainTw.ParInv

variable {D : D7}

theorem conjP_eq_conjPl' (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

theorem under_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  rw [← conjP_eq_conjPl', GlobalTheory.GridPlaces.under_conjP]

theorem absNorm_conjPl' (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (Formalism.DivisionValues.conjPl P).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

theorem conjPl_ne_of_isSplit (w : HeightOneSpectrum (𝓞 D.host.E))
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : Formalism.DivisionValues.conjPl w ≠ w := by
  rintro hc
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E),
      Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) R.asIdeal = (w.under (𝓞 D.host.F)).asIdeal → R = w := by
    intro R hR
    rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := R) (HeightOneSpectrum.ext hR) with h | h
    · exact h
    · rw [h, conjP_eq_conjPl', hc]
  exact hPQ ((key P hP).trans (key Q hQ).symm)

end GlobalTheory.ChainTw.ParInv

end


open GlobalTheory.ChainTw.ParInv in
theorem GlobalTheory.ChainTw.invFam_bounded : ∀ D : D7, ForStageQ D fun c _ j s => ∀ (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E), IsPar u (chainPar c B j) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (GlobalTheory.ChainNS.invFam B) D.R.r ((D.R.r : ℝ) / 2) := by
  intro D c tw htw j hj s hs u B hu hB
  classical
  obtain ⟨hr, -, hflat⟩ := hs
  have hsd : IsSelfDualC s.V s.Λ := hflat.selfDual
  obtain ⟨hu0, hpar⟩ := hu
  obtain ⟨v0, hv0⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (Subtype.ext (LinearMap.ext fun v => by simpa using h v))
  have hP := hpar v0 hv0
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram s.V
  have key : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) := by
    intro w hw
    have hv : w.under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hw
    have hd :=
      (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) hJ.2
        (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice s.V s.Λ hsd)).2 (fun y => hsd.2 y) (w.under (𝓞 D.host.F))
    have hx := hP (w.under (𝓞 D.host.F)) hv w rfl
    by_cases hc : Formalism.DivisionValues.conjPl w = w
    · rw [hc]
      rcases hx with ⟨hs, -⟩ | ⟨hin, -⟩
      · exact absurd hc (conjPl_ne_of_isSplit w hs)
      · exact (GlobalTheory.LFun.ConjPlace.map_inv_of_isParamVec hin (hP _ hv w rfl)).symm
    · have hx' := hP (w.under (𝓞 D.host.F)) hv (Formalism.DivisionValues.conjPl w) (under_conjPl w)
      exact GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd (Ne.symm hc) hx hx'
  intro w hw
  have hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    show (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
    rw [under_conjPl]; exact hw
  have hB' : B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := GlobalTheory.T.firstMemberParameter_inv_of_chainParameter_inv D c htw.com j hj B w hw (key w hw)
  have e : GlobalTheory.ChainNS.invFam B w = B (Formalism.DivisionValues.conjPl w) := hB'.symm
  rw [e]
  have h2 := hB (Formalism.DivisionValues.conjPl w) hw'
  rwa [absNorm_conjPl'] at h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AntidiagonalUnipotentConjSiegelSquareSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AntidiagonalUnipotentConjSiegelSquareSplit
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitDblGenLeft

open GlobalTheory.InertDbl GlobalTheory.InertBigCell

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sq_smul_eq {n : Type} {v : Pl (F := F)} {c : AE F E} (hc : ∀ z : AE F E, At (evFin F v) z → c * c * z = z)
    {X : Matrix n n (AE F E)} (hX : At (evFin F v) X) : (c * c) • X = X := by
  ext i j
  rw [Matrix.smul_apply, smul_eq_mul]
  exact hc _ fun u hu => by simpa using congrFun (congrFun (hX u hu) i) j

theorem inlD_mem_closure_of_split {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {d : ℕ} (W : Spc F E d) (v : Pl (F := F))
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (h2 : (2 : 𝓞 F) ∉ v.asIdeal) (k : UA σ W.J) (hk : k ∈ GlobalTheory.InertSph.KAt σ W v) :
    inlD σ W k ∈ Subgroup.closure (ParD σ W v ∪ NabD σ W v) := by
  obtain ⟨c, hcσ, hcat, hcsq, hclat⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hB v hv
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ d W v h2 c hcσ hcat (hclat d W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ d W v h2 c hcσ (hclat d W) k hk
  have e1 : mat k * mat k⁻¹ = 1 := by
    show mat (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have e2 : mat k⁻¹ * mat k = 1 := by
    show mat (k⁻¹ * k) = 1
    rw [inv_mul_cancel]; rfl
  have hsq : (c * c) • (mat k - 1) = mat k - 1 := sq_smul_eq hcsq hk.1
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E d c (mat k) (mat k⁻¹) e1 e2 hsq
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E d c (mat k) (mat k⁻¹) e1 hsq
  let t : GL (Fin d) (AE F E) := ⟨GlobalTheory.SplitDblGen.tMat c (mat k), GlobalTheory.SplitDblGen.tMat c (mat k⁻¹), ht, mul_eq_one_comm.1 ht⟩
  have hq : n⁻¹ * (p * inlD σ W k) ∈ ParD σ W v := by
    refine ⟨KAtD_mul (KAtD_inv hn.1) (KAtD_mul hp.1 (inlD_mem hk)), t, ?_⟩
    have en : matD n⁻¹ * matD n = 1 := (n.1).inv_val
    show matD n⁻¹ * (matD p * matD (inlD σ W k)) * diagCols (Fin d) = diagCols (Fin d) * GlobalTheory.SplitDblGen.tMat c (mat k)
    rw [matD_inlD, hpm]
    rw [← hnm] at hid
    erw [Matrix.mul_assoc, hid, ← Matrix.mul_assoc, ← Matrix.mul_assoc, en, Matrix.one_mul]
    rfl
  have e : inlD σ W k = p⁻¹ * (n * (n⁻¹ * (p * inlD σ W k))) := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (Or.inl hp)))
    (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr hn)) (Subgroup.subset_closure (Or.inl hq)))

theorem inlD_mem_closure_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v hv _ h2 k hk
  exact inlD_mem_closure_of_split hT.base G.V' v hv h2 k hk

end GlobalTheory.SplitDblGenLeft
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AntidiagonalUnipotentConjSiegelSquareSplitStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antidiagonalUnipotent_conj_siegel_square_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, GlobalTheory.InertDbl.inlD σ G.V' k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.V' v ∪ GlobalTheory.InertDbl.NabD σ G.V' v) := by
  first | exact @GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left | exact GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left | (intros; apply GlobalTheory.SplitDblGenLeft.inlD_mem_closure_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarSqSmulMatrixSupportedAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarSqSmulMatrixSupportedAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
open GlobalTheory.SplitDblGen

namespace GlobalTheory.SplitDblGen

theorem inlD_mem_closure_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v hsp _ h2 k hk
  obtain ⟨c, hcσ, hcAt, hc2, hcL⟩ := GlobalTheory.T.exists_antiInvariant_sign_adele_splitPlace F E σ B hTr.base v hsp
  obtain ⟨p, hp, hpm⟩ := GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix F E σ _ G.W v h2 c hcσ hcAt (hcL _ G.W)
  obtain ⟨n, hn, hnm⟩ := GlobalTheory.T.nablaUnipotent_mem_integralDoubledUnipotent F E σ _ G.W v h2 c hcσ (hcL _ G.W) k hk
  have hg := GlobalTheory.T.doubledFirstFactor_mem_doubledLatticeStabilizer F E σ _ G.W v k hk
  have hKK' : mat k * mat k⁻¹ = 1 := congrArg (fun g : UA σ G.W.J => g.1.1) (mul_inv_cancel k)
  have hK'K : mat k⁻¹ * mat k = 1 := congrArg (fun g : UA σ G.W.J => g.1.1) (inv_mul_cancel k)
  have hAtK : At (evFin F v) (mat k - 1) := hk.1
  have hAtK' : At (evFin F v) (mat k⁻¹ - 1) := by
    intro u hu
    have e : mat k⁻¹ - 1 = -(mat k⁻¹ * (mat k - 1)) := by rw [Matrix.mul_sub, hK'K, Matrix.mul_one, neg_sub]
    rw [e, smul_neg, ← Matrix.mul_smul, hAtK u hu, Matrix.mul_zero, neg_zero]
  have hc2M : ∀ M : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E), At (evFin F v) M → (c * c) • M = M := by
    intro M hM
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hc2 _ (fun u hu => by
      have h0 := congrFun (congrFun (hM u hu) i) j
      simpa using h0)
  have ht := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k) (mat k⁻¹) hKK' (hc2M _ hAtK)
  have ht' := GlobalTheory.T.splitDoublingTMatrix_mul_inverse_eq_one F E _ c (mat k⁻¹) (mat k) hK'K (hc2M _ hAtK')
  have hid := GlobalTheory.T.diagonalFixingDoublingMatrix_mul_fromBlocks_mul_diagCols F E _ c (mat k) (mat k⁻¹) hKK' hK'K (hc2M _ hAtK)
  let T : GL (Fin (a + a')) (AE F E) := ⟨tMat c (mat k), tMat c (mat k⁻¹), ht, ht'⟩
  have hinv : GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD n = 1 := GlobalTheory.DblVacFlip.matD_inv_mul n
  have hq : n⁻¹ * p * GlobalTheory.InertDbl.inlD σ G.W k ∈ GlobalTheory.InertDbl.ParD σ G.W v := by
    refine ⟨GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.mul_mem_KD (GlobalTheory.DblVacFlip.inv_mem_KD hn.1) hp.1) hg, T, ?_⟩
    show GlobalTheory.InertDbl.matD n⁻¹ * GlobalTheory.InertDbl.matD p * GlobalTheory.InertDbl.matD (GlobalTheory.InertDbl.inlD σ G.W k) *
        diagCols (Fin (a + a')) = diagCols (Fin (a + a')) * tMat c (mat k)
    have h3 := congrArg (fun M => GlobalTheory.InertDbl.matD n⁻¹ * M) hid
    simp only [← Matrix.mul_assoc] at h3
    rw [GlobalTheory.InertDbl.matD_inlD, hpm]
    refine h3.trans ?_
    rw [← hnm, hinv]
    exact congrArg (· * tMat c (mat k)) (Matrix.one_mul _)
  have e : GlobalTheory.InertDbl.inlD σ G.W k = p⁻¹ * n * (n⁻¹ * p * GlobalTheory.InertDbl.inlD σ G.W k) := by group
  rw [e]
  have s : ∀ x, x ∈ GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v →
      x ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) :=
    fun x hx => Subgroup.subset_closure hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (s _ (Or.inl hp))) (s _ (Or.inr hn))) (s _ (Or.inl hq))

end GlobalTheory.SplitDblGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarSqSmulMatrixSupportedAtPlaceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarSq_smul_matrix_supported_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, GlobalTheory.InertDbl.inlD σ G.W k ∈ Subgroup.closure (GlobalTheory.InertDbl.ParD σ G.W v ∪ GlobalTheory.InertDbl.NabD σ G.W v) := by
  first | exact @GlobalTheory.SplitDblGen.inlD_mem_closure_split | exact GlobalTheory.SplitDblGen.inlD_mem_closure_split | (intros; apply GlobalTheory.SplitDblGen.inlD_mem_closure_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalProjectionPosDefSesquilinearFini
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalProjectionPosDefSesquilinearFini
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory

theorem exists_proj_sesq_posDef_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  intro M _ _ b F hF hpos hherm
  classical
  set n := Module.finrank ℂ F
  let v : Module.Basis (Fin n) ℂ F := Module.finBasis ℂ F
  let A : F →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => (b (v i : M)).comp F.subtype)
  let B : M →ₗ[ℂ] (Fin n → ℂ) :=
    { toFun := fun x i => star (b x (v i : M))
      map_add' := by intro x y; funext i; simp [map_add (f := _)]
      map_smul' := by intro c x; funext i; simp [mul_comm] }
  have key : ∀ (y : F) (x : M), (∀ i, b (v i : M) (y : M) = star (b x (v i : M))) →
      ∀ f ∈ F, b (y : M) f = b x f := by
    intro y x h f hf
    have hc : (b (y : M)).comp F.subtype = (b x).comp F.subtype := by
      refine v.ext (fun i => ?_)
      simp only [LinearMap.comp_apply, Submodule.coe_subtype]
      rw [← hherm _ (v i).2 _ y.2, h i, star_star]
    have := LinearMap.congr_fun hc ⟨f, hf⟩
    simpa using this
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h0 : ∀ i, b (v i : M) (y : M) = star (b (0 : M) (v i : M)) := by
      intro i
      have := congrFun hy i
      simpa [A] using this
    have hyy := key y 0 h0 y y.2
    by_contra hne
    have hne' : (y : M) ≠ 0 := by simpa using hne
    have := hpos y y.2 hne'
    rw [hyy] at this
    simp at this
  have hdim : Module.finrank ℂ F = Module.finrank ℂ (Fin n → ℂ) := by simp [n]
  let Aeq := LinearMap.linearEquivOfInjective A hinj hdim
  refine ⟨F.subtype.comp (Aeq.symm.toLinearMap.comp B), fun x => (Aeq.symm (B x)).2, ?_⟩
  intro x f hf
  show b ((Aeq.symm (B x) : F) : M) f = b x f
  refine key (Aeq.symm (B x)) x ?_ f hf
  intro i
  have h1 : A (Aeq.symm (B x)) = B x := by
    exact Aeq.apply_symm_apply (B x)
  have := congrFun h1 i
  simpa [A, B] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalProjectionPosDefSesquilinearFiniStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonalProjection_posDef_sesquilinear_finiteDim : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (b : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (F : Submodule ℂ M), FiniteDimensional ℂ F →
    (∀ x ∈ F, x ≠ 0 → 0 < (b x x).re) → (∀ x ∈ F, ∀ y ∈ F, star (b x y) = b y x) →
    ∃ e : M →ₗ[ℂ] M, (∀ x, e x ∈ F) ∧ ∀ x, ∀ f ∈ F, b (e x) f = b x f := by
  first | exact @GlobalTheory.exists_proj_sesq_posDef_finiteDim | exact GlobalTheory.exists_proj_sesq_posDef_finiteDim | (intros; apply GlobalTheory.exists_proj_sesq_posDef_finiteDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviThetaValueLeDetMulRationalSum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviThetaValueLeDetMulRationalSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
noncomputable section

namespace GlobalTheory.LeviThetaSum

theorem levi_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec S S₀ r)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om →
    ∃ (μ' : Measure (Mx D T.rank r)) (𝓕' : Set (Mx D T.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D T.rank r) μ' 𝓕' ∧
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D),
        ‖om (d.levi α, 1) f 0‖ₑ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank α) *
          ∑' ξ : Matrix (Fin T.rank) (Fin r) D.host.E,
            ‖d.mixS T ψ μ' 𝓕' f (HMul.hMul (ξ.map (incA D) : Mx D T.rank r) α.1) 0‖ₑ := by
  intro D ψ S S₀ T r d χS χT om ho
  obtain ⟨v⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank r
  obtain ⟨om₀, ho₀⟩ := GlobalTheory.WeilExist.exists_isWeilDatumO D ψ ho.std S₀ T χS χT
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) ho.hecS ho.hecT (GlobalTheory.Unf.resEta_core d ho.resS) ho.resT
  refine ⟨v.μ, v.𝓕, v.covol, fun f hf α => ?_⟩
  have hF := GlobalTheory.MixSourceFormulas.mixed_source D ψ S S₀ T r d χS χT om om₀ ho ho₀ v.μ v.𝓕 v.covol f hf
  have hg : IsThetaFunO ψ S T (om (d.levi α, 1) f) := ho.om_pres _ f hf
  have hsum := (GlobalTheory.HeisMixSource.heis_mixS D ψ ho.std S S₀ T r d v (om (d.levi α, 1) f) hg).2.2.2.2 0
  rw [map_zero] at hsum
  rw [← hsum.tsum_eq]
  refine enorm_tsum_le_tsum_enorm.trans (le_of_eq ?_)
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext ξ
  have e := congrFun (hF.levi α (GlobalTheory.MixModel.rat ξ)) 0
  change ‖(I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.source d) T ψ v.μ v.𝓕
    (om (d.levi α, 1) f) (GlobalTheory.MixModel.rat ξ) 0‖ₑ = _
  rw [e, Pi.smul_apply, smul_eq_mul, enorm_mul, enorm_mul]
  congr 1
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Circle.norm_coe, ENNReal.ofReal_one, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod_pos _ _).le]

end GlobalTheory.LeviThetaSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviThetaValueLeDetMulRationalSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leviThetaValue_le_det_mul_rational_sum : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec S S₀ r)
    (χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)),
    IsWeilDatumO ψ S T χS χT om →
    ∃ (μ' : Measure (Mx D T.rank r)) (𝓕' : Set (Mx D T.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D T.rank r) μ' 𝓕' ∧
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D),
        ‖om (d.levi α, 1) f 0‖ₑ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank α) *
          ∑' ξ : Matrix (Fin T.rank) (Fin r) D.host.E,
            ‖d.mixS T ψ μ' 𝓕' f (HMul.hMul (ξ.map (incA D) : Mx D T.rank r) α.1) 0‖ₑ := by
  first | exact @GlobalTheory.LeviThetaSum.levi_sum | exact GlobalTheory.LeviThetaSum.levi_sum | (intros; apply GlobalTheory.LeviThetaSum.levi_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVe
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

namespace GlobalTheory.RatMoveJets

theorem exists_unitary_ratCoord {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node) (hX : DefNode D.R.m X) (r : FinPt G X) (hr : GlobalTheory.MovedKappaEx.RatFin (G.V X) r) :
    ∃ U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E, GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U := by
  obtain ⟨γ, hγ, hf⟩ := hr
  obtain ⟨γ', h1, h2⟩ := id hγ
  have hG : star γ'.1 * (G.V X).gram * γ'.1 = (G.V X).gram := h1
  have hmt : Formalism.L2.Theta.mt (G.V X) γ = γ'.1.map (incA D) := congrArg Units.val h2.symm
  set F := (S.N.fr X).1 with hFdef
  set Fi := ((S.N.fr X)⁻¹ : GL (Fin (G.V X).rank) D.host.E).1 with hFidef
  have hF : star F * (G.V X).gram * F = 1 := S.N.fr_on X hX
  have e1 : Fi * F = 1 := by rw [hFdef, hFidef]; exact Units.inv_mul _
  have e2 : F * Fi = 1 := by rw [hFdef, hFidef]; exact Units.mul_inv _
  have hGram : star Fi * Fi = (G.V X).gram := by
    have : star Fi * (star F * (G.V X).gram * F) * Fi = (G.V X).gram := by
      calc star Fi * (star F * (G.V X).gram * F) * Fi = star (F * Fi) * (G.V X).gram * (F * Fi) := by
            rw [star_mul]; simp only [Matrix.mul_assoc]
        _ = (G.V X).gram := by rw [e2, star_one, Matrix.one_mul, Matrix.mul_one]
    rw [hF, Matrix.mul_one] at this
    exact this
  have hU : star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = 1 := by
    calc star (Fi * γ'.1 * F) * (Fi * γ'.1 * F) = star F * (star γ'.1 * (star Fi * Fi) * γ'.1) * F := by
          simp only [star_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hGram, hG]; exact hF
  refine ⟨⟨Fi * γ'.1 * F, Matrix.mem_unitaryGroup_iff'.2 hU⟩, γ, hγ, hf, ?_⟩
  rw [hmt]
  congr 1
  change γ'.1 = F * (Fi * γ'.1 * F) * Fi
  simp only [← Matrix.mul_assoc, e2, Matrix.one_mul]
  rw [Matrix.mul_assoc, e2, Matrix.mul_one]

end GlobalTheory.RatMoveJets
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCoordinate_of_rationalPoint_definiteVertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ r : FinPt G X, GlobalTheory.MovedKappaEx.RatFin (G.V X) r →
    ∃ U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E, GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U := by
  first | exact @GlobalTheory.RatMoveJets.exists_unitary_ratCoord | exact GlobalTheory.RatMoveJets.exists_unitary_ratCoord | (intros; apply GlobalTheory.RatMoveJets.exists_unitary_ratCoord <;> assumption)
end
end
