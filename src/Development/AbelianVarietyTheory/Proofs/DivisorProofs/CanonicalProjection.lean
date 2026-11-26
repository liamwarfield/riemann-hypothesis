module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxGraphGraphHeis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjection
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp

noncomputable section

open scoped TensorProduct
open NumberField Formalism.BasicNotions Formalism.IndefR.NX Formalism.IndefR.Arith GlobalTheory.IndefiniteRowSideFullHecke.FractionalBaseInclusion

namespace GlobalTheory.BigOn.Exp.ProjRd

attribute [local instance] GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.algKK


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem rd_eOp {D : D7} {c : NChoice D} {w : D.what₂.places.Pl} (ht : NChTie D c) {Gp : Type} [Group Gp] [Fintype Gp]
    (I : Gp ≃* G0g D.nd) (S : RatDat D.ntw) (j : ℕ)
    {Ks' WL' : Type} {_ : Field Ks'} {_ : NumberField Ks'} {_ : Algebra Ks' D.what₂.LL} {_ : AddCommGroup WL'}
    {_ : Module D.what₂.LL WL'} {_ : Module Ks' WL'} [IsScalarTower Ks' D.what₂.LL WL']
    {_ : Module (𝓞 Ks') WL'} {_ : IsScalarTower (𝓞 Ks') Ks' WL'}
    {W' : (D.what₂.LL →+* ℂ) → Type} {_ : ∀ σ, NormedAddCommGroup (W' σ)} {_ : ∀ σ, InnerProductSpace ℂ (W' σ)}
    (A' : FormsL D.what₂.LL Ks' WL' W' Gp) (fi : FormsIso (S.A j) A') (hks : (S.A j).IsKsForm)
    (hgeq : ∀ s, I (fi.eG s) = S.eG s)
    (rho : RhoStab S j) (chi : ChiInLL0 S j)
    (eF : D.nexp.Fm (c.twI w) j (c.sd w) ≃ₗ[FractionRing (D.ntw.O (c.twI w))] Fm S (c.twI w) j (c.sd w))
    (hact : ∀ g x, eF (D.nexp.actG (c.twI w) j (c.sd w) g x) = actG S (c.twI w) j (c.sd w) rho chi g (eF x))
    (eC : Gp → D.what₂.LL) (heC : ∀ h, eC h = (D.nexp.eLL0 (I h) : D.what₂.LL))
    (rd : WL' →ₛₗ[c.embW w] FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w))
    (hrd : ∀ f : FmK S j, rd (fi.e (Subtype.val f)) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] eF.symm ((1 : KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f))
    (y : WL') :
    rd (A'.eOp eC y) = GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) (rd y) := by
  classical
  obtain ⟨e, -, -, h3, h4⟩ := GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.stage1 (w := w) ht j S hks rho chi eF hact
  have hre : ∀ x, rd (fi.e x) = e x := by
    intro x
    obtain ⟨n, b, hbK, -, -, -, hsp⟩ := hks
    have hx : x ∈ Submodule.span D.what₂.LL (Set.range b) := hsp ▸ Submodule.mem_top
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.what₂.LL).1 hx
    have h5 := h3 n a (fun k => ⟨b k, hbK k⟩)
    refine Eq.trans ?_ h5.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smulₛₗ]
    rw [hrd ⟨b k, hbK k⟩, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  obtain ⟨x, rfl⟩ := fi.e.surjective y
  letI : Fintype S.G := Fintype.ofEquiv Gp fi.eG.symm.toEquiv
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv Gp I.toEquiv
  have hL : A'.eOp eC (fi.e x) = fi.e (∑ s : S.G, eC (fi.eG s) •
      ((((S.A j).chi s)⁻¹ : D.what₂.LLˣ).val • (S.A j).ρ s x)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, FormsL.eOp, LinearMap.sum_apply]
    refine (Fintype.sum_equiv fi.eG.toEquiv _ _ fun s => ?_).symm
    rw [map_smul, map_smul, fi.rho]
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, LinearMap.smul_apply, smul_smul, fi.chi]
  have hR : ∀ t : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) j (c.sd w),
      GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) t = ∑ s : S.G,
        algebraMap (FractionRing (D.ntw.O (c.twI w))) (FractionRing (c.Oe w)) ((D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s)) •
          GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.ext (D.ntw.O (c.twI w)) (FractionRing (c.Oe w))
            ((D.nexp.actG (c.twI w) j (c.sd w) (S.eG s)).toLinearMap) t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add u v hu hv => rw [map_add (f := _), hu, hv, ← Finset.sum_add_distrib]; simp only [map_add (f := _), smul_add]
    | tmul a m =>
      have h1 : GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eExt D.nexp (c.twI w) j (c.sd w) (c.Oe w) (a ⊗ₜ m) =
          a ⊗ₜ[D.ntw.O (c.twI w)] GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp D.nexp (c.twI w) j (c.sd w) m := rfl
      have h2 : GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp D.nexp (c.twI w) j (c.sd w) m = ∑ s : S.G,
          (D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s) • D.nexp.actG (c.twI w) j (c.sd w) (S.eG s) m := by
        unfold GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators.eOp
        rw [GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.lift_eq_sum, LinearMap.sum_apply]
        exact (Fintype.sum_equiv S.eG.toEquiv _ _ fun s => rfl).symm
      rw [h1, h2, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.tmul_smul_frac, GroupAverageFixedPoints.GlobalTheory.CompanionTheory.LatSpan.ext_tmul, TensorProduct.smul_tmul', smul_eq_mul]
      rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, hre, hre, hR, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smulₛₗ, h4 s x]
  congr 1
  rw [heC, hgeq, GlobalTheory.Proof.FractionFieldEmbeddingCompat.embW_eq_of_tie ht w]
  change _ = fracExt c w ((D.nexp.eAlg (c.twI w) (c.sd w)).coeff (S.eG s))
  rw [D.nexp.eAlg_def]
  rfl

end GlobalTheory.BigOn.Exp.ProjRd

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BoxSpan

theorem boxFun_mem_SB' {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem schr_boxFun {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (w : (κ ⊕ κ' → R) × (κ ⊕ κ' → R)) (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ w (boxFun φ₁ φ₂) = boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁)
      (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Pi.add_apply]
  rw [show (∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) +
      ⅟(2 : R) * ((∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) =
      ((∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i))) +
      ((∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) by ring,
    AddChar.map_add_eq_mul]
  rw [show (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl from rfl,
    show (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr from rfl]
  ring

end GlobalTheory.BoxSpan


open GlobalTheory.BoxSpan in
theorem GlobalTheory.BoxSpan.boxSpan_ker : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  intro F _ _ v κ κ' _ _ ψ hψ h1 Λ hΛ Φ hΦ
  classical
  let N : Submodule ℂ ((κ ⊕ κ' → Fv F v) → ℂ) := Submodule.span ℂ
    {f | ∃ φ₁ ∈ SB (κ → Fv F v), ∃ φ₂ ∈ SB (κ' → Fv F v), f = boxFun φ₁ φ₂}
  have hN : N ≤ SB (κ ⊕ κ' → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact boxFun_mem_SB' h₁ h₂
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    intro w
    let Lw : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → Fv F v) → ℂ) :=
      { toFun := schr ψ w
        map_add' := fun f g => by funext x; simp [schr, mul_add]
        map_smul' := fun c f => by funext x; simp [schr]; ring }
    have : N ≤ N.comap Lw := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      show schr ψ w (boxFun φ₁ φ₂) ∈ N
      rw [schr_boxFun]
      exact Submodule.subset_span ⟨_, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₁, _,
        GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₂, rfl⟩
    exact fun φ hφ => this hφ
  let i₁ := Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
  let i₂ := Set.indicator {x : κ' → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ' → Fv F v) → ℂ)
  have h0 : boxFun i₁ i₂ ∈ N := Submodule.subset_span
    ⟨i₁, GlobalTheory.StdVacuum.indicator_mem_SB v, i₂, GlobalTheory.StdVacuum.indicator_mem_SB v, rfl⟩
  have hne : boxFun i₁ i₂ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [boxFun, i₁, i₂, Set.indicator, zero_mem] at this
  have hall := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hN hS _ h0 hne
  have hk : N ≤ LinearMap.ker Λ := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact hΛ φ₁ h₁ φ₂ h₂
  rw [← hall] at hΦ
  exact hk hΦ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhatStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_eq_zero_of_kills_productSchwartzBruhat : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  first | exact @GlobalTheory.BoxSpan.boxSpan_ker | exact GlobalTheory.BoxSpan.boxSpan_ker | (intros; apply GlobalTheory.BoxSpan.boxSpan_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookLogSumSubSizeTermLeLowerBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookLogSumSubSizeTermLeLowerBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowMainTerm

theorem logHook_congr (n : ℕ) (a b : ℕ → ℝ) (h : ∀ i < n, a i = b i) :
    Formalism.BasicNotions.DV.logHook n a = Formalism.BasicNotions.DV.logHook n b := by
  unfold Formalism.BasicNotions.DV.logHook
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [h i (Finset.mem_range.mp hi)]
  · refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => ?_
    have hi' := Finset.mem_range.mp hi
    have hl' := (Finset.mem_Ioo.mp hl).2
    rw [h i hi', h l hl']

theorem pW_eq (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ = (D.R.sigW ((j : ℕ) + 1)).1 := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW
  rw [GlobalTheory.RecGaps.sig_Wc]

theorem sigW_fst (D : D7) (j : Fin D.R.m) : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := by
  simp [Formalism.BasicNotions.Ranks.sigW]

theorem hook_term (D : D7) (j : Fin D.R.m) (ρ : D.what₂.Tau) :
    Real.log ((GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ)
        (Formalism.IndefR.Links.aPl D j (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D j ρ) ρ) : ℕ) : ℝ)
      = Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ) := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  rw [pW_eq, sigW_fst]
  have key : ∀ n < D.R.k + (j : ℕ),
      ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ n : ℕ) : ℝ) = Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) ρ n := by
    intro n hn
    have := GlobalTheory.RecordWeightVec.aPl_eq_aPlusQ D j ρ n hn
    unfold Formalism.BasicNotions.DV.aPlus
    rw [← this]
    push_cast
    rfl
  have rs := (GlobalTheory.BlockRows.rows_sizes D ((j : ℕ) + 1) h1 h2 ρ).1
  have hanti : ∀ (x y : ℕ), x ≤ y → y < D.R.k + (j : ℕ) →
      Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y ≤ Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x := by
    intro x y hxy hy
    have hx : x < D.R.k + (j : ℕ) := lt_of_le_of_lt hxy hy
    have e : (D.R.sigW ((j : ℕ) + 1)).1 = D.R.k + (j : ℕ) := sigW_fst D j
    have hy' : y < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hy
    have hx' : x < (D.R.sigW ((j : ℕ) + 1)).1 := e ▸ hx
    have ha := rs.1 (show (⟨x, hx'⟩ : Fin _) ≤ ⟨y, hy'⟩ from hxy)
    have ex := rs.2.2 ⟨x, hx'⟩
    have ey := rs.2.2 ⟨y, hy'⟩
    have r : ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ y : ℕ) : ℝ)
        ≤ ((Formalism.IndefR.Links.aPl D j (D.R.k + (j : ℕ)) ρ x : ℕ) : ℝ) := by
      rw [key y hy, key x hx]
      simp only at ex ey
      rw [← ex, ← ey]
      exact_mod_cast ha
    exact_mod_cast r
  rw [(GlobalTheory.HookDiagram.hookOf_pos_log _ _ hanti).2]
  exact logHook_congr _ _ _ key

end GlobalTheory.LowMainTerm

namespace GlobalTheory.LowMainTerm

theorem sum_logHook_eq (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (j : Fin D.R.m) :
    (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) = GlobalTheory.LiftLower.hookPlus D j := by
  have h1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
  have h2 : (j : ℕ) + 1 ≤ D.R.m := j.isLt
  have e1 : (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ)
      = ∑ z : Bool × G.HH D, Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1
          (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) (tauPl D z)) :=
    Finset.sum_congr rfl fun z _ => Formalism.L2.DIV.NumTieH.logHook_eq D L Del h0 h1 h2 z
  rw [e1, Function.Bijective.sum_comp (tauPl_bijective D)
    (fun τ => Formalism.BasicNotions.DV.logHook (D.R.sigW ((j : ℕ) + 1)).1 (Formalism.BasicNotions.DV.aPlus D ((j : ℕ) + 1) τ))]
  unfold GlobalTheory.LiftLower.hookPlus
  exact (Finset.sum_congr rfl fun ρ _ => hook_term D j ρ).symm

theorem main_le_lowB : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  intro D L Del h0 Csz j hC hS
  rw [sum_logHook_eq]
  have hLp : (ofRecord D L Del h0).Lp = GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    rw [Formalism.L2.DIV.NumTieH.Lp_eq]; rfl
  have hpos : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by
    have := (GlobalTheory.AdelicScalar.SizeBounds.sizes D j L.sc.b hS).1
    linarith
  rw [hLp]
  unfold GlobalTheory.BigOn.lowB
  have hX : 0 ≤ (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Lp D L.sc.b := by positivity
  nlinarith

end GlobalTheory.LowMainTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookLogSumSubSizeTermLeLowerBoundStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hookLogSum_sub_sizeTerm_le_lowerBound : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (Csz : ℝ) (j : Fin D.R.m), 8 ≤ Csz → Sizes D j L.sc.b → (∑ ρ, (ofRecord D L Del h0).logHook ((j : ℕ) + 1) ρ) - Csz * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * (ofRecord D L Del h0).Lp) ≤ lowB D j L.sc.b := by
  first | exact @GlobalTheory.LowMainTerm.main_le_lowB | exact GlobalTheory.LowMainTerm.main_le_lowB | (intros; apply GlobalTheory.LowMainTerm.main_le_lowB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafShareIOfShareW
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.ShareOn.Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tied

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst}

theorem card_comap_base (h1 : R.grp_levels F) : Nat.card (F.P0.comap (mirIncl R)) = Nat.card F.P0 := by
  refine Nat.card_congr (Equiv.ofBijective (fun u : F.P0.comap (mirIncl R) => (⟨mirIncl R u, u.2⟩ : F.P0)) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (mirIncl_injective R (congrArg Subtype.val hab))
  · rintro ⟨g, hg⟩
    obtain ⟨u, -, rfl⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨⟨u, hg⟩, rfl⟩

variable {P : Type} [Group P] [Finite P]

theorem mem_eig_iff {O : OnObj ((R.toCx F).data F.cr false) P c} {inc : P →* G} (h1 : R.grp_levels F) (h2 : R.grp_chiW)
    (hinc : F.P0 ≤ inc.range) (j : Fin D.R.m) (w : (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL))
    (hρ : ∀ g x, w (O.ρ j g x) = (R.FW j).ρ (inc g) (w x)) (hU : O.U = F.P0.comap inc)
    (hψ : ∀ (g : P) (hg : inc g ∈ F.P0), ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) = (F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ))
    (x : Fin (O.nZ j) → D.what₂.LL) : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ ↔ w x ∈ GlobalTheory.CovTop.spType R F j := by
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ ↔ ∀ u : O.U, O.ρ j u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ j g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW j).ρ (inc g) (w x) = (((R.FW j).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • w x :=
    fun g hg => by
      rw [chi_eq_one h1 h2 j hg, one_mul, ← hψ g hg, ← hρ, ← LinearEquiv.map_smul, w.injective.eq_iff]
  show _ ↔ ∀ q : F.P0, (R.FW j).ρ q (w x) = (((R.FW j).chi q * F.ψ0⁻¹ q : D.what₂.LLˣ) : D.what₂.LL) • w x
  refine e1.trans ⟨?_, fun h u => ?_⟩
  · rintro h ⟨g, hg⟩
    obtain ⟨q, rfl⟩ := hinc hg
    exact (e2 q hg).1 (h ⟨q, hU ▸ hg⟩)
  · have hg : inc u ∈ F.P0 := (hU ▸ u.2 : (u : P) ∈ F.P0.comap inc)
    exact (e2 u hg).2 (h ⟨inc u, hg⟩)

theorem tied_dims {O : OnObj ((R.toCx F).data F.cr false) (Mir R) c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph (mirIncl R) O) (h1 : R.grp_levels F) (h2 : R.grp_chiW)
    (j : Fin D.R.m) :
    O.nZ j = R.nW j ∧ Nat.card O.U = Nat.card F.P0 ∧ O.d0 j = (finrank D.what₂.LL (GlobalTheory.CovTop.spType R F j) : ℝ) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v, -⟩ := exists_place3 D.what₂.LL
  have t := (ht v j).1
  let w : (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) :=
    LinearEquiv.ofBijective (toForms (T := (run v).full) (R := R) (h v) fw j (z j))
      (toForms_bijective (T := (run v).full) (R := R) (h v) fw j (z j))
  have hinc : F.P0 ≤ (mirIncl R).range := fun g hg => by
    obtain ⟨u, -, rfl⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · have := w.finrank_eq
    simpa only [Module.finrank_fin_fun] using this
  · rw [t.U_eq]
    exact card_comap_base h1
  · have hm : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).map (w : (Fin (O.nZ j) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL)) =
        GlobalTheory.CovTop.spType R F j := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (mem_eig_iff h1 h2 hinc j w (t.rho_eq_of_actionPin (ht v j).2) t.U_eq t.ψ_eq x).1 hx
      · intro hu
        refine ⟨w.symm u, ?_, w.apply_symm_apply u⟩
        refine (mem_eig_iff h1 h2 hinc j w (t.rho_eq_of_actionPin (ht v j).2) t.U_eq t.ψ_eq _).2 ?_
        rw [w.apply_symm_apply]
        exact hu
    unfold OnObj.d0
    rw [← hm, LinearEquiv.finrank_map_eq]

end Tied

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem leafShareI_of_shareW (p : PtAt ex Csz) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hR : RecAt p Tp r O) (hW : ∀ i, ShareW p i (1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3))) :
    LeafShareI O := by
  have hfk : O.f = (D.R.f : ℝ) ∧ O.k = (D.R.k : ℝ) := by
    letI := hostAlg D
    obtain ⟨st, rt⟩ := hR.1.depth
    exact ⟨rt.f_eq, rt.k_eq⟩
  obtain ⟨hc, hinj, ht⟩ := hR.1.tied
  intro j
  obtain ⟨hn, hU, hd⟩ := tied_dims ht p.charW.base.grp.levels p.charW.base.grp.chiW j
  refine ⟨O.y, le_rfl, ?_⟩
  have hy : O.y = 1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3) := by
    unfold OnObj.y
    rw [hfk.1, hfk.2]
  have hw := hW j
  unfold ShareW at hw
  rw [hy, hn, hd, hU]
  exact hw

end Point

end GlobalTheory.ShareOn.Comparison₂

namespace GlobalTheory.ShareOn

end GlobalTheory.ShareOn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedExistence
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open Formalism.BasicNotions Formalism.MainNotions Formalism.IndefR.Links Formalism.L2.Host GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp.Adapt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ext_frac {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
    (hinj : Function.Injective (algebraMap A B)) [Module.Finite A B] (f : FractionRing A →+* ℂ) :
    ∃ g : FractionRing B →+* ℂ, ∀ a : A, g (algebraMap B _ (algebraMap A B a)) = f (algebraMap A _ a) := by
  letI : Algebra A ℂ := (f.comp (algebraMap A (FractionRing A))).toAlgebra
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsAlgebraic A B := inferInstance
  haveI : Algebra.IsAlgebraic B (FractionRing B) := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
  haveI : Algebra.IsAlgebraic A (FractionRing B) := Algebra.IsAlgebraic.trans A B (FractionRing B)
  have hA : Function.Injective (algebraMap A (FractionRing B)) := by
    rw [IsScalarTower.algebraMap_eq A B (FractionRing B)]
    exact (IsFractionRing.injective B (FractionRing B)).comp hinj
  have hC : Function.Injective (algebraMap A ℂ) :=
    f.injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : Module.IsTorsionFree A (FractionRing B) := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hA (h.trans (map_zero _).symm)) id
  haveI : Module.IsTorsionFree A ℂ := Module.IsTorsionFree.of_smul_eq_zero fun r m h => by
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp (fun h => hC (h.trans (map_zero _).symm)) id
  let g := IsAlgClosed.lift (M := ℂ) (R := A) (S := FractionRing B)
  refine ⟨g.toRingHom, fun a => ?_⟩
  have h := g.commutes a
  rw [IsScalarTower.algebraMap_apply A B (FractionRing B)] at h
  exact h

variable {D : D7}

theorem charOf_congr {Ω : Type} [Field Ω] [Algebra D.host.E Ω] (a : Recip D Ω) {R : Type} [CommRing R]
    (f f' : R →+* ℂ) (ψ : G D.host.E Ω →* Rˣ) (h : ∀ σ, f (ψ σ : Rˣ) = f' (ψ σ : Rˣ)) :
    GlobalTheory.SeriesTie.charOf a f ψ = GlobalTheory.SeriesTie.charOf a f' ψ := by
  have hv : ∀ x, ∃ σ, a.pull ψ x = ψ σ := by
    intro x
    unfold Recip.pull GlobalTheory.SeriesTie.descend
    split_ifs with hc
    · obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective _ (a.sym x)
      refine ⟨σ, ?_⟩
      rw [MonoidHom.comp_apply, ← hσ]
      rfl
    · exact ⟨1, by simp⟩
  refine MonoidHom.ext fun x => ?_
  obtain ⟨σ, hσ⟩ := hv x
  simp only [GlobalTheory.SeriesTie.charOf, MonoidHom.comp_apply, hσ]
  rw [show Units.map f.toMonoidHom (ψ σ) = Units.map f'.toMonoidHom (ψ σ) from Units.ext (h σ)]


open Classical in
def withTau (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : Setup D.ntw :=
  { ρ with
    e := fun i b => if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b
    ek := fun i b k => if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k }


open Classical in
theorem withTau_e (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) :
    (withTau ρ t s τ).e i b = if i = t ∧ b = s then τ.toRingHom.comp (ρ.e i b) else ρ.e i b := rfl


open Classical in
theorem withTau_ek (ρ : Setup D.ntw) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) (i : D.ntw.Tw) (b : Bool) (k : ℕ) :
    (withTau ρ t s τ).ek i b k = if i = t ∧ b = s then τ.toRingHom.comp (ρ.ek i b k) else ρ.ek i b k := rfl

theorem withTau_good {ρ : Setup D.ntw} (hρ : ρ.Good) (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ)
    (hfix : ∀ y, τ (embLL0 D y) = embLL0 D y)
    (hδ : ∀ σ, τ (ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t)
        ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) =
      ρ.eO t s (algebraMap (D.ntw.O0 t) (D.ntw.O t) ((Formalism.MainNotions.BlochKatoReduction.Gen.psiAt s (D.ntw.delta t) σ : (D.ntw.O0 t)ˣ) : D.ntw.O0 t))) :
    (withTau ρ t s τ).Good := by
  refine ⟨hρ.rc, hρ.ch, hρ.bad_ne, hρ.goodSetup_bad_mem_badPlaces, hρ.goodSetup_badPlaces_conj, hρ.goodSetup_placesOverTwo_subset, hρ.goodSetup_count_eq_zero_off_badPlaces, ?_, ?_, hρ.base, hρ.latS, hρ.latT, hρ.Pg,
    ?_, hρ.weil, hρ.classes⟩
  · intro i b x
    rw [withTau_e]
    split_ifs with h
    · show τ (ρ.e i b _) = _
      rw [hρ.e_LL0]
      exact hfix x
    · exact hρ.e_LL0 i b x
  · intro i b k x
    show (withTau ρ t s τ).ek i b k _ = (withTau ρ t s τ).e i b _
    rw [withTau_e, withTau_ek]
    split_ifs with h
    · exact congrArg τ (hρ.ek_e i b k x)
    · exact hρ.ek_e i b k x
  · intro i j b
    show (ρ.B i j b).de = twistOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (ρ.ch i)
      (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
    rw [hρ.delta i j b]
    unfold twistOf
    have : GlobalTheory.SeriesTie.charOf ρ.rc ((ρ.eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) =
        GlobalTheory.SeriesTie.charOf ρ.rc (((withTau ρ t s τ).eO i b).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)))
          (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)) := by
      refine charOf_congr _ _ _ _ fun σ => ?_
      show ρ.e i b _ = (withTau ρ t s τ).e i b _
      rw [withTau_e]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact (hδ σ).symm
      · rfl
    rw [this]

theorem ext_onSmallField {c : NChoice D} (hc : NChTie D c) (w : D.what₂.places.Pl) {ρ : Setup D.ntw} (hρ : ρ.Good)
    (g : FractionRing (c.Oe w) →+* ℂ)
    (hg : ∀ a : D.ntw.Ok (c.twI w) (c.k' w), g (algebraMap (c.Oe w) _ (algebraMap _ (c.Oe w) a)) =
      ρ.ek (c.twI w) (c.sd w) (c.k' w) (algebraMap _ _ a))
    (y : D.LL0) : g (c.embW w (y : D.what₂.LL)) = embLL0 D y := by
  obtain ⟨⟨y', z⟩, hz⟩ := IsLocalization.surj (nonZeroDivisors (D.ntw.O0 (c.twI w)))
    ((if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) y)
  have hz0 : (z : D.ntw.O0 (c.twI w)) ≠ 0 := nonZeroDivisors.coe_ne_zero z
  have e1 : ∀ x : D.ntw.O (c.twI w), ρ.ek (c.twI w) (c.sd w) (c.k' w)
      (algebraMap _ (FractionRing _) (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) x)) =
      ρ.e (c.twI w) (c.sd w) (algebraMap _ _ x) := hρ.ek_e (c.twI w) (c.sd w) (c.k' w)
  have h1 := congrArg g (hc.embedding_baseField_condition w y y' z hz0 hz)
  rw [map_mul, hg, hg, e1, e1] at h1
  have h2 : sideEmb D.ntw (c.twI w) (c.sd w) y * algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z) =
      algebraMap _ _ (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y') := by
    have := congrArg (IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w))
      (K := FractionRing (D.ntw.O0 (c.twI w))) (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) hz
    simp only [map_mul, IsFractionRing.map, IsLocalization.map_eq] at this
    exact this
  have h3 := congrArg (ρ.e (c.twI w) (c.sd w)) h2
  rw [map_mul, hρ.e_LL0] at h3
  have hne : ρ.e (c.twI w) (c.sd w) (algebraMap _ (FractionRing (D.ntw.O (c.twI w)))
      (algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z)) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      ((map_ne_zero_iff _ (D.ntw.O_inj (c.twI w))).2 hz0))
  exact mul_right_cancel₀ hne (h1.trans h3.symm)

section Point

theorem realPin_withTau {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    {Rl : RealDat3 D A3 Ks} {cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (h : RealPin Rl cG ρ)
    (t : D.ntw.Tw) (s : Bool) (τ : ℂ ≃+* ℂ) : RealPin Rl cG (withTau ρ t s τ) :=
  { psi := h.psi, inf := h.inf, cartT := h.cartT, onbS := h.onbS, onbT := h.onbT, latS := h.latS, latT := h.latT,
    frS := h.frS, frT := h.frT, vac := h.vac, Pg := h.Pg, grp := h.grp, mu0 := h.mu0, eta := h.eta, delta := h.delta,
    deltaPl := h.deltaPl, ap := h.ap, am := h.am }

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem adapt_at (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m) (hm : More p) (ρ : Setup D.ntw) (hρ : ρ.Good)
    (hpin : RealPin p.R p.cG ρ) : ∃ ρ' : Setup D.ntw, ρ'.Good ∧ SameBut ρ ρ' ∧ Adapted p w ρ' := by
  haveI : Module.Finite (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w) := ex.nch.Oe_fin w
  obtain ⟨g, hg⟩ := exists_ext_frac (ex.nch.Oe_inj w) (ρ.ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w))
  haveI : Countable D.what₂.LL := Countable.of_equiv _ (Module.finBasis ℚ D.what₂.LL).equivFun.symm.toEquiv
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq D.what₂.LL (g.comp (ex.nch.embW w)) D.what₂.embLL
  have hfix : ∀ y : D.LL0, τ (embLL0 D y) = embLL0 D y := fun y => by
    have h := ext_onSmallField ex.nch_tie w hρ g hg y
    have h2 : τ (g (ex.nch.embW w (y : D.what₂.LL))) = D.what₂.embLL y := hτ _
    rw [h] at h2
    exact h2
  have hχ : (p.R.C.delAt (D.ntw.l (ex.nch.twI w))).ValuesIn 0 (embLL0 D) := by
    have hv := hm.2.2.small.val
    unfold CharFrame.delAt
    split_ifs
    exacts [hv.del', hv.del]
  have hδ := GlobalTheory.T.ringAut_fixing_smallField_fixes_delta_values ρ hρ (ex.nch.twI w) j (ex.nch.sd w) _ (hpin.delta _ j _) hχ τ hfix
  refine ⟨withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ, withTau_good hρ _ _ τ hfix hδ, ⟨rfl, rfl, rfl, rfl, rfl⟩, realPin_withTau hpin _ _ τ,
    τ.toRingHom.comp g, fun x => hτ x, fun a => ?_⟩
  show τ (g _) = (withTau ρ (ex.nch.twI w) (ex.nch.sd w) τ).ek (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) _
  rw [withTau_ek, if_pos ⟨rfl, rfl⟩]
  exact congrArg τ (hg a)

end Point

end GlobalTheory.BigOn.Exp.Adapt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalExistence
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem li_one_tmul_of_li {O K' M : Type} [CommRing O] [IsDomain O] [Field K'] [Algebra O K']
    (hO : Function.Injective (algebraMap O K'))
    [AddCommGroup M] [Module (FractionRing O) M] [Module O M] [IsScalarTower O (FractionRing O) M] {n : ℕ} (m : Fin n → M)
    (hm : LinearIndependent (FractionRing O) m) :
    LinearIndependent K' fun a => ((1 : K') ⊗ₜ[O] m a : K' ⊗[O] M) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination (FractionRing O) m).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hm.fintypeLinearCombination_injective)
  have hgm : ∀ a, g (m a) = Pi.single a 1 := fun a => by
    have h := LinearMap.congr_fun hg (Pi.single a 1)
    simp only [LinearMap.comp_apply, LinearMap.id_apply, Fintype.linearCombination_apply_single, one_smul] at h
    exact h
  let κ : FractionRing O →ₐ[O] K' := IsFractionRing.liftAlgHom (K := FractionRing O) (g := Algebra.ofId O K') hO
  let φ : M →ₗ[O] (Fin n → K') := LinearMap.pi fun k =>
    κ.toLinearMap.comp ((LinearMap.proj k).comp (g.restrictScalars O))
  let F := φ.liftBaseChange K'
  have hF : ∀ a, F ((1 : K') ⊗ₜ[O] m a) = Pi.single a 1 := fun a => by
    simp only [F, LinearMap.liftBaseChange_tmul, one_smul]
    funext k
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.proj_apply, hgm,
      AlgHom.toLinearMap_apply]
    by_cases h : k = a
    · subst h; simp
    · simp [Pi.single_apply, h]
  refine LinearIndependent.of_comp F ?_
  have : (F ∘ fun a => ((1 : K') ⊗ₜ[O] m a : K' ⊗[O] M)) = fun a => Pi.single a (1 : K') := funext hF
  rw [this]
  convert (Pi.basisFun K' (Fin n)).linearIndependent using 1
  funext a
  exact (Pi.basisFun_apply K' (Fin n) a).symm

theorem embW_tmul_eq {D : D7} (S : NX.RatDat D.ntw) (c : NChoice D) (hc : NChTie D c) (w : D.what₂.places.Pl) {M : Type}
    [AddCommGroup M] [Module (FractionRing (D.ntw.O (c.twI w))) M] [Module (D.ntw.O (c.twI w)) M]
    [IsScalarTower (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) M] (a : S.Ks) (m : M) :
    (c.embW w (algebraMap S.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (c.twI w)] m : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)]
        ((show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) • m) := by
  classical
  set e0 := (if c.sd w then D.ntw.emb0 (c.twI w) else D.ntw.emb0b (c.twI w)) (S.kKs a) with he0
  obtain ⟨y, z, hz, hyz⟩ := IsFractionRing.div_surjective (A := D.ntw.O0 (c.twI w)) e0
  have hz0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
  have hz' : algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hz
  have hE : e0 * algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) z =
      algebraMap (D.ntw.O0 (c.twI w)) (FractionRing (D.ntw.O0 (c.twI w))) y := by
    rw [← hyz, div_mul_cancel₀ _ hz']
  have h1 := hc.embedding_baseField_condition w (S.kKs a) y z hz0 hE
  rw [S.kKs_spec] at h1
  set zO := algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) z with hzO
  set yO := algebraMap (D.ntw.O0 (c.twI w)) (D.ntw.O (c.twI w)) y with hyO
  have hφ : ∀ u : D.ntw.O (c.twI w), algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) u =
      algebraMap (c.Oe w) (FractionRing (c.Oe w)) (algebraMap (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)
        (algebraMap (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) u)) := fun u => by
    rw [IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (c.Oe w) (FractionRing (c.Oe w)),
      IsScalarTower.algebraMap_apply (D.ntw.O (c.twI w)) (D.ntw.Ok (c.twI w) (c.k' w)) (c.Oe w)]
  have hι : (show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) *
      algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) zO = algebraMap (D.ntw.O (c.twI w)) (FractionRing (D.ntw.O (c.twI w))) yO := by
    have hm : ∀ u : D.ntw.O0 (c.twI w), IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O0 (c.twI w)))
        (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w)) (algebraMap _ _ u) = algebraMap (D.ntw.O (c.twI w)) _ (algebraMap _ _ u) :=
      fun u => IsLocalization.map_eq _ _
    change (IsFractionRing.map (A := D.ntw.O0 (c.twI w)) (B := D.ntw.O (c.twI w)) (K := FractionRing (D.ntw.O0 (c.twI w)))
        (L := FractionRing (D.ntw.O (c.twI w))) (D.ntw.O_inj (c.twI w))) e0 * _ = _
    rw [hzO, hyO, ← hm, ← hm, ← map_mul, hE]
  have hζ : algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) zO ≠ 0 := by
    rw [hφ]
    intro h0
    apply hz0
    have := IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w)) (h0.trans (map_zero _).symm)
    have := c.Oe_inj w (this.trans (map_zero _).symm)
    have := D.ntw.Ok_inj (c.twI w) (c.k' w) (this.trans (map_zero _).symm)
    exact D.ntw.O_inj (c.twI w) (this.trans (map_zero _).symm)
  have key : ∀ t : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M,
      zO • t = algebraMap (D.ntw.O (c.twI w)) (FractionRing (c.Oe w)) zO • t :=
    fun t => (algebraMap_smul (FractionRing (c.Oe w)) zO t).symm
  have hL : zO • (c.embW w (algebraMap S.Ks D.what₂.LL a) ⊗ₜ[D.ntw.O (c.twI w)] m : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] (yO • m) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, hφ, mul_comm, h1, ← hφ, Algebra.algebraMap_eq_smul_one,
      TensorProduct.smul_tmul]
  have hR : zO • ((1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)]
      ((show FractionRing (D.ntw.O (c.twI w)) from NX.ιK S (c.twI w) (c.sd w) a) • m) : FractionRing (c.Oe w) ⊗[D.ntw.O (c.twI w)] M) =
      (1 : FractionRing (c.Oe w)) ⊗ₜ[D.ntw.O (c.twI w)] (yO • m) := by
    rw [← TensorProduct.tmul_smul]
    congr 1
    rw [← algebraMap_smul (FractionRing (D.ntw.O (c.twI w))) zO, smul_smul, mul_comm, hι, algebraMap_smul]
  have h2 := (key _).symm.trans (hL.trans (hR.symm.trans (key _)))
  exact smul_right_injective _ hζ h2

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem canEx_at (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m) :
    ∃ rd : Can p w j, IsCan p rd ∧ ∃ (n : ℕ) (β : Module.Basis (Fin n) D.what₂.LL (Fin ((R2 p).nW j) → D.what₂.LL)),
      LinearIndependent (FractionRing (ex.nch.Oe w)) fun a => rd (β a) := by
  classical
  obtain ⟨n, b, hbK, hliK, hspK, hliL, hspL⟩ := p.fw.ks j
  have hEs : ∀ (a : p.Sx.Ks) (v : p.Sx.WL ((j : ℕ) + 1)), (p.nexp.fi j).e (a • v) = (p.nexp.fi j).eK a • (p.nexp.fi j).e v :=
    fun a v => by
      rw [← algebraMap_smul D.what₂.LL a v, LinearEquiv.map_smul, ← (p.nexp.fi j).eK_LL, algebraMap_smul]
  let f : Fin n → NX.FmK p.Sx ((j : ℕ) + 1) := fun k =>
    ⟨(p.nexp.fi j).e.symm (b k), ((p.nexp.fi j).wk _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hbK k)⟩
  have hf : ∀ k, (p.nexp.fi j).e (f k).1 = b k := fun k => LinearEquiv.apply_symm_apply _ _
  let v : NX.FmK p.Sx ((j : ℕ) + 1) →ₗ[p.Sx.Ks] p.Sx.WL ((j : ℕ) + 1) := (p.Sx.A ((j : ℕ) + 1)).WK.subtype
  have hv : ∀ g, v g = g.1 := fun _ => rfl
  have hsum : ∀ a : Fin n → p.Sx.Ks, (p.nexp.fi j).e (∑ k, a k • f k).1 = ∑ k, (p.nexp.fi j).eK (a k) • b k := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hv, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hv, hEs, hf]
  have hdec : ∀ g : NX.FmK p.Sx ((j : ℕ) + 1), ∃ a : Fin n → p.Sx.Ks, g = ∑ k, a k • f k := by
    intro g
    have hg : (p.nexp.fi j).e g.1 ∈ (p.R.FW j).WK := ((p.nexp.fi j).wk _).1 g.2
    rw [← hspK, Submodule.mem_span_range_iff_exists_fun] at hg
    obtain ⟨c, hc⟩ := hg
    refine ⟨fun k => (p.nexp.fi j).eK.symm (c k), Subtype.ext ((p.nexp.fi j).e.injective ?_)⟩
    rw [hsum, ← hc]
    simp only [RingEquiv.apply_symm_apply]
  have hliF : LinearIndependent p.Sx.Ks f := by
    rw [Fintype.linearIndependent_iff]
    intro a ha k
    have h0 : ∑ k, (p.nexp.fi j).eK (a k) • b k = 0 := by
      rw [← hsum, ha, ← hv, map_zero, map_zero]
    have := (Fintype.linearIndependent_iff.1 hliK) _ h0 k
    exact (map_eq_zero_iff _ (p.nexp.fi j).eK.injective).1 this
  let bK : Module.Basis (Fin n) p.Sx.Ks (NX.FmK p.Sx ((j : ℕ) + 1)) := Module.Basis.mk hliF (fun g _ => by
    obtain ⟨a, rfl⟩ := hdec g
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  set eF := p.nexp.eF (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) (Nat.le_add_left _ _) j.2 with heF
  let m : Fin n → D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) := fun k =>
    eF.symm ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k)
  let t : Fin n → Tgt ex w j := fun k => (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] m k
  let β : Module.Basis (Fin n) D.what₂.LL (Fin ((R2 p).nW j) → D.what₂.LL) := Module.Basis.mk hliL hspL.ge
  have hβ : ∀ k, β k = b k := fun k => Module.Basis.mk_apply _ _ _
  let rd : Can p w j :=
    { toFun := fun x => ∑ k, ex.nch.embW w (β.equivFun x k) • t k
      map_add' := fun x y => by simp only [map_add (f := _), Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum] }
  have hrd : ∀ x, rd x = ∑ k, ex.nch.embW w (β.equivFun x k) • t k := fun _ => rfl
  refine ⟨rd, fun g => ?_, n, β, ?_⟩
  · obtain ⟨a, rfl⟩ := hdec g
    have hx : (p.nexp.fi j).e (∑ k, a k • f k).1 = β.equivFun.symm fun k => algebraMap p.Sx.Ks D.what₂.LL (a k) := by
      rw [hsum, Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hβ, ← (p.nexp.fi j).eK_LL]
      exact (algebraMap_smul D.what₂.LL _ _).symm
    have hterm : ∀ k, ex.nch.embW w (algebraMap p.Sx.Ks D.what₂.LL (a k)) • t k =
        (1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)]
          eF.symm ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] (a k • f k)) := fun k => by
      simp only [t, m]
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, embW_tmul_eq p.Sx ex.nch ex.nch_tie w]
      congr 1
      rw [TensorProduct.tmul_smul, ← algebraMap_smul (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) (a k)]
      exact (eF.symm.map_smul _ _).symm
    refine (hrd _).trans ?_
    rw [hx, LinearEquiv.apply_symm_apply, Finset.sum_congr rfl fun k _ => hterm k, ← TensorProduct.tmul_sum]
    congr 1
    rw [TensorProduct.tmul_sum]
    exact (map_sum eF.symm _ _).symm
  · have hB : LinearIndependent (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) fun k =>
        ((1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k :
          NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w) ⊗[p.Sx.Ks] NX.FmK p.Sx ((j : ℕ) + 1)) := by
      have := (Algebra.TensorProduct.basis (NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) bK).linearIndependent
      convert this using 1
      funext k
      rw [Algebra.TensorProduct.basis_apply, Module.Basis.mk_apply]
    let u : Fin n → NX.Fm p.Sx (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w) := fun k =>
      (1 : NX.KB p.Sx (ex.nch.twI w) (ex.nch.sd w)) ⊗ₜ[p.Sx.Ks] f k
    have hB' : LinearIndependent (FractionRing (D.ntw.O (ex.nch.twI w))) u := hB
    have hm : LinearIndependent (FractionRing (D.ntw.O (ex.nch.twI w))) m := hB'.map' eF.symm.toLinearMap eF.symm.ker
    have hO : Function.Injective (algebraMap (D.ntw.O (ex.nch.twI w)) (FractionRing (ex.nch.Oe w))) := by
      have e1 : algebraMap (D.ntw.O (ex.nch.twI w)) (FractionRing (ex.nch.Oe w)) =
          (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w))).comp
            ((algebraMap (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) (ex.nch.Oe w)).comp
              (algebraMap (D.ntw.O (ex.nch.twI w)) (D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)))) := by
        rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
      rw [e1, RingHom.coe_comp, RingHom.coe_comp]
      exact (IsFractionRing.injective _ _).comp ((ex.nch.Oe_inj w).comp (D.ntw.Ok_inj _ _))
    have hrb : ∀ a, rd (β a) = t a := fun a => by
      rw [hrd, Finset.sum_eq_single a]
      · simp [Module.Basis.equivFun_self]
      · intro k _ hk
        simp [Module.Basis.equivFun_self, Ne.symm hk]
      · intro h; exact absurd (Finset.mem_univ a) h
    have := li_one_tmul_of_li (K' := FractionRing (ex.nch.Oe w)) hO m hm
    have ht : (fun a => rd (β a)) = t := funext hrb
    rw [ht]
    exact this

end Point

end GlobalTheory.BigOn.Exp

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp
end
end
