module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceStepFactorInverseAwayUnit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussMulUnram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (gauss unifAt PsiUnr)

noncomputable section

namespace GlobalTheory.GaussUnr

open ValuativeRel GlobalTheory.SplitFlip GlobalTheory.GaussNonvanish

theorem gauss_mul_unram : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ), (∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ξ x = 1) →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ ∧
      ∃ y : (Fv F v)ˣ, gauss ψ (ν₀ * ξ) = (((ξ y)⁻¹ : ℂˣ) : ℂ) * gauss ψ ν₀ := by
  intro F _ _ ψ v ν₀ ξ hξ
  have hϖ : IsUnif (unifAt v) := (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  have hunit : ∀ x : (Fv F v)ˣ, valuation (Fv F v) (x : Fv F v) = 1 → ξ x = 1 := fun x hx => by
    apply hξ x
    · exact (val_le_one_iff v _).1 hx.le
    · apply (val_le_one_iff v _).1
      rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]
  have hce : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (ν₀ * ξ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
    congr 1
    ext c
    simp only [Set.mem_setOf_eq, CondLE]
    refine forall₂_congr fun x hx => ?_
    rw [MonoidHom.mul_apply, hunit x hx.1, mul_one]
  refine ⟨hce, ?_⟩
  unfold gauss
  rw [hce]
  generalize GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀ = c
  rcases Nat.eq_zero_or_pos c with h0 | hc1
  · subst h0
    have hsu : ∀ a b : (Res (Fv F v) 0)ˣ, a = b := fun a b =>
      Units.ext ((Ideal.Quotient.subsingleton_iff.2 (by simp)).elim _ _)
    classical
    rw [Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim), Fintype.sum_eq_single 1 (fun y hy => (hy (hsu y 1)).elim)]
    by_cases h : ((Quotient.out (1 : (Res (Fv F v) 0)ˣ).1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · refine ⟨1, ?_⟩
      rw [dite_eq_left h, dite_eq_left h, mul_zero]
    · refine ⟨Units.mk0 _ h, ?_⟩
      rw [dite_eq_right h, dite_eq_right h, MonoidHom.mul_apply, mul_inv, Units.val_mul, mul_comm (((ν₀ _)⁻¹ : ℂˣ) : ℂ),
        mul_assoc]
  · refine ⟨1, ?_⟩
    rw [map_one, inv_one, Units.val_one, one_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : ((Quotient.out y.1 : (ValuativeRel.valuation (Fv F v)).integer) : Fv F v) = 0
    · rw [dite_eq_left h, dite_eq_left h]
    · rw [dite_eq_right h, dite_eq_right h, MonoidHom.mul_apply, hunit _ (val_rep_unit hϖ hc1 y), mul_one]

end GlobalTheory.GaussUnr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

namespace GlobalTheory.SqStepArith

theorem chrW_chs_eq_mul {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    chrW (GlobalTheory.SqStep.chs G i j t).ν τ = chrW (GlobalTheory.SqStep.chs G i j μ₀).ν τ *
      ((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime τ)).comp
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom) := by
  have e : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    simp only [nuH, hL.xi_base, mul_one]
    exact (div_mul_eq_mul_div _ _ _).symm
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.mul_apply, chrW_chs G hL, chrW_chs G hL, MonoidHom.comp_apply, e]
  rfl

theorem chrW_chs_continuous {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    Continuous (fun x : (Fv D.host.F v)ˣ => (chrW (GlobalTheory.SqStep.chs G i j t).ν τ x : ℂ)) := by
  refine GlobalTheory.StepFacNe.chrW_continuous _ ?_ τ
  have e : (GlobalTheory.SqStep.chs G i j t).ν = G.nu t i (j + 1) := by
    show (Lc.mu t (j + 1) * Lc.eta ^ _) / (G.ch.chi _ * Lc.eta ^ _) = _
    rw [mul_div_mul_right_eq_div]
    rfl
  rw [e]
  exact (chrEq_nu G t i j hL).1.1

theorem chrW_chs_norm {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc)
    (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (x : (Fv D.host.F v)ˣ) : ‖(chrW (GlobalTheory.SqStep.chs G i j t).ν τ x : ℂ)‖ = 1 :=
  Circle.norm_coe _

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

open Formalism.L2.Host in
theorem levelLe_mul {L : Type} [Field L] [NumberField L] {a b : HChar L} {w : HeightOneSpectrum (𝓞 L)} {n : ℕ}
    (ha : a.LevelLe w n) (hb : b.LevelLe w n) : (a * b).LevelLe w n := fun x hx h => by
  change a.loc w x * b.loc w x = 1
  rw [ha x hx h, hb x hx h, one_mul]

open Formalism.L2.Host in
theorem levelLe_inv {L : Type} [Field L] [NumberField L] {a : HChar L} {w : HeightOneSpectrum (𝓞 L)} {n : ℕ}
    (ha : a.LevelLe w n) : (a⁻¹).LevelLe w n := fun x hx h => by
  change (a.loc w x)⁻¹ = 1
  rw [ha x hx h, inv_one]

open Formalism.L2.Host in
theorem levelLe_mono {L : Type} [Field L] [NumberField L] {a : HChar L} {w : HeightOneSpectrum (𝓞 L)} {m n : ℕ}
    (ha : a.LevelLe w m) (hmn : m ≤ n) : a.LevelLe w n := fun x hx h =>
  ha x hx (h.trans (WithZero.exp_le_exp.2 (by omega)))

theorem nuH_levelLe_two {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (i j : Fin D.R.m) (t : T) (PP : HeightOneSpectrum (𝓞 D.host.E)) (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ S1 D) :
    (nuH G t i j).LevelLe PP 2 ∧ ¬ (nuH G t i j).LevelLe PP 1 := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have hchi := G.ch.lev1 _ hm.1 hm.2 PP hPP
  have hmu : (Lc.C.mu0 j).LevelLe PP 1 := (Lc.C.isMu0 j).tame PP
  have hxi : (Lc.xiH t).LevelLe PP 1 := hL.xi_tame t PP
  refine ⟨?_, fun h => hchi.2 ?_⟩
  · rw [nuH, div_eq_mul_inv]
    exact levelLe_mul (levelLe_mul (levelLe_mono hmu (by omega)) (levelLe_mono hxi (by omega))) (levelLe_inv hchi.1)
  · have e : G.ch.chiH (D.R.m - i) = Lc.C.mu0 j * Lc.xiH t / nuH G t i j := by
      rw [nuH, div_div_cancel]
    rw [e, div_eq_mul_inv]
    exact levelLe_mul (levelLe_mul hmu hxi) (levelLe_inv h)


attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem condExp_comp_eq_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (χ : HChar E)
    (h2 : χ.LevelLe (GlobalTheory.AdelicU.splitPrime τ) 2) (h1 : ¬ χ.LevelLe (GlobalTheory.AdelicU.splitPrime τ) 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ((χ.loc (GlobalTheory.AdelicU.splitPrime τ)).comp
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) = 2 := by
  have key : ∀ n, GlobalTheory.SplitFlip.CondLE (unifAt v) n ((χ.loc (GlobalTheory.AdelicU.splitPrime τ)).comp
      (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom)) ↔ χ.LevelLe (GlobalTheory.AdelicU.splitPrime τ) n :=
    fun n => GlobalTheory.CondLESplit.condLE_iff τ _ n
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
  refine le_antisymm (Nat.sInf_le ((key 2).2 h2)) (le_csInf ⟨2, (key 2).2 h2⟩ fun c hc => ?_)
  by_contra hlt
  exact h1 (levelLe_mono ((key c).1 hc) (by omega))

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem factor_unr {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)}
    (ν₀ ξ : (Fv F v)ˣ →* ℂˣ)
    (hξ : ∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ξ x = 1)
    (s : (Fv F v)ˣ) (z : ℤ) (h0 : (((ν₀ * ξ) s : ℂˣ) : ℂ) * eps ψ (ν₀ * ξ) z ≠ 0) :
    ∃ u : (Fv F v)ˣ, ((ν₀ s : ℂˣ) : ℂ) * eps ψ ν₀ z = ((ξ u : ℂˣ) : ℂ) * ((((ν₀ * ξ) s : ℂˣ) : ℂ) * eps ψ (ν₀ * ξ) z) := by
  obtain ⟨hc, y, hg⟩ := GlobalTheory.GaussUnr.gauss_mul_unram ψ ν₀ ξ hξ
  have he := eps_mul_of_condExp ψ ν₀ ξ s z hc
  have hG1 : gauss ψ (ν₀ * ξ) ≠ 0 := by
    intro h; apply h0; unfold eps; rw [h]; ring
  have hG0 : gauss ψ ν₀ ≠ 0 := by
    intro h; apply hG1; rw [hg, h, mul_zero]
  refine ⟨y * (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀)⁻¹, ?_⟩
  rw [hg] at he
  simp only [Units.val_inv_eq_inv_val] at he
  have hy : ((ξ y : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hb : ((ξ (s * unifAt v ^ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp ν₀) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  refine mul_right_cancel₀ (mul_ne_zero (inv_ne_zero hy) hG0) ?_
  rw [he]
  field_simp


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem factor_ram {F : Type} [Field F] [NumberField F] {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)
    (ψ : AddChar (AF F) ℂ) {v : HeightOneSpectrum (𝓞 F)} (ν₀ ξ : (Fv F v)ˣ →* ℂˣ) (s : (Fv F v)ˣ) (z : ℤ) (c : ℕ)
    (hc0 : condExp ν₀ = c) (hc1 : condExp (ν₀ * ξ) = c) (h1 : 1 ≤ c) (hψ : PsiUnr ψ v)
    (hcont0 : Continuous (fun x : (Fv F v)ˣ => (ν₀ x : ℂ))) (hcont1 : Continuous (fun x : (Fv F v)ˣ => ((ν₀ * ξ) x : ℂ)))
    (hun0 : ∀ x, ‖(ν₀ x : ℂ)‖ = 1) (hun1 : ∀ x, ‖((ν₀ * ξ) x : ℂ)‖ = 1)
    (hr0 : ∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → (ν₀ x : ℂ) ∈ Set.range σ)
    (hr1 : ∀ x : (Fv F v)ˣ, (x : Fv F v) ∈ v.adicCompletionIntegers F →
      ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F → ((ν₀ * ξ) x : ℂ) ∈ Set.range σ)
    (hζ : ∀ ζ : ℂ, ζ ^ (Ideal.absNorm v.asIdeal ^ c) = 1 → ζ ∈ Set.range σ)
    (h0 : (((ν₀ * ξ) s : ℂˣ) : ℂ) * eps ψ (ν₀ * ξ) z ≠ 0) :
    ∃ g g' : 𝓞 K, g ∣ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ c ∧ g' ∣ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ c ∧
      ((ν₀ s : ℂˣ) : ℂ) * eps ψ ν₀ z =
        (((ξ (s * unifAt v ^ c))⁻¹ : ℂˣ) : ℂ) * (σ (g : K) / σ (g' : K)) * ((((ν₀ * ξ) s : ℂˣ) : ℂ) * eps ψ (ν₀ * ξ) z) := by
  obtain ⟨g, g₁, hg, hgg⟩ := GlobalTheory.GaussDiv.gauss_dvd_pow σ ψ v ν₀ hψ hcont0 hun0 (hc0 ▸ h1) hr0 (hc0 ▸ hζ)
  obtain ⟨g', g₁', hg', hgg'⟩ := GlobalTheory.GaussDiv.gauss_dvd_pow σ ψ v (ν₀ * ξ) hψ hcont1 hun1 (hc1 ▸ h1) hr1 (hc1 ▸ hζ)
  have he := eps_mul_of_condExp ψ ν₀ ξ s z (hc1.trans hc0.symm)
  have hG1 : gauss ψ (ν₀ * ξ) ≠ 0 := by
    intro h; apply h0; unfold eps; rw [h]; ring
  refine ⟨g, g', ⟨g₁, by rw [hgg, hc0]⟩, ⟨g₁', by rw [hgg', hc1]⟩, ?_⟩
  rw [hg, hg', ← hc0]
  calc _ = ((ν₀ s : ℂˣ) : ℂ) * eps ψ ν₀ z * gauss ψ (ν₀ * ξ) / gauss ψ (ν₀ * ξ) := (mul_div_cancel_right₀ _ hG1).symm
    _ = _ := by rw [he]; ring

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith


open Formalism.L2.Host in
theorem nuH_loc_mem {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} {G : GridData Lc sc} {μ₀ : T} {W : G.Weil}
    {S : GridChoice W Set.univ} (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (y : (w.adicCompletion D.host.E)ˣ) :
    (((nuH G t i j).loc w y : ℂˣ) : ℂ) ∈ Set.range D.what₂.embLL := by
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have h1 : _ ∈ D.what₂.embLL.fieldRange := RingHom.mem_fieldRange.2 (hN.chars.mu0 j w y)
  have h2 : _ ∈ D.what₂.embLL.fieldRange := RingHom.mem_fieldRange.2 (hN.chars.xi t w y)
  have h3 : _ ∈ D.what₂.embLL.fieldRange := RingHom.mem_fieldRange.2 (hN.chars.chi _ hm.1 hm.2 w y)
  refine RingHom.mem_fieldRange.1 ?_
  change (((Lc.C.mu0 j).loc w y * (Lc.xiH t).loc w y *
    ((G.ch.chiH (D.R.m - i)).loc w y)⁻¹ : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
  rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  exact mul_mem (mul_mem h1 h2) (inv_mem h3)


open Formalism.L2.Host in
theorem isUnitAt_complMap {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) (h1 : (x : Fv F v) ∈ v.adicCompletionIntegers F)
    (h2 : ((x⁻¹ : (Fv F v)ˣ) : Fv F v) ∈ v.adicCompletionIntegers F) :
    IsUnitAt (GlobalTheory.AdelicU.splitPrime τ) (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom x) := by
  unfold IsUnitAt
  rw [Units.coe_map]
  show Valued.v (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ) (x : Fv F v)) = 1
  rw [GlobalTheory.LFun.SplitTie.valued_complMap τ (GlobalTheory.AdelicU.splitPrime_under τ)]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1 h2
  rw [Units.val_inv_eq_inv_val, map_inv₀] at h2
  have hne : Valued.v (x : Fv F v) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2)

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


set_option maxHeartbeats 1000000 in
open Formalism.L2.Host in
theorem base_place_factor_zero : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ),
    ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 →
    ∃ (b : D.what₂.LL) (g g' : 𝓞 D.what₂.LL), GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      g ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      g' ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      ((chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v)) z) =
        D.what₂.embLL (b * ((g : D.what₂.LL) / (g' : D.what₂.LL))) * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) := by
  intro D T Lc sc G μ₀ hL W S hN i j t Bs hB v hv s z h0
  classical
  have hwu : (GlobalTheory.AdelicU.splitPrime (Bs.τ v)).under (𝓞 D.host.F) = v.1 := GlobalTheory.AdelicU.splitPrime_under (Bs.τ v)
  have hν := chrW_chs_eq_mul G hL i j t (Bs.τ v)
  rw [hν] at h0 ⊢
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨hc1, -, -, -, -⟩ := GlobalTheory.Square.isAwayUnit_closure D.what₂.LL (Qn G t) hQn
  have hval : ∀ y, ∃ b : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      D.what₂.embLL b = (((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v)) y : ℂˣ) : ℂ) := by
    intro y
    obtain ⟨b, hb⟩ := hN.chars.xi t _ y
    obtain ⟨n, hn, hord⟩ := hL.xi_fin t
    refine ⟨b, hc1 b n hn ?_, hb⟩
    apply D.what₂.embLL.injective
    rw [map_pow, hb, map_one]
    have e := congrArg (fun χ : HChar D.host.E => ((χ.loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v)) y : ℂˣ) : ℂ)) hord
    exact e
  by_cases hu : ∀ x : (Fv D.host.F v.1)ˣ, (x : Fv D.host.F v.1) ∈ v.1.adicCompletionIntegers D.host.F →
      ((x⁻¹ : (Fv D.host.F v.1)ˣ) : Fv D.host.F v.1) ∈ v.1.adicCompletionIntegers D.host.F →
      (((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v))).comp
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom)) x = 1
  · obtain ⟨u, hu'⟩ := factor_unr Bs.ψ _ _ hu _ z h0
    obtain ⟨b, hb, hbe⟩ := hval (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom u)
    refine ⟨b, 1, 1, hb, one_dvd _, one_dvd _, ?_⟩
    rw [hu', div_self (by simp), mul_one, hbe]
    rfl
  · have hy0 : ∃ y0 : (Fv D.host.F v.1)ˣ, y0 = Units.map (Int.castRingHom (Fv D.host.F v.1)).toMonoidHom s := ⟨_, rfl⟩
    obtain ⟨y0, hy0⟩ := hy0
    have hy1 : ∃ y1 : (Fv D.host.F v.1)ˣ, y1 = (y0 * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v.1 ^ 2)⁻¹ := ⟨_, rfl⟩
    obtain ⟨y1, hy1⟩ := hy1
    obtain ⟨b, hb, hbe⟩ := hval (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom y1)
    have hram : ¬ (Lc.xiH t).UnrAt (GlobalTheory.AdelicU.splitPrime (Bs.τ v)) := fun h =>
      hu fun x h1 h2 => h _ (isUnitAt_complMap (Bs.τ v) x h1 h2)
    have hv0 : v.1 ≠ G.pl.v0 := by
      intro e
      rcases (hL.Q_ram t _).1 hram with h | ⟨PP', h, hc'⟩
      · exact G.pl.levelPlace_ne_basePlace t _ h (hwu.trans e)
      · exact G.pl.levelPlace_ne_basePlace t PP' h ((GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc').trans (hwu.trans e))
    have hv1 : v.1 ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left hv0
    have hce : condExp G.pl v.1 = 2 := if_neg hv0
    have hloc : GlobalTheory.AdelicU.splitPrime (Bs.τ v) ∈ locPl G t := hB.2.2.2 v (Finset.mem_union_left _ hv)
    have hw : GlobalTheory.AdelicU.splitPrime (Bs.τ v) = G.pl.w v.1 := by
      rcases Finset.mem_union.1 hloc with h | h
      · obtain ⟨v', hv', e⟩ := Finset.mem_image.1 h
        have e' : v' = v.1 := by rw [← G.pl.under_w hv', e, hwu]
        rw [← e, e']
      · have := G.pl.w_Q t _ h (hwu.symm ▸ hv1)
        rwa [hwu] at this
    have hdep : depthAt G (GlobalTheory.AdelicU.splitPrime (Bs.τ v)) = 2 := by
      rw [hw, (depthAt_w G hv).2]
      exact if_neg hv0
    have hroots := hN.roots t _ hloc
    rw [hdep, GlobalTheory.LFun.SplitChart.absNorm_splitPrime] at hroots
    have hchr : ∀ t', chrW (GlobalTheory.SqStep.chs G i j t').ν (Bs.τ v) = ((nuH G t' i j).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v))).comp
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom) := fun t' =>
      MonoidHom.ext fun x => chrW_chs G hL i j t' (Bs.τ v) x
    have hexp : ∀ t', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t').ν (Bs.τ v)) = 2 := fun t' => by
      obtain ⟨h2, h1⟩ := nuH_levelLe_two G hL i j t' _ (hwu.symm ▸ hv1)
      rw [hchr]
      exact condExp_comp_eq_two (Bs.τ v) _ h2 h1
    have hrange : ∀ t' x, (chrW (GlobalTheory.SqStep.chs G i j t').ν (Bs.τ v) x : ℂ) ∈ Set.range D.what₂.embLL := fun t' x => by
      rw [hchr]
      exact nuH_loc_mem hN i j t' _ _
    have e1 := hexp t
    have c1 := chrW_chs_continuous G hL i j t (Bs.τ v)
    have n1 := chrW_chs_norm G i j t (Bs.τ v)
    have r1 := hrange t
    rw [hν] at e1 c1 n1 r1
    have key := factor_ram D.what₂.embLL Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v))
      (((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v))).comp
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom))
      (Units.map (Int.castRingHom (Fv D.host.F v.1)).toMonoidHom s) z 2 (hexp μ₀) e1 (by norm_num)
    specialize key (hB.2.2.1 v.1 v.2)
    specialize key (chrW_chs_continuous G hL i j μ₀ (Bs.τ v))
    specialize key c1
    specialize key (chrW_chs_norm G i j μ₀ (Bs.τ v))
    specialize key n1
    specialize key (fun x _ _ => hrange μ₀ x)
    specialize key (fun x _ _ => r1 x)
    specialize key hroots
    have k2 := key h0
    rcases k2 with ⟨g, k3⟩
    rcases k3 with ⟨g', k4⟩
    have hg := k4.1
    have hg' := k4.2.1
    have he := k4.2.2
    refine ⟨b, g, g', hb, hce ▸ hg, hce ▸ hg', ?_⟩
    have hξ : ((((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v)))
        (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom y1) : ℂˣ) : ℂ) =
        ((((((Lc.xiH t).loc (GlobalTheory.AdelicU.splitPrime (Bs.τ v))).comp
          (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under (Bs.τ v))).toMonoidHom))
          (Units.map (Int.castRingHom (Fv D.host.F v.1)).toMonoidHom s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v.1 ^ 2))⁻¹ : ℂˣ) : ℂ) := by
      rw [hy1, hy0, map_inv, map_inv]
      rfl
    rw [he]
    rw [map_mul D.what₂.embLL]
    rw [map_div₀]
    rw [hbe, hξ]

end GlobalTheory.SqStepArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasePlaceCharacterFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_place_character_factor : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E), GlobalTheory.SqStep.BaseFits G W i j t Bs → ∀ (v : Bs.P), v.1 ∈ G.pl.S0 → ∀ (s : ℤˣ) (z : ℤ),
    ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) ≠ 0 →
    ∃ (b : D.what₂.LL) (g g' : 𝓞 D.what₂.LL), GlobalTheory.Square.IsAwayUnit (Qn G t) b ∧
      g ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      g' ∣ ((Ideal.absNorm v.1.asIdeal : ℕ) : 𝓞 D.what₂.LL) ^ condExp G.pl v.1 ∧
      ((chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j μ₀).ν (Bs.τ v)) z) =
        D.what₂.embLL (b * ((g : D.what₂.LL) / (g' : D.what₂.LL))) * ((chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW (GlobalTheory.SqStep.chs G i j t).ν (Bs.τ v)) z) := by
  first | exact @GlobalTheory.SqStepArith.base_place_factor_zero | exact GlobalTheory.SqStepArith.base_place_factor_zero | (intros; apply GlobalTheory.SqStepArith.base_place_factor_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotient
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqStepArith

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal)

theorem stepFac_ratio_core {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T} (hL : Lc.Is μ₀)
    (W : G.Weil) (S : GridChoice W Set.univ) (hN : NumbersIn D.what₂.embLL S μ₀) (i j : Fin D.R.m) (t : T)
    (Bs : Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ) (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ)
    (hB : GlobalTheory.SqStep.BaseFits G W i j t Bs) (h0 : stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0) :
    GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
      (stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  classical
  have hQn : 0 < Qn G t := Finset.prod_pos fun w _ => Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨hc1, -, hcmul, hcinv, -⟩ := GlobalTheory.Square.isAwayUnit_closure D.what₂.LL (Qn G t) hQn
  have hone : GlobalTheory.Square.IsAwayUnit (Qn G t) (1 : D.what₂.LL) := GlobalTheory.Square.IsAwayUnit.one _
  have hzpow : ∀ (x : D.what₂.LL) (n : ℕ), 0 < n → x ^ n = 1 → ∀ e : ℤ, GlobalTheory.Square.IsAwayUnit (Qn G t) (x ^ e) := by
    intro x n hn hx e
    refine hc1 _ n hn ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  have hprod : ∀ (s : Finset Bs.P) (f : Bs.P → D.what₂.LL), (∀ v ∈ s, GlobalTheory.Square.IsAwayUnit (Qn G t) (f v)) →
      GlobalTheory.Square.IsAwayUnit (Qn G t) (∏ v ∈ s, f v) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hone
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact hcmul _ _ (hf a (Finset.mem_insert_self _ _)) (ih fun v hv => hf v (Finset.mem_insert_of_mem hv))
  set σ := D.what₂.embLL with hσ
  set X₀ := GlobalTheory.SqStep.chs G i j μ₀ with hX₀
  set X := GlobalTheory.SqStep.chs G i j t with hX
  set Sz := G.pl.S0 with hS0
  set f : Chars D.host.F D.host.E → Bs.P → ℂ := fun Y v =>
    (chrW Y.ν (Bs.τ v) (Units.map (Int.castRingHom _).toMonoidHom s) : ℂ) * eps Bs.ψ (chrW Y.ν (Bs.τ v)) z with hf
  have hS0T : Sz ⊆ X.T := Finset.subset_union_left
  have hT0 : X₀.T = Sz := GlobalTheory.SqStepArith.chs_T_base G hL i j
  have hst : ∀ Y : Chars D.host.F D.host.E, stepFac Bs Y e₁ e₂ s 𝔟 𝔠 z =
      ((idealVal Y.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) * ((idealVal Y.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Y.T), f Y v := by
    intro Y
    simp only [stepFac, Units.val_mul, Units.val_zpow_eq_zpow_val, hf]

  have hsplit : ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T), f X v =
      (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v) *
        ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v := by
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T)) (fun v : Bs.P => v.1 ∈ Sz),
      Finset.filter_filter, Finset.filter_filter]
    congr 2
    · ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨hS0T h, h⟩⟩
  have hne : ∀ v : Bs.P, v.1 ∈ Sz → f X v ≠ 0 := by
    intro v hv
    rw [hst, hsplit] at h0
    have h1 := left_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using hv)
  have hS := fun (v : Bs.P) (hv : v.1 ∈ Sz) => GlobalTheory.T.base_place_character_factor G hL W S hN i j t Bs hB v hv s z (hne v hv)
  choose bS gS gS' hbS hgS hgS' heS using hS
  have hneT : ∀ v : Bs.P, v.1 ∈ X.T → v.1 ∉ Sz → f X v ≠ 0 := by
    intro v hv hv'
    rw [hst, hsplit] at h0
    have h1 := right_ne_zero_of_mul (right_ne_zero_of_mul h0)
    exact (Finset.prod_ne_zero_iff.1 h1) v (by simpa using And.intro hv hv')
  have hTw := fun (v : Bs.P) (hv : v.1 ∈ X.T) (hv' : v.1 ∉ Sz) => GlobalTheory.T.twistPlace_stepFactor_inverse_awayUnit G hL W S hN i j t Bs hB v hv hv' s z (hneT v hv hv')
  choose bT hbT heT using hTw
  obtain ⟨b1, ⟨n1, hn1, hb1⟩, e1⟩ := GlobalTheory.T.squareStepChar_idealValue_eq_base_mul_rootOfUnity G hL W S hN i j t 𝔟
  obtain ⟨b2, ⟨n2, hn2, hb2⟩, e2⟩ := GlobalTheory.T.squareStepChar_idealValue_eq_base_mul_rootOfUnity G hL W S hN i j t 𝔠
  let bS₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ Sz then bS v h else 1
  let bT₁ : Bs.P → D.what₂.LL := fun v => if h : v.1 ∈ X.T ∧ v.1 ∉ Sz then bT v h.1 h.2 else 1
  let g : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS ⟨v, h.1⟩ h.2 else 1
  let g' : HeightOneSpectrum (𝓞 D.host.F) → 𝓞 D.what₂.LL := fun v => if h : v ∈ Bs.P ∧ v ∈ Sz then gS' ⟨v, h.1⟩ h.2 else 1
  have hSP : ∀ v ∈ Sz, v ∈ Bs.P := fun v hv => hB.2.1 (hS0T hv)

  have hmap : ∀ F' : HeightOneSpectrum (𝓞 D.host.F) → D.what₂.LL,
      ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1 = ∏ v ∈ Sz, F' v := by
    intro F'
    rw [show (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), F' v.1) =
        ∏ v ∈ (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)).map (Function.Embedding.subtype _), F' v from
      (Finset.prod_map (Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz)) (Function.Embedding.subtype _) F').symm]
    congr 1
    ext v
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype]
    exact ⟨fun ⟨w, hw, e⟩ => e ▸ hw, fun hv => ⟨⟨v, hSP v hv⟩, hv, rfl⟩⟩
  refine ⟨b1 ^ (e₁ : ℤ) * b2 ^ (e₂ : ℤ) * (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
    (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v), g, g', ?_, ?_, ?_⟩
  · refine hcmul _ _ (hcmul _ _ (hcmul _ _ (hzpow b1 n1 hn1 hb1 _) (hzpow b2 n2 hn2 hb2 _)) ?_) ?_
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ Sz := by simpa using hv
      simp only [bS₁, dif_pos hv']
      exact hbS v hv'
    · refine hprod _ _ fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      exact hbT v hv'.1 hv'.2
  · intro v hv
    have h : v ∈ Bs.P ∧ v ∈ Sz := ⟨hSP v hv, hv⟩
    simp only [g, g', dif_pos h]
    exact ⟨hgS _ h.2, hgS' _ h.2⟩
  · have hA : ∀ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz),
        f X₀ v = σ (bS₁ v * ((g v.1 : D.what₂.LL) / (g' v.1 : D.what₂.LL))) * f X v := by
      intro v hv
      have hv' : v.1 ∈ Sz := by simpa using hv
      have h2 : v.1 ∈ Bs.P ∧ v.1 ∈ Sz := ⟨v.2, hv'⟩
      simp only [bS₁, g, g', dif_pos hv', dif_pos h2]
      exact heS v hv'
    have hTw : (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), f X v) *
        σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ X.T ∧ v.1 ∉ Sz), bT₁ v) = 1 := by
      rw [map_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun v hv => ?_
      have hv' : v.1 ∈ X.T ∧ v.1 ∉ Sz := by simpa using hv
      simp only [bT₁, dif_pos hv']
      rw [mul_comm]
      exact heT v hv'.1 hv'.2
    rw [hst X₀, hst X, hsplit, hT0, Finset.prod_congr rfl hA, Finset.prod_mul_distrib, ← map_prod,
      Finset.prod_mul_distrib, hmap (fun v => (g v : D.what₂.LL) / (g' v : D.what₂.LL)), e1, e2, mul_zpow, mul_zpow]
    simp only [map_mul, map_zpow₀]
    linear_combination (-((σ b1) ^ (e₁ : ℤ) * (σ b2) ^ (e₂ : ℤ) *
      σ (∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), bS₁ v) *
      σ (∏ v ∈ Sz, (g v : D.what₂.LL) / (g' v : D.what₂.LL)) * ((idealVal X.ν 𝔟 : ℂ)) ^ (e₁ : ℤ) *
      ((idealVal X.ν 𝔠 : ℂ)) ^ (e₂ : ℤ) * ∏ v ∈ Finset.univ.filter (fun v : Bs.P => v.1 ∈ Sz), f X v)) * hTw

end GlobalTheory.SqStepArith

namespace GlobalTheory.SqStepArith

theorem stepFac_ratio : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ hL G => ?_⟩⟩
  intro W S _ hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0
  exact stepFac_ratio_core G hL W S hN i j t Bs e₁ e₂ s 𝔟 𝔠 z hB h0

end GlobalTheory.SqStepArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStepFactorRatioUnitGaussSumQuotientStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient : GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (e₁ e₂ s : ℤˣ)
      (𝔟 𝔠 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (z : ℤ), GlobalTheory.SqStep.BaseFits G W i j t Bs →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z ≠ 0 →
      GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j μ₀) e₁ e₂ s 𝔟 𝔠 z) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (GlobalTheory.SqStep.chs G i j t) e₁ e₂ s 𝔟 𝔠 z) := by
  first | exact @GlobalTheory.SqStepArith.stepFac_ratio | exact GlobalTheory.SqStepArith.stepFac_ratio | (intros; apply GlobalTheory.SqStepArith.stepFac_ratio <;> assumption)
end
