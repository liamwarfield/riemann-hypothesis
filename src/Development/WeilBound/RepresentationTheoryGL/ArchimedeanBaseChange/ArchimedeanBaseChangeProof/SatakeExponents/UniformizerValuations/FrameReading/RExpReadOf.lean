module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriGlCasselmanDatum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlocksExponent
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardResidueEqQV
noncomputable section
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.JacEigAt

theorem qV_pos {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : 0 < qV E w := by
  unfold qV
  exact Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem card_residue_eq_qV {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    Nat.card 𝓀[w.adicCompletion E] = qV E w := by
  have h := GlobalTheory.LocLanglands.resCard_eq_normV (w := w)
  simpa [GlobalTheory.SplitWeil.resCard, Formalism.ConjugateSelfDual.normV, qV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using h

theorem modExp_points (n : ℕ) (a : Fin n) :
    modExp (fun _ : Fin n => Unit) a = (n : ℤ) - 1 - 2 * (a : ℕ) := by
  have h1 : (Finset.univ.filter fun b : Fin n => a < b) = Finset.Ioi a := by ext; simp
  have h2 : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by ext; simp
  have ha := a.2
  simp only [modExp, Fintype.card_unique, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one, h1, h2,
    Fin.card_Ioi, Fin.card_Iio]
  omega

theorem nabs_zpow {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ϖ : kˣ) (h : ord k ϖ = 1) (m : ℤ) :
    GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = (GlobalTheory.SplitWeil.resCard k : ℝ) ^ (-m) := by
  have h1 : GlobalTheory.SplitWeil.nabs k (ϖ ^ m) = GlobalTheory.SplitWeil.nabs k ϖ ^ m := by
    simp [GlobalTheory.SplitWeil.nabs]
  rw [h1, GlobalTheory.LGrp.nabs_eq_zpow, h, _root_.zpow_neg, zpow_one, _root_.inv_zpow, _root_.zpow_neg]

theorem prod_zpow_sum {ι : Type} (s : Finset ι) (r : ℂ) (hr : r ≠ 0) (f : ι → ℤ) :
    ∏ a ∈ s, r ^ f a = r ^ ∑ a ∈ s, f a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hr]

theorem absPow_term {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (e m : ℤ) :
    (absPow (w.adicCompletion E) ((e : ℂ) / 2) (ϖ ^ m) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (-(e * m)) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  set r : ℝ := Real.sqrt (qV E w : ℝ) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hq
  have hrq : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = r ^ (2 : ℤ) := by
    have : (GlobalTheory.SplitWeil.resCard (w.adicCompletion E) : ℝ) = qV E w := by
      simp [GlobalTheory.SplitWeil.resCard, card_residue_eq_qV]
    rw [this, hr, zpow_ofNat, Real.sq_sqrt hq.le]
  have hs : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hs, val_absPow_ofReal, nabs_zpow ϖ h, hrq, ← _root_.zpow_mul, ← Real.rpow_intCast, ← Real.rpow_mul hr0.le]
  have : (((2 * -m : ℤ) : ℝ)) * ((e : ℝ) / 2) = ((-(e * m) : ℤ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_intCast]
  push_cast
  rfl

theorem deltaHalf_inv {E : Type} [Field E] [NumberField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (ϖ : (w.adicCompletion E)ˣ) (h : ord (w.adicCompletion E) ϖ = 1) (x : Fin n → ℤ) :
    (((deltaHalf (w.adicCompletion E) (fun _ : Fin n => Unit)
        (leviTorus (w.adicCompletion E) (Fin n) fun i => ϖ ^ x i))⁻¹ : ℂˣ) : ℂ) =
      (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i) := by
  have hq : (0 : ℝ) < qV E w := by exact_mod_cast qV_pos w
  have hr : (((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hd : ∀ i, GeneralLinearGroup.det
      (leviTorus (w.adicCompletion E) (Fin n) (fun i => ϖ ^ x i) i) = ϖ ^ x i :=
    fun i => congrFun ((leviTorus (w.adicCompletion E) (Fin n)).left_inv fun i => ϖ ^ x i) i
  rw [Units.val_inv_eq_inv_val, deltaHalf_apply, Units.coe_prod]
  simp only [hd, absPow_term w ϖ h, modExp_points]
  rw [prod_zpow_sum _ _ hr, ← _root_.zpow_neg, Finset.sum_neg_distrib, neg_neg]

end GlobalTheory.CompanionTheory.JacEigAt


end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlocksExponent
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.DlBridgeAt

theorem val_eq_uniformizer_of_ord {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ) (h : ord k ϖ = 1) :
    valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨y, hy⟩ := valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact uniformizer_ne_zero hy.symm
  have hu : valuation k ((Units.mk0 y hy0 : kˣ) : k) = uniformizer k := hy
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hu
  have h2 : ord k (ϖ * (Units.mk0 y hy0)⁻¹) = 0 := by
    have h3 := ord_mul k (ϖ * (Units.mk0 y hy0)⁻¹) (Units.mk0 y hy0)
    rw [inv_mul_cancel_right] at h3
    omega
  have h4 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hu] at h4
  have hne : uniformizer k ≠ 0 := uniformizer_ne_zero
  exact (mul_inv_eq_one₀ hne).1 h4

end GlobalTheory.CompanionTheory.DlBridgeAt


open GlobalTheory.CompanionTheory.DlBridgeAt in
theorem GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  intro E _ _ _ w ϖ hϖ
  have hord : ord (w.adicCompletion E) ϖ = 1 := (GlobalTheory.CompanionTheory.CtS.NuVal.ord_eq_ordL_unit w ϖ).trans hϖ
  refine ⟨val_eq_uniformizer_of_ord ϖ hord, fun N x => ?_⟩
  have hinv := GlobalTheory.CompanionTheory.JacEigAt.deltaHalf_inv N w ϖ hord x
  have hv := val_deltaHalf (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  have hm := deltaB_eq_modulus (fun i : Fin N => ϖ ^ x i)
  have hpos := modulus_pos (w.adicCompletion E)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i)
  rw [Units.val_inv_eq_inv_val, hv] at hinv
  rw [hv, hm]
  change _ = GlobalTheory.BCT.qh w ^ _ at hinv
  rw [← hinv]
  set m := modulus (w.adicCompletion E) (fun _ : Fin N => Unit)
    (leviTorus (w.adicCompletion E) (Fin N) fun i => ϖ ^ x i) with hmdef
  have hs : √m * √m = m := Real.mul_self_sqrt hpos.le
  have hs0 : √m ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  have key : ∀ s : ℝ, s ≠ 0 → (s * s)⁻¹ * s = s⁻¹ := fun s h => by field_simp
  have h5 := key _ hs0
  rw [hs] at h5
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, h5]

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeltaBlocksExponentStatement
namespace PositivityTheory.Rg.BcB.F.Tail.PExp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_blocks_exponent : PositivityTheory.Rg.BcB.F.Tail.PExp.DlBridge := by
  first | exact @GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge | exact GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge | (intros; apply GlobalTheory.CompanionTheory.DlBridgeAt.dlBridge <;> assumption)
end PositivityTheory.Rg.BcB.F.Tail.PExp
end
end

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F.Tail

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gap_iff {m : ℕ} (x : Fin m → ℤ) : Gap x ↔ StrictAnti x :=
  ⟨fun h i j hij => by have := h i j hij; omega, fun h i j hij => by have := h hij; omega⟩

theorem gap_neg (m : ℕ) : Gap (fun i : Fin m => -((i : ℕ) : ℤ)) := fun i j hij => by
  have : (i : ℕ) < j := hij
  show -((j : ℕ) : ℤ) + 1 ≤ -((i : ℕ) : ℤ)
  omega

theorem dcos_eq (m : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (x : Fin m → ℤ) :
    dcos m w (tdiag ϖ x) = GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd (fun i => ϖ ^ x i) := by
  funext g
  by_cases h : ∃ a ∈ iwGL m w, ∃ b ∈ iwGL m w, g = a * tdiag ϖ x * b
  · rw [dcos, if_pos h, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd, Set.indicator_of_mem]
    exact h
  · rw [dcos, if_neg h, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd, Set.indicator_of_notMem]
    exact h

theorem dcos_right (m : ℕ) (w : Pl E) (t g : GLw m w) (i : GLw m w) (hi : i ∈ iwGL m w) :
    dcos m w t (g * i) = dcos m w t g := by
  have key : (∃ a ∈ iwGL m w, ∃ b ∈ iwGL m w, g * i = a * t * b) ↔
      (∃ a ∈ iwGL m w, ∃ b ∈ iwGL m w, g = a * t * b) := by
    constructor
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * i⁻¹, mul_mem hb (inv_mem hi), by rw [← mul_assoc, ← e]; group⟩
    · rintro ⟨a, ha, b, hb, e⟩
      exact ⟨a, ha, b * i, mul_mem hb hi, by rw [e]; group⟩
  unfold dcos
  simp only [key]

theorem smul_cancel {M : Type} [AddCommGroup M] [Module ℂ M] {δ dh c p d : ℂ} {J y : M} (hne : δ ≠ 0)
    (hd : d = δ * dh) (h : (c * (d * p)) • y = δ • J) : J = (c * p * dh) • y := by
  have e : (c * (d * p)) • y = δ • ((c * p * dh) • y) := by
    rw [smul_smul, hd]
    congr 1
    ring
  rw [e] at h
  exact (smul_right_injective M hne h).symm


set_option maxHeartbeats 1000000 in
theorem sat_of_eig (hSub : PExp.SubEig) (hCC0 : PExp.CosetCount) (hTE : PExp.TorusExp) (hDl : PExp.DlBridge)
    (hES : PExp.ExpToSat) {m : ℕ} (P : Pre E m) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ)
    (hϖ : ordL (ϖ : w.adicCompletion E) = 1) (ξ : Fin m → ℂˣ) (hm : N3.Mono ξ) (u : _)
    (hu : u ∈ fixed (prodAt P w) (iwGL m w)) (hu0 : u ≠ 0) (c : ℂ)
    (heig : ∀ x, Gap x → hkG (prodAt P w) (iwGL m w) (dcos m w (tdiag ϖ x)) u = (c * (dl w x * pw ξ x)) • u) :
    P.Sat w (Finset.univ.val.map ξ) := by
  have hD := hDl E w ϖ hϖ
  have hcon : ∀ x : Fin m → ℤ, Gap x → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.Contracts (fun i => ϖ ^ x i) := fun x hx =>
    GlobalTheory.IwahoriTraceProof.dominantContracts ϖ hD.1 x ((gap_iff x).1 hx).antitone
  have hCC := fun x hx => hCC0 (w.adicCompletion E) m _ (hcon x hx)
  obtain ⟨P', hsub, u', hu', hu0', heig'⟩ := hSub (GLw m w) _ (prodAt P w) (GlobalTheory.SmGL.isSmooth_parInd _ _)
    (iwGL m w) {x : Fin m → ℤ // Gap x} (fun x => GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd (fun i => ϖ ^ x.1 i))
    (fun x => c * (dl w x.1 * pw ξ x.1)) (fun x => (hCC x.1 x.2).1) u hu hu0
    (fun x => by rw [← dcos_eq]; exact heig x.1 x.2)
  obtain ⟨y, hy⟩ : ∃ y : Jacquet P'.ρ (GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin m)), y = Submodule.Quotient.mk u' :=
    ⟨_, rfl⟩
  have hinj := GlobalTheory.IwahoriInj.iwahoriProj_injective (w.adicCompletion E) (Fin m) P'.V P'.ρ P'.smooth
  have hy0 : y ≠ 0 := by
    intro h0
    rw [hy] at h0
    have : GlobalTheory.SmGL.iwahoriProj P'.ρ ⟨u', hu'⟩ = 0 := Subtype.ext h0
    exact hu0' (congrArg Subtype.val (hinj (this.trans (map_zero _).symm)))
  have hyfix : y ∈ fixed (GlobalTheory.SmGL.jacBU P'.ρ) (GlobalTheory.SmGL.torusO (w.adicCompletion E) (Fin m)) :=
    hy ▸ (GlobalTheory.SmGL.iwahoriProj P'.ρ ⟨u', hu'⟩).2
  have hstep : ∀ x : Fin m → ℤ, StrictAnti x → GlobalTheory.SmGL.jacBU P'.ρ (fun i => ϖ ^ x i) y =
      (c * (∏ i, ((ξ i ^ x i : ℂˣ) : ℂ)) * (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (fun _ : Fin m => Unit)
        (GlobalTheory.SmGL.leviTorus (w.adicCompletion E) (Fin m) fun i => ϖ ^ x i) : ℂ)) • y := by
    intro x hx
    have hg : Gap x := (gap_iff x).2 hx
    have h1 := (hCC x hg).2 P'.V P'.ρ u' hu'
    have h1' : PExp.hkS P'.ρ (GlobalTheory.SmGL.iwahori (w.adicCompletion E) (Fin m))
        (GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.cosetInd fun i => ϖ ^ x i) u' = (c * (dl w x * pw ξ x)) • u' := heig' ⟨x, hg⟩
    rw [h1', Submodule.Quotient.mk_smul, ← hy] at h1
    have hne : ((((GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.deltaB (fun i => ϖ ^ x i))⁻¹ : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (inv_pos.2 (GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.deltaB_pos (fun i => ϖ ^ x i))).ne'
    exact smul_cancel hne (hD.2 m x).symm h1
  have hall := hTE (w.adicCompletion E) m P'.V P'.ρ ϖ hD.1 ξ c y hy0 hyfix hstep
  obtain ⟨hsph, b, hb, hsum⟩ := hES E w P.c m P.N P.h (fun i => P.σ i w) P' ξ hsub hm ⟨y, hy0, hall⟩
  exact ⟨b, fun i => ⟨hsph i, hb i⟩, hsum⟩

set_option maxHeartbeats 1000000 in
theorem rExpRead_of (h0 : PExp.HkEFin) (h1 : PExp.TensHk) (h2 : PExp.TensEig) (h3 : PExp.TensEigR)
    (h4 : PExp.ContrFix) (hSub : PExp.SubEig) (hCC0 : PExp.CosetCount) (hTE : PExp.TorusExp) (hDl : PExp.DlBridge)
    (hES : PExp.ExpToSat) : RExpRead := by
  intro _ E _ _ _ a b Pa Pb w ϖ ξa ξb hϖ hma hmb hJ
  obtain ⟨v, hv, hv0, heig⟩ := hJ
  have hD := hDl E w ϖ hϖ
  have hcon : ∀ {m : ℕ} (x : Fin m → ℤ), Gap x → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.Contracts (fun i => ϖ ^ x i) := fun x hx =>
    GlobalTheory.IwahoriTraceProof.dominantContracts ϖ hD.1 x ((gap_iff x).1 hx).antitone
  have hfin : ∀ {m : ℕ} (x : Fin m → ℤ), Gap x → {q : GLw m w ⧸ iwGL m w | dcos m w (tdiag ϖ x) q.out ≠ 0}.Finite :=
    fun x hx => by
      rw [dcos_eq]
      exact (hCC0 (w.adicCompletion E) _ _ (hcon x hx)).1
  have hdl : ∀ {m : ℕ} (x : Fin m → ℤ) (ξ : Fin m → ℂˣ), dl w x * pw ξ x ≠ 0 := fun {m} x ξ => by
    refine mul_ne_zero ?_ ?_
    · rw [show dl w x = _ from (hD.2 m x).symm]
      refine mul_ne_zero ?_ (Units.ne_zero _)
      exact_mod_cast (inv_pos.2 (GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.deltaB_pos _)).ne'
    · exact Finset.prod_ne_zero_iff.2 fun i _ => Units.ne_zero _
  let A : {x : Fin a → ℤ // Gap x} → Module.End ℂ _ := fun x =>
    PExp.hkE (prodAt Pa w) (iwGL a w) (dcos a w (tdiag ϖ x.1))
  let B : {y : Fin b → ℤ // Gap y} → Module.End ℂ _ := fun y =>
    PExp.hkE (prodAt Pb w) (iwGL b w) (dcos b w (tdiag ϖ y.1))
  have hT : ∀ x y, TensorProduct.map (A x) (B y) v =
      ((dl w x.1 * pw ξa x.1) * (dl w y.1 * pw ξb y.1)) • v := by
    intro x y
    exact (h1 _ _ _ _ (prodAt Pa w) (prodAt Pb w) (iwGL a w) (iwGL b w) _ _
      (fun g i hi => dcos_right a w _ g i hi) (fun g i hi => dcos_right b w _ g i hi) (hfin x.1 x.2) (hfin y.1 y.2)
      v hv).symm.trans (heig x.1 y.1 x.2 y.2)
  have hA : ∀ {m : ℕ} (P : Pre E m) (x : Fin m → ℤ), Gap x → ∀ z,
      PExp.hkE (prodAt P w) (iwGL m w) (dcos m w (tdiag ϖ x)) z = hkG (prodAt P w) (iwGL m w) (dcos m w (tdiag ϖ x)) z :=
    fun P x hx z => h0 _ _ (prodAt P w) _ _ (hfin x hx) z
  constructor
  · obtain ⟨l, c, hc, hu0, hAu⟩ := h2 _ _ _ _ A B (fun x => dl w x.1 * pw ξa x.1)
      (fun y => dl w y.1 * pw ξb y.1) v hv0 ⟨⟨_, gap_neg b⟩⟩ (fun x => hdl x.1 ξa) (fun y => hdl y.1 ξb) hT
    refine sat_of_eig hSub hCC0 hTE hDl hES Pa w ϖ hϖ ξa hma _ ((h4 _ _ _ _ (prodAt Pa w) (prodAt Pb w) (iwGL a w) (iwGL b w) v hv).1 l)
      hu0 c fun x hx => ?_
    exact (hA Pa x hx _).symm.trans (hAu ⟨x, hx⟩)
  · obtain ⟨l, c, hc, hu0, hBu⟩ := h3 _ _ _ _ A B (fun x => dl w x.1 * pw ξa x.1)
      (fun y => dl w y.1 * pw ξb y.1) v hv0 ⟨⟨_, gap_neg a⟩⟩ (fun x => hdl x.1 ξa) (fun y => hdl y.1 ξb) hT
    refine sat_of_eig hSub hCC0 hTE hDl hES Pb w ϖ hϖ ξb hmb _ ((h4 _ _ _ _ (prodAt Pa w) (prodAt Pb w) (iwGL a w) (iwGL b w) v hv).2 l)
      hu0 c fun y hy => ?_
    exact (hA Pb y hy _).symm.trans (hBu ⟨y, hy⟩)

theorem rExpRead : RExpRead :=
  rExpRead_of GlobalTheory.T.hecke_eigen_finite GlobalTheory.T.tensor_hecke GlobalTheory.T.tensor_eigen GlobalTheory.T.tensor_eigen_real GlobalTheory.T.contraction_fixed GlobalTheory.T.sub_eigen_tail_hecke GlobalTheory.T.coset_count_tail
    GlobalTheory.T.torus_exponent_tail GlobalTheory.T.delta_blocks_exponent GlobalTheory.T.exponent_to_saturation

end PositivityTheory.Rg.BcB.F.Tail

end
