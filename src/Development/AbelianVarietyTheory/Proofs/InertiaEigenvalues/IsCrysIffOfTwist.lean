module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysIffOfTwist
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.TwistCrys

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W] [FiniteDimensional LL W]

theorem isCrys_twist (ht : TensorCrys PD LL) (hq : QuotCrys PD LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G W) (χ : G → LL)
    (lam : W →ₗ[LL] LL) (w : W) (hw : lam w = 1)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (cν : IsCrys PD ν) (cρ : IsCrys PD ρ) : IsCrys PD ρ' := by
  let f : V ⊗[LL] W →ₗ[LL] V := (TensorProduct.rid LL V).toLinearMap ∘ₗ lam.lTensor V
  have hf : ∀ v x, f (v ⊗ₜ x) = lam x • v := fun v x => by simp [f]
  refine hq (V ⊗[LL] W) (ρ.tprod ν) V ρ' f ?_ ?_ (ht V ρ W ν cρ cν)
  · intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul v y =>
      rw [Representation.tprod_apply, TensorProduct.map_tmul, hf, hf, hν, hρ, map_smul, map_smul,
        smul_eq_mul, mul_smul]
  · intro v
    exact ⟨v ⊗ₜ w, by rw [hf, hw, one_smul]⟩

theorem isCrys_twist_iff (ht : TensorCrys PD LL) (hq : QuotCrys PD LL) (hd : DualCrys PD LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G W) (χ : G → LL)
    (lam : W →ₗ[LL] LL) (w : W) (hw : lam w = 1)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (cν : IsCrys PD ν) : IsCrys PD ρ ↔ IsCrys PD ρ' := by
  refine ⟨isCrys_twist PD ht hq ρ ρ' ν χ lam w hw hν hρ cν, ?_⟩
  have hinv : ∀ g, χ g⁻¹ * χ g = 1 := fun g => by
    have h1 : ν g⁻¹ (ν g w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have h2 := congrArg lam h1
    rwa [hν, hν, map_smul, map_smul, hw, smul_eq_mul, smul_eq_mul, mul_one] at h2
  refine isCrys_twist PD ht hq ρ' ρ ν.dual (fun g => χ g⁻¹) (Module.Dual.eval LL W w) lam hw
    (fun g f => ?_) (fun g x => ?_) (hd W ν cν)
  · ext x
    simp [Representation.dual_apply, Module.Dual.transpose_apply, hν]
  · rw [hρ, smul_smul, hinv, one_smul]

end Generic

theorem isCrys_iff_of_twist : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsCrys (P.PD K) ν → (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ') := by
  intro hF l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ cν
  have h := (fontaineFormalism_iff l P).1 (GlobalTheory.RegularRing.fontaineFormalism hF l P AI ⟨T⟩) K LL
  exact isCrys_twist_iff (P.PD K) h.2.2.2.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.2.1 ρ ρ' ν χ
    (LinearMap.proj 0) (fun _ => 1) rfl hν hρ cν

end GlobalTheory.TwistCrys
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReduction
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.RedAct

theorem ringHom_padicInt_eq {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (f : ℤ_[l] →+* k)
    (z : ℤ_[l]) : f z = ((ZMod.castHom (dvd_refl l) k).comp PadicInt.toZMod) z := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  have hz : z = (z.zmodRepr : ℤ_[l]) + l * c := by rw [← hc]; ring
  rw [hz]
  simp only [map_add (f := _), map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem map_act {l : ℕ} [Fact l.Prime] {O k : Type} [CommRing O] [Algebra ℤ_[l] O] [Field k] [CharP k l]
    (f : O →+* k) (c : ℤ_[l]) (a : O⟦X⟧) :
    PowerSeries.map f (GlobalTheory.CycFr.act O c a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l c (PowerSeries.map f a) := by
  have hb : PowerSeries.map f (GlobalTheory.CycFr.bin O c) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l c := by
    ext n
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, PowerSeries.coeff_map, PowerSeries.coeff_map,
      PowerSeries.binomialSeries_coeff, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
      ← Algebra.algebraMap_eq_smul_one]
    exact ringHom_padicInt_eq (f.comp (algebraMap ℤ_[l] O)) _
  rw [GlobalTheory.CycFr.act_apply, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, ← hb]
  have h := PowerSeries.map_subst (GlobalTheory.CycFr.hasSubst_bin O c) (h := f) a
  have h2 : PowerSeries.map f (GlobalTheory.CycFr.bin O c - 1) = PowerSeries.map f (GlobalTheory.CycFr.bin O c) - 1 := by
    rw [map_sub, map_one]
  rw [← h2]
  exact h

theorem deltaPi_one_add {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (b : k⟦X⟧) :
    GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (1 + l) b = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l b := by
  have h := PowerSeries.binomialSeries_nat (R := ℤ_[l]) (A := ℤ_[l]) (1 + l)
  rw [Nat.cast_add, Nat.cast_one] at h
  rw [GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi, GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow, h]
  simp

theorem chi_surjective {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) :
    Function.Surjective χ := by
  intro u
  obtain ⟨χ', h1, -, h3⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  obtain ⟨g, hg, hgu⟩ := h3 K 0 (le_trans (le_inf le_rfl hK) le_sup_left) u (by simp)
  refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (GlobalTheory.algebraMap_padicInt_OL_injective LL ?_)⟩
  rw [hχ]
  apply Subtype.ext
  have h := W.χΓ_res ⟨g, hg⟩
  rw [P.PD_χ, ← h1] at h
  refine h.trans ?_
  change algebraMap ℚ_[l] ↥LL.1 ((χ' g : ℤ_[l]) : ℚ_[l]) = _
  rw [hgu]
  rfl

theorem card_torsion {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) (h : K.1 ≤ Ks K 1) :
    W.DelF.card = l - 1 := by
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h
  rw [p1, mul_one] at hc
  exact hc

theorem gamma_eq_act {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) (g : W.Gam) :
    W.γ₀ g = GlobalTheory.CycFr.act ↥(OL LL) (χ g : ℤ_[l]) :=
  GlobalTheory.WachTie.γ₀_eq W (P.PD_p K) χ hχ g

theorem action_of_surjective {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (χ : W.Gam →* ℤ_[l]ˣ)
    (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O)) (hs : Function.Surjective χ)
    (hγ : ∀ g, W.γ₀ g = GlobalTheory.CycFr.act O (χ g : ℤ_[l])) (hc : W.DelF.card = l - 1)
    {k : Type} [Field k] [CharP k l] (r : O →+* k) :
    (∃ γ : W.Gam, (W.χΓ γ : O) = 1 + (l : O) ∧
      ∀ a, PowerSeries.map r (W.γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map r a)) ∧
    ∃ e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a,
      PowerSeries.map r (W.γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map r a) := by
  have h2l := (Fact.out : l.Prime).two_le
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  have hcard : Nat.card (CommGroup.torsion W.Gam) = l - 1 := by
    rw [← hc, ← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [CommGroup.mem_torsion, Finset.mem_coe, GlobalTheory.WachTie.mem_DelF_iff]
  have hpow : ∀ δ ∈ W.DelF, δ ^ (l - 1) = 1 := fun δ hδ => by
    have h1 : (⟨δ, (GlobalTheory.WachTie.mem_DelF_iff W δ).1 hδ⟩ : CommGroup.torsion W.Gam) ^ (l - 1) = 1 := by
      rw [← hcard]; exact pow_card_eq_one'
    exact congrArg Subtype.val h1
  constructor
  · have hu : IsUnit (1 + (l : ℤ_[l])) := by
      have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (-(l : ℤ_[l]))
      rw [sub_neg_eq_add, IsUnit.neg_iff] at h1
      exact h1.resolve_left PadicInt.p_nonunit
    obtain ⟨g, hg⟩ := hs hu.unit
    have hg' : (χ g : ℤ_[l]) = 1 + l := by rw [hg, hu.unit_spec]
    refine ⟨g, by rw [← hχ, hg', map_add (f := _), map_one, map_natCast], fun a => ?_⟩
    rw [hγ, map_act, hg', deltaPi_one_add]
  · let f : {δ // δ ∈ W.DelF} → {z : ℤ_[l] // z ^ (l - 1) = 1} := fun δ =>
      ⟨χ δ.1, by rw [← Units.val_pow_eq_pow_val, ← map_pow, hpow δ.1 δ.2, map_one, Units.val_one]⟩
    have hf : Function.Bijective f := by
      refine ⟨fun a b hab => Subtype.ext (hχi (Units.ext (congrArg Subtype.val hab))), fun z => ?_⟩
      have hu : IsUnit z.1 := IsUnit.of_pow_eq_one z.2 (by omega)
      obtain ⟨g, hg⟩ := hs hu.unit
      have hg' : (χ g : ℤ_[l]) = z.1 := by rw [hg, hu.unit_spec]
      refine ⟨⟨g, (W.DelF_def g).2 ⟨l - 1, by omega, hχi (Units.ext ?_)⟩⟩, Subtype.ext hg'⟩
      rw [map_pow, Units.val_pow_eq_pow_val, hg', z.2, map_one, Units.val_one]
    refine ⟨Equiv.ofBijective f hf, fun δ a => ?_⟩
    rw [hγ, map_act]
    rfl

theorem gamma_action_reduction : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  intro l _ P H S k _ _ _
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P S.K S.LL (S.W H)
  exact action_of_surjective (S.W H) χ hχ (chi_surjective P S.K S.LL _ S.hyp.1.2.1.1 χ hχ)
    (gamma_eq_act P S.K S.LL _ χ hχ)
    (card_torsion P S.K S.LL _ S.hyp.1.2.1.1 S.hyp.1.2.1.2.1 S.hyp.1.2.1.2.2.2.2.1) (algebraMap S.O k)

end GlobalTheory.RedAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReductionStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_gamma_eq_deltaPi_teichmuller : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], (∃ γ : (S.W H).Gam, ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) ∧ ∀ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ γ a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap S.O k) a)) ∧ ∃ e : {δ // δ ∈ (S.W H).DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1}, ∀ δ a, PowerSeries.map (algebraMap S.O k) ((S.W H).γ₀ δ.1 a) = GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap S.O k) a) := by
  first | exact @GlobalTheory.RedAct.gamma_action_reduction | exact GlobalTheory.RedAct.gamma_action_reduction | (intros; apply GlobalTheory.RedAct.gamma_action_reduction <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDeRhamFiltrationQuotientInvariants
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.TateFilQuot

open GlobalTheory.DRFil

section Abstract

variable {G B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
  (σ : G → B →+* B) (ρ : G → M →+ M) (F : ℤ → AddSubgroup B) (FM : ℤ → AddSubgroup M)

theorem step_invariant
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    {ι : Type} [DecidableEq ι] (k : ι → ℤ) (d : ι → M) (hd : ∀ i g, ρ g (d i) = d i)
    (hdk : ∀ i, d i ∈ FM (k i)) (c : ℤ) (n : ℕ) :
    ∀ (s : Finset ι), s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (c - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • d i) - ∑ i ∈ s, b i • d i ∈ FM (c + 1)) →
      ∃ w ∈ FM c, (∀ g, ρ g w = w) ∧ ∑ i ∈ s, b i • d i - w ∈ FM (c + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hsum
  by_cases hs : ∃ i ∈ s, ∃ κ : ι → B, (∀ j, κ j ∈ F 0 ∧ (∀ g, σ g (κ j) = κ j) ∧ (k i ≠ k j → κ j = 0)) ∧
      d i + ∑ j ∈ s.erase i, κ j • d j ∈ FM (k i + 1)
  · obtain ⟨i, hi, κ, hκ, hmem⟩ := hs
    have heq : ∑ j ∈ s, b j • d j = b i • (d i + ∑ j ∈ s.erase i, κ j • d j) +
        ∑ j ∈ s.erase i, (b j - b i * κ j) • d j := by
      rw [← Finset.add_sum_erase s _ hi]
      simp only [smul_add, Finset.smul_sum, mul_smul, sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 := hsmul _ _ _ _ (hb i hi) hmem
    rw [show c - k i + (k i + 1) = c + 1 by ring] at h1
    rw [heq] at hsum ⊢
    obtain ⟨w, hw, hwg, hw'⟩ := ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) (s.erase i) rfl
      (fun j => b j - b i * κ j) (fun j hj => by
        refine (F _).sub_mem (hb j (Finset.mem_of_mem_erase hj)) ?_
        by_cases hk : k i = k j
        · have := hmul _ _ _ _ (hb i hi) (hκ j).1
          rwa [add_zero, hk] at this
        · rw [(hκ j).2.2 hk, mul_zero]
          exact (F _).zero_mem) (fun g => by
        have h2 := (FM _).sub_mem (hsum g) ((FM _).sub_mem (hMG g _ _ h1) h1)
        convert h2 using 1
        rw [map_add (ρ g) (b i • _)]
        abel)
    refine ⟨w, hw, hwg, ?_⟩
    rw [add_sub_assoc]
    exact (FM _).add_mem h1 hw'
  · have hg : ∀ g, ∀ i ∈ s, σ g (b i) - b i ∈ F (c - k i + 1) := fun g =>
      graded_indep σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k d hd hdk s hs c
        (fun i => σ g (b i) - b i) (fun i hi => (F _).sub_mem (hFG _ _ _ (hb i hi)) (hb i hi)) (by
          convert hsum g using 1
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, hρ, hd, sub_smul, Finset.sum_sub_distrib])
    have hκ : ∀ i, ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (c - k i ≠ 0 → κ = 0) ∧
        (i ∈ s → b i - κ ∈ F (c - k i + 1)) := fun i => by
      by_cases hi : i ∈ s
      · obtain ⟨κ, h1, h2, h3, h4⟩ := hT _ _ (hb i hi) (fun g => hg g i hi)
        exact ⟨κ, h1, h2, h3, fun _ => h4⟩
      · exact ⟨0, (F 0).zero_mem, fun g => map_zero _, fun _ => rfl, fun h => (hi h).elim⟩
    choose κ h1 h2 h3 h4 using hκ
    refine ⟨∑ i ∈ s, κ i • d i, (FM _).sum_mem fun i _ => ?_, fun g => ?_, ?_⟩
    · by_cases hk : c - k i = 0
      · have := hsmul _ _ _ _ (h1 i) (hdk i)
        rwa [show 0 + k i = c by omega] at this
      · rw [h3 i hk, zero_smul]
        exact (FM _).zero_mem
    set_option synthInstance.maxHeartbeats 100000 in
      · simp only [map_sum, hρ, hd, h2]
    · rw [← Finset.sum_sub_distrib]
      refine (FM _).sum_mem fun i hi => ?_
      have := hsmul _ _ _ _ (h4 i hi) (hdk i)
      rwa [show c - k i + 1 + k i = c + 1 by ring, sub_smul] at this

theorem invariant_mod
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    (hFa : Antitone F) (hMa : Antitone FM) (hFe : ∀ x, ∃ a, x ∈ F a) (hMe : ∀ x, ∃ a, x ∈ FM a)
    (hspan : ∀ y : M, ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → M),
      (∀ i g, ρ g (d i) = d i) ∧ y = ∑ i, b i • d i)
    (a b : ℤ) (z : M) (hz : z ∈ FM a) (hg : ∀ g, ρ g z - z ∈ FM b) :
    ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM b := by
  have key : ∀ c, a ≤ c → c ≤ max a b → ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM c := by
    intro c hc
    induction c, hc using Int.leInduction with
    | base => exact fun _ => ⟨0, (FM _).zero_mem, fun g => map_zero _, by rwa [sub_zero]⟩
    | succ c hc ih =>
      intro hcb
      have hcb' : c + 1 ≤ b := by omega
      obtain ⟨w, hw, hwg, hzw⟩ := ih (by omega)
      obtain ⟨m, b₀, d₀, hd₀, e₀⟩ := hspan (z - w)
      obtain ⟨m', k', b', d', h, e⟩ := filtered σ ρ F FM hρ hmul hsmul hFG hMG hinv hT hFa hMa hFe hMe
        c (z - w) hzw m b₀ d₀ hd₀ e₀
      obtain ⟨w', hw', hwg', hzw'⟩ := step_invariant σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k' d'
        (fun i => (h i).1) (fun i => (h i).2.1) c _ Finset.univ rfl b' (fun i _ => (h i).2.2)
        (fun g => by
          rw [← e, map_sub, hwg, sub_sub_sub_cancel_right]
          exact hMa hcb' (hg g))
      refine ⟨w + w', (FM _).add_mem hw (hMa hc hw'), fun g => by rw [map_add (f := _), hwg, hwg'], ?_⟩
      rwa [← e, sub_sub] at hzw'
  obtain ⟨w, hw, hwg, hzw⟩ := key (max a b) (le_max_left _ _) le_rfl
  exact ⟨w, hw, hwg, hMa (le_max_right _ _) hzw⟩

end Abstract

theorem tied_invariant_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (TT : LocTied l P AI) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    (hdR : IsDR (P.PD K) ρ) (a b : ℤ) (z : V ⊗[ℚ_[l]] P.R.BdR)
    (hz : z ∈ FilV (P.PD K) (LL := LL) (V := V) a)
    (hg : ∀ g, actVdR (P.PD K) ρ g z - z ∈ FilV (P.PD K) (LL := LL) (V := V) b) :
    ∃ w ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) a,
      z - w ∈ FilV (P.PD K) (LL := LL) (V := V) b := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  have hspan := GlobalTheory.Per.DeRhamSpan.span_of_isField (P.PD K) ρ
    (GlobalTheory.Per.TiedField.tied_field l P AI TT).1 hdR
  let φ : P.R.BdR →+* Module.End LL (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun b => AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module P.R.BdR (V ⊗[ℚ_[l]] P.R.BdR) := Module.compHom _ φ
  have hsm : ∀ (b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR), b • x =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b) x := fun _ _ => rfl
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x := fun x => by
    simp [DdR, Submodule.mem_iInf, sub_eq_zero]
  have htm : ∀ (a : ℤ) (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a →
      v ⊗ₜ[ℚ_[l]] x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a v x hx =>
    ⟨v ⊗ₜ ⟨x, hx⟩, rfl⟩
  have hind : ∀ (a : ℤ) (S : AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR)),
      (∀ (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a → v ⊗ₜ[ℚ_[l]] x ∈ S) →
      ∀ z ∈ FilV (P.PD K) (LL := LL) (V := V) a, z ∈ S := by
    rintro a S hS _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | tmul v x => exact hS v x x.2
    | add x y hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
  have hFa : Antitone fun a => ((P.PD K).Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have hMa : Antitone fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup :=
    fun a a' h z hz => hind a' _ (fun v x hx => htm a v x (hFa h hx)) z hz
  obtain ⟨w, hw, hwg, hzw⟩ := invariant_mod (G := ↥(GK K))
    (fun g => ((P.PD K).actdR g : P.R.BdR →+* P.R.BdR))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom)
    (fun a => ((P.PD K).Fil a).toAddSubgroup)
    (fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup)
    (fun g b x => by
      rw [hsm, hsm]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v x => simp [actVdR]
      | add x y hx hy => simp only [map_add (f := _), hx, hy])
    (P.PD K).Fil_mul
    (fun a c x z hx hz => hind c
      ((FilV (P.PD K) (LL := LL) (V := V) (a + c)).toAddSubgroup.comap (φ x).toAddMonoidHom)
      (fun v w hw => htm _ v (x * w) ((P.PD K).Fil_mul _ _ _ _ hx hw)) z hz)
    (P.PD K).Fil_G
    (fun g a z hz => hind a
      ((FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup.comap (actVdR (P.PD K) ρ g).toAddMonoidHom)
      (fun v w hw => htm _ (ρ g v) ((P.PD K).actdR g w) ((P.PD K).Fil_G _ _ _ hw)) z hz)
    (graded_inv Θ K) (graded_invariants TT Θ K) hFa hMa (P.PD K).Fil_exh
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, AddSubgroup.zero_mem _⟩
      | tmul v x =>
        obtain ⟨c, hc⟩ := (P.PD K).Fil_exh x
        exact ⟨c, htm c v x hc⟩
      | add x y hx hy =>
        obtain ⟨c, hc⟩ := hx
        obtain ⟨c', hc'⟩ := hy
        exact ⟨min c c', AddSubgroup.add_mem _ (hMa (min_le_left _ _) hc) (hMa (min_le_right _ _) hc')⟩)
    (fun y => by
      obtain ⟨m, b, d, hd, e⟩ := hspan y
      exact ⟨m, b, d, fun i g => (hD _).1 (hd i) g, e⟩)
    a b z hz hg
  exact ⟨w, ⟨(hD _).2 hwg, hw⟩, hzw⟩

theorem tate_fil_quot : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm5 D := by
  intro D l _ K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact tied_invariant_mod l (D.loc l) (D.locA l) (D.locT l) K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.DirectSumHT

theorem finrank_split {L A A₁ A₂ : Type} [Field L] [AddCommGroup A] [Module L A] [AddCommGroup A₁] [Module L A₁]
    [AddCommGroup A₂] [Module L A₂] (i₁ : A₁ →ₗ[L] A) (i₂ : A₂ →ₗ[L] A) (p₁ : A →ₗ[L] A₁) (p₂ : A →ₗ[L] A₂)
    (h11 : ∀ x, p₁ (i₁ x) = x) (h22 : ∀ x, p₂ (i₂ x) = x) (h12 : ∀ x, p₁ (i₂ x) = 0) (h21 : ∀ x, p₂ (i₁ x) = 0)
    (hs : ∀ x, i₁ (p₁ x) + i₂ (p₂ x) = x)
    (S : Submodule L A) (S₁ : Submodule L A₁) (S₂ : Submodule L A₂)
    [FiniteDimensional L S₁] [FiniteDimensional L S₂]
    (a₁ : ∀ x ∈ S₁, i₁ x ∈ S) (a₂ : ∀ x ∈ S₂, i₂ x ∈ S) (b₁ : ∀ x ∈ S, p₁ x ∈ S₁) (b₂ : ∀ x ∈ S, p₂ x ∈ S₂) :
    finrank L S = finrank L S₁ + finrank L S₂ := by
  let f : S →ₗ[L] S₁ × S₂ := (p₁.restrict b₁).prod (p₂.restrict b₂)
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      have e1 : p₁ x = 0 := congrArg (fun y : S₁ × S₂ => (y.1 : A₁)) hx
      have e2 : p₂ x = 0 := congrArg (fun y : S₁ × S₂ => (y.2 : A₂)) hx
      apply Subtype.ext
      have := hs x
      rw [e1, e2, map_zero, map_zero, add_zero] at this
      exact this.symm
    · rintro ⟨y₁, y₂⟩
      refine ⟨⟨i₁ y₁ + i₂ y₂, S.add_mem (a₁ _ y₁.2) (a₂ _ y₂.2)⟩, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change p₁ (i₁ y₁ + i₂ y₂) = y₁
        rw [map_add (f := _), h11, h12, add_zero]
      · apply Subtype.ext
        change p₂ (i₁ y₁ + i₂ y₂) = y₂
        rw [map_add (f := _), h21, h22, zero_add]
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, Module.finrank_prod]

section Funct

variable {Qp : Type} [Field Qp] {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

noncomputable def ext (R : Type) [AddCommGroup R] [Module Qp R] (f : V →ₗ[LL] V') :
    V ⊗[Qp] R →ₗ[LL] V' ⊗[Qp] R :=
  AlgebraTensorModule.map f (LinearMap.id : R →ₗ[Qp] R)

theorem ext_comm {R R' : Type} [AddCommGroup R] [Module Qp R] [AddCommGroup R'] [Module Qp R']
    (f : V →ₗ[LL] V') (u : V →ₗ[LL] V) (u' : V' →ₗ[LL] V') (h : ∀ v, f (u v) = u' (f v))
    (k : R →ₗ[Qp] R') (x : V ⊗[Qp] R) :
    ext R' f (AlgebraTensorModule.map u k x) = AlgebraTensorModule.map u' k (ext R f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [ext, h]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]

theorem finrank_split_tensor (R : Type) [AddCommGroup R] [Module Qp R] (e : V ≃ₗ[LL] V₁ × V₂)
    (S : Submodule LL (V ⊗[Qp] R)) (S₁ : Submodule LL (V₁ ⊗[Qp] R)) (S₂ : Submodule LL (V₂ ⊗[Qp] R))
    [FiniteDimensional LL S₁] [FiniteDimensional LL S₂]
    (a₁ : ∀ x ∈ S₁, ext R (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) x ∈ S)
    (a₂ : ∀ x ∈ S₂, ext R (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) x ∈ S)
    (b₁ : ∀ x ∈ S, ext R (LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) x ∈ S₁)
    (b₂ : ∀ x ∈ S, ext R (LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) x ∈ S₂) :
    finrank LL S = finrank LL S₁ + finrank LL S₂ := by
  refine finrank_split _ _ _ _ ?_ ?_ ?_ ?_ ?_ S S₁ S₂ a₁ a₂ b₁ b₂
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [ext]
    | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [ext, AlgebraTensorModule.map_tmul, LinearMap.id_apply, ← TensorProduct.add_tmul]
      congr 1
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.inl_apply, LinearMap.inr_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add,
        Prod.mk.eta, LinearEquiv.symm_apply_apply]
    | add a b ha hb =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ha, hb]

end Funct

section Per

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem ext_Dcris (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ Dcris PD ρ, ext B f x ∈ Dcris PD ρ' := by
  intro x hx
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := ext_comm f (ρ g) (ρ' g) (h g) (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp) x
  rw [actVB, ← this]
  exact congrArg _ (hx g)

theorem ext_DdR (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    ∀ x ∈ DdR PD ρ, ext BdR f x ∈ DdR PD ρ' := by
  intro x hx
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  have := ext_comm f (ρ g) (ρ' g) (h g) (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) x
  rw [actVdR, ← this]
  exact congrArg _ (hx g)

theorem ext_FildR (f : V →ₗ[LL] V') (h : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    ∀ x ∈ FildR PD ρ τ a, ext BdR f x ∈ FildR PD ρ' τ a := by
  rintro x ⟨⟨h1, h2⟩, y, hy⟩
  refine ⟨⟨ext_DdR PD f h x h1, ?_⟩, ext _ f y, ?_⟩
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero] at h2 ⊢
    intro c
    have := ext_comm f LinearMap.id LinearMap.id (fun _ => rfl)
      (LinearMap.mulLeft Qp (algebraMap K BdR c)) x
    rw [mulVdR, ← this, ← map_smul]
    exact congrArg _ (h2 c)
  · rw [← hy]
    exact (ext_comm f LinearMap.id LinearMap.id (fun _ => rfl) _ y).symm

variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    {ρ₁ : Representation LL G V₁} {ρ₂ : Representation LL G V₂}

omit [Module Qp V] [IsScalarTower Qp LL V] [Module Qp V₁] [IsScalarTower Qp LL V₁]
  [Module Qp V₂] [IsScalarTower Qp LL V₂] in
theorem equivariant (e : V ≃ₗ[LL] V₁ × V₂) (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) :
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) (ρ₁ g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inl LL V₁ V₂) v)) ∧
    (∀ g v, (e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) (ρ₂ g v) =
      ρ g ((e.symm.toLinearMap ∘ₗ LinearMap.inr LL V₁ V₂) v)) ∧
    (∀ g v, (LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) (ρ g v) =
      ρ₁ g ((LinearMap.fst LL V₁ V₂ ∘ₗ e.toLinearMap) v)) ∧
    (∀ g v, (LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) (ρ g v) =
      ρ₂ g ((LinearMap.snd LL V₁ V₂ ∘ₗ e.toLinearMap) v)) := by
  refine ⟨fun g v => ?_, fun g v => ?_, fun g v => ?_, fun g v => ?_⟩
  · apply e.injective
    simp [he]
  · apply e.injective
    simp [he]
  · simp [he]
  · simp [he]

theorem finrank_Dcris_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (Dcris PD ρ₁)] [FiniteDimensional LL (Dcris PD ρ₂)] :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ₁) + finrank LL (Dcris PD ρ₂) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  exact finrank_split_tensor B e _ _ _ (ext_Dcris PD _ h1) (ext_Dcris PD _ h2) (ext_Dcris PD _ h3)
    (ext_Dcris PD _ h4)

theorem finrank_DdR_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (DdR PD ρ₁)] [FiniteDimensional LL (DdR PD ρ₂)] :
    finrank LL (DdR PD ρ) = finrank LL (DdR PD ρ₁) + finrank LL (DdR PD ρ₂) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  exact finrank_split_tensor BdR e _ _ _ (ext_DdR PD _ h1) (ext_DdR PD _ h2) (ext_DdR PD _ h3)
    (ext_DdR PD _ h4)

theorem finrank_FildR_add (e : V ≃ₗ[LL] V₁ × V₂)
    (he : ∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2))
    [FiniteDimensional LL (DdR PD ρ₁)] [FiniteDimensional LL (DdR PD ρ₂)] (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ₁ τ a) + finrank LL (FildR PD ρ₂ τ a) := by
  obtain ⟨h1, h2, h3, h4⟩ := equivariant e he
  haveI : FiniteDimensional LL (FildR PD ρ₁ τ a) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ₁) (fun x hx => hx.1.1)
  haveI : FiniteDimensional LL (FildR PD ρ₂ τ a) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ₂) (fun x hx => hx.1.1)
  exact finrank_split_tensor BdR e _ _ _ (ext_FildR PD _ h1 τ a) (ext_FildR PD _ h2 τ a)
    (ext_FildR PD _ h3 τ a) (ext_FildR PD _ h4 τ a)

end Per


open GlobalTheory.Per.FontaineBound in
private theorem dcris_finite_le {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) :
    Module.Finite ↥LL.1 (Dcris (P.PD K) ρ) ∧
      finrank ↥LL.1 (Dcris (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 V := by
  have := isDomain_cris (PD := P.PD K) (isField_of_tied T)
  have := (P.PD K).finK₀
  have := LL.2
  refine finite_finrank_le (P.PD K).actB
    (fun b b' hb h => GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K b' b hb fun g hg => ?_) ρ
  have h1 := h ⟨g, hg⟩
  rw [P.PD_actB, P.PD_actB] at h1
  rw [mul_comm, h1, mul_comm]

theorem directSum_hodgeTate : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (e : V ≃ₗ[↥LL.1] (V₁ × V₂)), (∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ₁ ∧ IsDR (P.PD K) ρ₂) ∧ (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ₁ ∧ IsCrys (P.PD K) ρ₂) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = multV (P.PD K) ρ₁ τ a + multV (P.PD K) ρ₂ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ V₁ _ _ _ _ _ ρ₁ V₂ _ _ _ _ _ ρ₂ e he
  obtain ⟨d1, d1'⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V₁ ρ₁
  obtain ⟨d2, d2'⟩ := GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V₂ ρ₂
  obtain ⟨f1, c1⟩ := dcris_finite_le T K LL V₁ ρ₁
  obtain ⟨f2, c2⟩ := dcris_finite_le T K LL V₂ ρ₂
  have hV : finrank ↥LL.1 V = finrank ↥LL.1 V₁ + finrank ↥LL.1 V₂ := by
    rw [e.finrank_eq, Module.finrank_prod]
  refine ⟨?_, ?_, fun τ a => ?_⟩
  · unfold IsDR
    rw [finrank_DdR_add (P.PD K) e he, hV, mul_add]
    omega
  · unfold IsCrys
    rw [finrank_Dcris_add (P.PD K) e he, hV, mul_add]
    omega
  · unfold multV
    rw [finrank_FildR_add (P.PD K) e he, finrank_FildR_add (P.PD K) e he τ (a + 1)]
    push_cast
    ring

end GlobalTheory.Per.DirectSumHT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAddStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.directSum_deRham_crystalline_jumps_add : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (e : V ≃ₗ[↥LL.1] (V₁ × V₂)), (∀ g v, e (ρ g v) = (ρ₁ g (e v).1, ρ₂ g (e v).2)) → (IsDR (P.PD K) ρ ↔ IsDR (P.PD K) ρ₁ ∧ IsDR (P.PD K) ρ₂) ∧ (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ₁ ∧ IsCrys (P.PD K) ρ₂) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = multV (P.PD K) ρ₁ τ a + multV (P.PD K) ρ₂ τ a := by
  first | exact @GlobalTheory.Per.DirectSumHT.directSum_hodgeTate | exact GlobalTheory.Per.DirectSumHT.directSum_hodgeTate | (intros; apply GlobalTheory.Per.DirectSumHT.directSum_hodgeTate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConditionAboveLCoeffMapFunctorial
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.SelFun

section General

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R M'] [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  (rho : Representation R Γ M) (rho' : Representation R Γ M') (u : M →ₗ[R] M') (hu : Continuous u)
  (he : ∀ g m, u (rho g m) = rho' g (u m))

theorem selMaps_res_map {H : Type} [Group H] [TopologicalSpace H] (phi : H →* Γ) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (mapH1 rho rho' u hu he x) =
      mapH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m) (resH1 rho phi hphi x) := by
  induction x using Submodule.Quotient.induction_on with
  | H z => rfl

theorem selMaps_map_ur (J : Subgroup Γ) (x : H1 rho) (hx : x ∈ H1ur rho J) :
    mapH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have h0 : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (selMaps_res_map rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ h0).trans (map_zero _))

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i)) {Λ : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
  {B B' : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]
  [AddCommGroup B'] [Module Λ B'] [TopologicalSpace B'] [DiscreteTopology B']

theorem localConditionAboveL_coeffMap_functorial (f : B →ₗ[Λ] B') (v : PlE D.host) (x : H1 ((repOn ρ κ B).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ B v) : h1MapSubgroup ρ κ (DecV N v) f x ∈ bkOn bkP i ρ κ B' v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨cocycles1MapOfEquivariant _ _ (f.compLeft (Fin r)) continuous_of_discreteTopology
        (fun g m => repOn_map ρ κ f g.1 m) z, c, y, f b, hc, hy, fun g a => ?_, rfl⟩
      change f ((z : ↥(DecV N v) → Fin r → B) g a) = _
      rw [hz, map_smul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem selmerClass_coeffMap_mem_selmer (f : B →ₗ[Λ] B') (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ B))
    (hx : x ∈ selOn bkP i ρ κ B Q) : h1Map ρ κ f x ∈ selOn bkP i ρ κ B' Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (selMaps_res_map (repOn ρ κ B) (repOn ρ κ B') (f.compLeft (Fin r)) continuous_of_discreteTopology
    (repOn_map ρ κ f) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact localConditionAboveL_coeffMap_functorial bkP i ρ κ f v _ hv
  · exact Submodule.mem_top
  · exact selMaps_map_ur _ _ _ _ _ _ _ hv

theorem selMaps (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) : SelMaps bkP i s κ Q := by
  intro B B' _ _ _ _ _ _ _ _ f
  rintro _ ⟨x, hx, rfl⟩
  exact selmerClass_coeffMap_mem_selmer bkP i _ κ f Q x hx

end GlobalTheory.SelFun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepOnEqOfEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun

namespace GlobalTheory.SelFun.Colim

section General

variable {Γ O Λ : Type} [Group Γ] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
  [TopologicalSpace Γ] {B : Type} [AddCommGroup B] [Module Λ B] [TopologicalSpace B] [DiscreteTopology B]

theorem exists_fg_cocycle [CompactSpace Γ] (z : Z1 (repOn ρ κ B)) :
    ∃ B' : Submodule Λ B, B'.FG ∧ ∃ z' : Z1 (repOn ρ κ B'), ∀ g a, ((z'.1 g a : B') : B) = z.1 g a := by
  have hfin : (Set.range fun p : Γ × Fin r => z.1 p.1 p.2).Finite := by
    have hc : Continuous fun p : Γ × Fin r => z.1 p.1 p.2 :=
      continuous_prod_of_discrete_right.2 fun a => (continuous_apply a).comp z.2.1
    exact (isCompact_range hc).finite_of_discrete
  refine ⟨Submodule.span Λ _, Submodule.fg_span hfin, ⟨fun g a => ⟨z.1 g a, Submodule.subset_span ⟨(g, a), rfl⟩⟩,
    continuous_pi fun a => ((continuous_apply a).comp z.2.1).subtype_mk _, fun g h => ?_⟩, fun g a => rfl⟩
  funext a
  apply Subtype.ext
  have e := congrFun (repOn_map ρ κ (Submodule.span Λ (Set.range fun p : Γ × Fin r => z.1 p.1 p.2)).subtype g
    (fun a => ⟨z.1 h a, Submodule.subset_span ⟨(h, a), rfl⟩⟩)) a
  have e2 := congrFun (z.2.2 g h) a
  exact e2.trans (congrArg (z.1 g a + ·) e.symm)

omit [TopologicalSpace Γ] [TopologicalSpace B] [DiscreteTopology B] in
theorem repOn_eq_of_eq_one {g : Γ} (h1 : ρ g = 1) (h2 : κ g = 1) (m : Fin r → B) : repOn ρ κ B g m = m := by
  have : repOn ρ κ B g = repOn ρ κ B 1 := by simp [repOn, h1, h2]
  rw [this, map_one, Module.End.one_apply]

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem tgl_eq_one (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) (v : PlE D.host)
    (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (A : ValuationSubring N.Om) (hA : IsPlaceOver A v)
    (σ : GE N) (hσ : σ ∈ Ine (F := D.host.E) A) : Tgl i s σ = 1 := by
  have hg : ∀ k, v ∉ placesOver D.host.E (D.host.g k) := fun k hk =>
    hS ⟨Or.inl (Set.mem_iUnion.2 ⟨k, hk⟩), hl⟩
  have hp : v ∉ X.pD i := fun hk => hS ⟨Or.inr hk, hl⟩
  have h1 : X.rhoS i s σ = 1 := h.1 v hl hg A hA σ hσ
  have h2 : chiS i s σ = 1 := X.twistCharacterFamily_unramified i _ _ v hl hg hp A hA σ hσ
  simp [Tgl, twGL, h1, h2]

theorem selColim : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ → LocSat bkP i s κ → SelColim bkP i s κ Q := by
  intro D N X bkP i s Λ _ _ _ κ Q hSet _ hSat B _ _ _ _ hB y hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨B', hfg, z', hz⟩ := exists_fg_cocycle (Tgl i s) κ z
  have hmap : h1Map (Tgl i s) κ B'.subtype (Submodule.Quotient.mk z') = Submodule.Quotient.mk z :=
    congrArg Submodule.Quotient.mk (Subtype.ext (funext fun g => funext fun a => hz g a))
  refine ⟨B', hfg, Submodule.Quotient.mk z', ?_, hmap⟩
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hy v
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with hl hS
  · refine hSat v hl B' B hB B'.subtype B'.injective_subtype _ ?_
    rw [← hmap] at hv
    exact hv
  · trivial
  · have hS1 : v ∉ Spl i := fun h => hS (Or.inl h)
    have hQ : v ∉ Q := fun h => hS (Or.inr h)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hv)
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨0, fun g => ?_⟩)
    have hg : (g.1.1 : GE N) ∈ Ine (F := D.host.E) (N.plOm.1 v) := g.2
    have e : z.1 g.1.1 = repOn (Tgl i s) κ B g.1.1 m - m := hm g
    rw [repOn_eq_of_eq_one _ _ (tgl_eq_one bkP i s hSet.1.1 v hl hS1 _ (N.plOm.2 v) _ hg)
      (hSet.2.2.2.2.2.2.2 v hQ _ (N.plOm.2 v) _ hg), sub_self] at e
    show z'.1 g.1.1 = repOn (Tgl i s) κ B' g.1.1 0 - 0
    rw [LinearMap.map_zero, sub_zero]
    funext a
    apply Subtype.ext
    exact (hz g.1.1 a).trans (congrFun e a)

end GlobalTheory.SelFun.Colim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContCoreTied
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.FundCont

theorem contCore_tied : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.contCore (P.PD K) :=
  fun _ _ _ AI T K => contCore_of_tied AI T K

end GlobalTheory.FundCont
end
