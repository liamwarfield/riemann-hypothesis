module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralQuotientEqIntegralFactorQuotient
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBessel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof : ∀ D : D7, GlobalTheory.FinPl.HandInv D := by
  first | exact @GlobalTheory.FinPl.HandInvPf.handInv | exact GlobalTheory.FinPl.HandInvPf.handInv | (intros; apply GlobalTheory.FinPl.HandInvPf.handInv <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepFiniteIntegralCollapseTwistPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffFourierJacob
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffFourierJacob
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepSupp

variable {D : D7}

theorem mem_cong {V : HSp D} {I : Ideal (AE D)} {g : GA D V}
    (h : ∀ i j, mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I) : g ∈ congGrp V I := by
  unfold congGrp
  rw [MonoidHom.mem_ker]
  ext i j
  have := h i j
  rw [← Ideal.Quotient.eq] at this
  simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
  exact this

theorem off_union {V : HSp D} {P P' R : Pl D → Prop} (hR : ∀ p, R p → P p ∨ P' p) {g : GA D V} (h : g ∈ grpOff V P)
    (h' : g ∈ grpOff V P') : g ∈ grpOff V R := by
  refine mem_cong fun i j => ?_
  have a := GlobalTheory.DisjComb.mem_congGrp' h i j
  have b := GlobalTheory.DisjComb.mem_congGrp' h' i j
  unfold idOff at a b ⊢
  simp only [Submodule.mem_iInf] at a b ⊢
  intro u
  rcases hR u.1 u.2 with k | k
  · exact a ⟨u.1, k⟩
  · exact b ⟨u.1, k⟩

theorem at_le_off (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' :=
  (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V ∅).2.2.2.2.2.2.1 P P' h

theorem at_eq (V : HSp D) (P : Pl D → Prop) : grpAt V P = GfC V ⊓ grpOff V (fun p => ¬ P p) := by
  rw [(GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V ∅).2.2.2.2.2.2.2.1]
  simp only [not_not]

theorem at_le_fin (V : HSp D) (P : Pl D → Prop) : grpAt V P ≤ GfC V := by
  rw [at_eq]; exact inf_le_left

theorem at_mono (V : HSp D) {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : grpAt V P ≤ grpAt V P' := by
  rw [at_eq V P']
  exact le_inf (at_le_fin V P) (at_le_off V fun p hp hn => hn (h p hp))

theorem split_two (V : HSp D) (A B : Finset (Pl D)) {x : GA D V} (hx : x ∈ GfC V)
    (ho : x ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B)) :
    ∃ a ∈ grpAt V (· ∈ A), ∃ b ∈ grpAt V (· ∈ B), b ∈ grpAt V (· ∉ A) ∧ x = a * b := by
  obtain ⟨e, he⟩ := (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D V A).2.2.2.2.2.1
  obtain ⟨⟨a, b⟩, hab⟩ := e.surjective ⟨x, hx⟩
  have h1 : x = a.1 * b.1 := by
    have := he (a, b)
    rw [hab] at this
    exact this
  refine ⟨a.1, a.2, b.1, ?_, b.2, h1⟩
  rw [at_eq]
  refine ⟨at_le_fin V _ b.2, ?_⟩
  have hb1 : b.1 ∈ grpOff V (fun p => p ∉ A ∧ p ∉ B) := by
    have : b.1 = a.1⁻¹ * x := by rw [h1]; group
    rw [this]
    exact mul_mem (inv_mem (at_le_off V (fun p hp hn => hn.1 hp) a.2)) ho
  have hb2 : b.1 ∈ grpOff V (· ∈ A) := at_le_off V (fun p hp hn => hp hn) b.2
  refine off_union (fun p hp => ?_) hb1 hb2
  by_cases h : p ∈ A
  · exact Or.inr h
  · exact Or.inl ⟨h, hp⟩

theorem vac_om {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {P : Pl D → Prop} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT P f) {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P) (hh : h ∈ grpOff T P) :
    Vac ψ S T LS LT P (om (g, h) f) := by
  have key : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, heisO ψ S T u f = f →
      heisO ψ S T u (om (g, h) f) = om (g, h) f := by
    intro u hu e
    have := hW.om_heis g h u f hf.1
    rw [GlobalTheory.DisjComb.actO_off hg hh (GlobalTheory.FinPl.LatMem.latO_mxAt hu), e] at this
    exact this.symm
  refine ⟨hW.om_pres _ _ hf.1, fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2) (hf.2.1 u hu),
    fun e he u hu hh' => key u hu (hf.2.2 e he u hu hh')⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P Q : Pl D → Prop}
    (hQ : ∀ p, Q p → P p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P f) : Vac ψ S T LS LT Q f := by
  have hm : latO S T (LS : Set _) (LT : Set _) Q ≤ latO S T (LS : Set _) (LT : Set _) P := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, hv, rest⟩
    exact ⟨α, hα, fun v hv' => hv v fun hq => hv' (hQ v hq), rest⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hm hu), fun e he u hu => hf.2.2 e he u (hm hu)⟩

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ GfC (c.V (j + 1)), ∀ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1), q₁ = r * y * (κ * k) := by
  intro D c v t w hc hv ht hf _ hoff hG _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ _ G x a _ f _ q₁ hq₁ q₂ hne
  have DC := GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1))
  have hom := (ht.sBF j (σ + 1) h).1
  have hW : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j (σ + 1) h).χV (t.sBF j (σ + 1) h).χW (t.om j) := by
    rw [← hom]; exact (t.sBF j (σ + 1) h).weil
  have hGQ : ∀ p, p ∈ w.Q → p ∉ v.gP := fun p hp => Finset.disjoint_left.1 hf.disjG hp

  obtain ⟨g, hg, hflat⟩ : ∃ g ∈ grpAt (c.V j) (· ∈ w.Q), flatBF (t.sBF j (σ + 1) h)
      (t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))) ≠ 0 := by
    unfold integ at hne
    obtain ⟨α, -, hα⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨g, hg, hg'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hα
    refine ⟨g, (hf.e j α).2 g hg, fun h0 => hg' ?_⟩
    rw [← hom] at h0
    have H := GlobalTheory.HandHom.hand_hom D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (φ α)
    unfold Chain.hand
    erw [h0, H.2.1]
    have := H.2.2 0 1 0 (rTrans q₂ f)
    rw [zero_smul, one_smul, zero_mul, zero_mul] at this
    erw [this, mul_zero]

  have vQ : ∀ P : Pl D → Prop, (∀ p, p ∈ w.Q → ¬ P p) →
      Vac c.ψ _ _ (v.N j) (v.N (j + 1)) P (comb c.ψ _ _ (w.eQ j) Ψ₁) := fun P hP =>
    ((DC (· ∈ w.Q) P hP).2.1 (w.eQ j) (hf.atQ j).1).2 _ _ _ (vac_mono (fun _ _ => trivial) h₁)
  have k₁ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) :=
    ((DC (· ∈ v.gP) (offP v w) (fun p hp hn => hn.1 hp)).2.1 (v.eG j) (hv.atG j).1).2 _ _ _
      (vQ _ fun p hp hn => hn.2 hp)
  have k₂ : ∀ P, Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) P Ψ₂ := fun P => vac_mono (fun _ _ => trivial) h₂
  have k₁' := vac_om hW k₁ (at_le_off _ (fun p hp hn => hn.2 hp) hg) (one_mem (grpOff (c.V (j + 1)) (offP v w)))
  have mulom : ∀ (g₁ g₂ : GA D (c.V j)) (y₁ y₂ : GA D (c.V (j + 1))) (Φ : WO (c.V j) (c.V (j + 1)) → ℂ),
      t.om j (g₁ * g₂, y₁ * y₂) Φ = t.om j (g₁, y₁) (t.om j (g₂, y₂) Φ) := by
    intro g₁ g₂ y₁ y₂ Φ
    rw [← Prod.mk_mul_mk, map_mul, Module.End.mul_apply]
  obtain ⟨r, hr, hrP, z, hz, κ, hκ, hdec⟩ := (hoff j σ h _ _ k₁' (k₂ _)).2.2.1 q₁ (by
    rw [← mulom, one_mul, mul_one]; exact hflat)
  have hzf : z ∈ GfC (c.V (j + 1)) := by
    have : z = r⁻¹ * q₁ * κ⁻¹ := by rw [hdec]; group
    rw [this]
    exact mul_mem (mul_mem (inv_mem (at_le_fin _ _ hrP)) hq₁) (inv_mem (at_le_fin _ _ hκ.1))
  obtain ⟨s, hs, y, hy, hy', hzs⟩ := split_two (c.V (j + 1)) v.gP w.Q hzf hz

  have e₁ := ((hoff j σ h _ _ k₁ (k₂ _)).1 κ hκ).1
  have hgo : g ∈ grpOff (c.V j) (· ∈ v.gP) := at_le_off _ hGQ hg
  have hyo : y ∈ grpOff (c.V (j + 1)) (· ∈ v.gP) := at_le_off _ hGQ hy
  have vG := vQ (· ∈ v.gP) hGQ
  have e₂ := (DC (· ∈ v.gP) (fun _ => False) (fun _ _ => id)).2.2.1 _ _ _ hW (v.eG j) (hv.atG j).1 g hgo y hyo _ vG.1
  have e₃ : t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) =
      t.om j (1, r) (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) := by
    rw [← e₂]
    conv_rhs => rw [← e₁]
    rw [← mulom, ← mulom, ← mulom, hdec, hzs]
    simp only [one_mul, mul_one, mul_assoc]
  have th : IsThetaFunO c.ψ _ _ (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) := by
    rw [← e₂]
    exact hW.om_pres _ _ (hW.om_pres _ _ k₁.1)
  have hfl : flatBF (t.sBF j (σ + 1) h)
      (t.om j (1, s) (comb c.ψ _ _ (v.eG j) (t.om j (g, y) (comb c.ψ _ _ (w.eQ j) Ψ₁)))) ≠ 0 := by
    intro h0
    apply hflat
    have := ((GlobalTheory.T.flatMap_handedFunction_vanishing_period_invariant D c.ψ (offP v w)).1 _ _ _ (t.sBF j (σ + 1) h) _ th r hr hrP).2 h0
    rw [hom] at this
    rw [e₃]
    exact this
  obtain ⟨r', hr', hr'P, k, hk, hsk⟩ := (hG j σ h _ _ (vac_om hW vG hgo hyo) (k₂ _)).1 s hs hfl
  refine ⟨r * r', mul_mem hr hr', mul_mem (at_le_fin _ _ hrP) (at_le_fin _ _ hr'P), y, hy, κ, hκ, k, hk, ?_⟩
  have hkP : k ∈ grpAt (c.V (j + 1)) (· ∈ v.gP) := (hv.JG (j + 1) (by omega)).1 hk
  have hcm := (GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) v.gP).2.2.2.2.1 k hkP (y * κ)
    (mul_mem hy' (at_mono _ (fun p hp => hp.1) hκ.1))
  rw [hdec, hzs, hsk]
  calc r * (r' * k * y) * κ = r * r' * (k * (y * κ)) := by group
    _ = r * r' * y * (κ * k) := by rw [hcm]; group

end GlobalTheory.DStepSupp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffFourierJacobStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_fourierJacobi : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ q₁ ∈ GfC (c.V (j + 1)), ∀ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ ∧ ∃ k ∈ v.JG (j + 1), q₁ = r * y * (κ * k) := by
  first | exact @GlobalTheory.DStepSupp.main | exact GlobalTheory.DStepSupp.main | (intros; apply GlobalTheory.DStepSupp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantBesselSecond
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantBesselSecond
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepCell.LeftSecond

variable {D : D7}

theorem contAut_translate {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_of_mem_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsmul : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsmul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact hadd hx hy
  | zero =>
    have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
    simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsmul (h x) c

theorem theta_comb {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T e f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.2.1 e f hf
    ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).1 hψ

theorem integ_left_second : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (r * q₂) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f hf r hr q₁ q₂
  have hΦ₁ := theta_comb hc.std (hv.atG j).1 (theta_comb hc.std (hF.atQ j).1 h₁.1)
  have hΦ₂ := theta_comb hc.std (hv.atG (j + 1)).1 (theta_comb hc.std (hF.atQ (j + 1)).1 h₂.1)
  obtain ⟨J, χ, hle⟩ := ht.CC (j + 1 + 1) (by omega)
  have hfc : IsContAut (c.V (j + 1 + 1)) f := hf ▸ contAut_translate _ (contAut_of_mem_multT (hle G.2) x)
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => congrArg (w.ε j α g * ·) ?_
  exact (GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof D c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sBF j (σ + 1) h)
    (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ hΦ₁ hΦ₂ (φ α) (hv.ram j _ (hφ α)).1 g q₁ q₂).2 f hfc r hr

end GlobalTheory.DStepCell.LeftSecond

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantBesselSecondStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_integrand_leftInvariant_bessel_second : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (r * q₂) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepCell.LeftSecond.integ_left_second | exact GlobalTheory.DStepCell.LeftSecond.integ_left_second | (intros; apply GlobalTheory.DStepCell.LeftSecond.integ_left_second <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFir
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFir
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepCell.LeftOne

theorem vac_empty_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {LS : Lat S} {LT : Lat T} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => False) f) : Vac ψ S T LS LT (fun _ => False) (comb ψ S T e f) :=
  ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).2 LS LT f hf

theorem vac_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT (fun _ => False) f := by
  have h := (GlobalTheory.DisjComb.main D ψ hψ S T (fun _ => True) (fun _ => False) (fun _ _ h => h)).2.2.2.2 LS LT f hS hT
  have e : (fun p : Pl D => True ∨ False) = fun _ => True := by funext p; simp
  rw [e] at h
  exact (h.1 hf).2

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (r * q₁) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv _ hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f _ r hr q₁ q₂
  have s0 := hv.sd j (by omega)
  have s1 := hv.sd (j + 1) (by omega)
  have s2 := hv.sd (j + 1 + 1) (by omega)
  have t₁ := (vac_empty_comb hc.std (hv.atG j).1 (vac_empty_comb hc.std (hF.atQ j).1 (vac_empty hc.std s0 s1 h₁))).1
  have t₂ := (vac_empty_comb hc.std (hv.atG (j + 1)).1
    (vac_empty_comb hc.std (hF.atQ (j + 1)).1 (vac_empty hc.std s1 s2 h₂))).1
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  have key := (GlobalTheory.T.doubleStepIntegrandBesselPeriodInvariant_proof D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ t₁ t₂ (φ α)
    (hv.ram j (φ α) (hφ α)).1 g q₁ q₂).1 r hr
  exact congrArg (fun z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ z (rTrans q₂ f)) key

end GlobalTheory.DStepCell.LeftOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFirStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStep_integrand_leftInvariant_fourierJacobi_first : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (r * q₁) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepCell.LeftOne.main | exact GlobalTheory.DStepCell.LeftOne.main | (intros; apply GlobalTheory.DStepCell.LeftOne.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondOffLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondOffLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepOffSnd

theorem vac_off {D : D7} {c : Comm D} (v : VCom c) {t : Tup c} (w : VTup t) (hc : c.Is) (hv : v.Is) (hw : VForm v w)
    (i : ℕ) (hi : i + 1 < D.R.m) (Ψ : WO (c.V i) (c.V (i + 1)) → ℂ)
    (hΨ : Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (fun _ => True) Ψ) :
    Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (offP v w) (comb c.ψ _ _ (v.eG i) (comb c.ψ _ _ (w.eQ i) Ψ)) := by
  have h0 : Vac c.ψ _ _ (v.N i) (v.N (i + 1)) (offP v w) Ψ := by
    have key := (GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (offP v w) (fun p => ¬ offP v w p)
      (fun p hp hn => hn hp)).2.2.2.2 (v.N i) (v.N (i + 1)) Ψ (hv.sd i (by omega)) (hv.sd (i + 1) hi)
    have e : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ => True := by
      funext p; exact eq_true (Classical.em _)
    rw [e] at key
    exact (key.1 hΨ).1
  have h1 := ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (· ∈ w.Q) (offP v w)
      (fun p hp hn => hn.2 hp)).2.1 (w.eQ i) (hw.atQ i).1).2 _ _ _ h0
  exact ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V i) (c.V (i + 1)) (· ∈ v.gP) (offP v w)
      (fun p hp hn => hn.1 hp)).2.1 (v.eG i) (hv.atG i).1).2 _ _ _ h1

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * κ) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hw _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ _ G x a ha f hf κ hκ q₁ q₂
  have hΦ₁ := vac_off v w hc hv hw j (by omega) Ψ₁ hΨ₁
  have hΦ₂ := vac_off v w hc hv hw (j + 1) (by omega) Ψ₂ hΨ₂
  have hfix := (hoff j σ h _ _ hΦ₁ hΦ₂).2.1 κ hκ
  have hom : t.om (j + 1) (q₁, q₂ * κ) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    have e : ((q₁, q₂ * κ) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (1, κ) := by simp
    rw [e, map_mul, Module.End.mul_apply, hfix]
  have hrow : rTrans κ f = f := by
    rw [hf]; exact (hw.row (j + 1 + 1) (by omega) G x a ha).2 κ hκ
  have hr : rTrans (q₂ * κ) f = rTrans q₂ f := by
    conv_rhs => rw [← hrow]
    funext g; simp only [rTrans, mul_assoc]
  have hs := (ht.sFB j σ h).1
  have hom' : (t.sFB j σ h).om (q₁, q₂ * κ) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      (t.sFB j σ h).om (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    rw [hs]; exact hom
  unfold integ Chain.hand
  rw [hr]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (fun Z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ
    (handFB (t.sFB j σ h) (c.vL j σ h) (handBF (t.sBF j (σ + 1) h) (c.lnk j σ h) (φ α) (flatBF (t.sBF j (σ + 1) h)
      ((t.sBF j (σ + 1) h).om (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁))))) (flatFB (t.sFB j σ h) Z))
      (rTrans q₂ f)) hom'

end GlobalTheory.DStepOffSnd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantSecondOffLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_offLevel : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1 + 1)) (v.N (j + 1 + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (q₂ * κ) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepOffSnd.main | exact GlobalTheory.DStepOffSnd.main | (intros; apply GlobalTheory.DStepOffSnd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstOffLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstOffLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepOff

theorem vac_off {D : D7} {c : Comm D} {v : VCom c} {t : Tup c} {w : VTup t} (hc : c.Is) (hv : v.Is) (hf : VForm v w)
    (j : ℕ) (hj : j + 1 < D.R.m) (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ)
    (hΨ : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ) :
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ)) := by
  have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (offP v w) Ψ := by
    have h1 := (GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (offP v w) (fun p => ¬ offP v w p)
      (fun p hp hn => hn hp)).2.2.2.2 (v.N j) (v.N (j + 1)) Ψ (hv.sd j (by omega)) (hv.sd (j + 1) hj)
    have h2 : (fun p => offP v w p ∨ ¬ offP v w p) = fun _ : Pl D => True := by
      funext p; exact propext ⟨fun _ => trivial, fun _ => em _⟩
    rw [h2] at h1
    exact (h1.1 hΨ).1
  have hQ := ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ w.Q) (offP v w)
    (fun p hp hn => hn.2 hp)).2.1 (w.eQ j) (hf.atQ j).1).2 _ _ _ h0
  exact ((GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1)) (· ∈ v.gP) (offP v w)
    (fun p hp hn => hn.1 hp)).2.1 (v.eG j) (hv.atG j).1).2 _ _ _ hQ

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * κ) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hf _ hoff _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ _ G x a _ f _ κ hκ q₁ q₂
  have k₁ := vac_off hc hv hf j (by omega) Ψ₁ h₁
  have k₂ := vac_off hc hv hf (j + 1) (by omega) Ψ₂ h₂
  obtain ⟨e₁, e₂⟩ := (hoff j σ h _ _ k₁ k₂).1 κ hκ
  have a₁ : ∀ g, t.om j (g, q₁ * κ) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) =
      t.om j (g, q₁) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) := by
    intro g
    have : ((g, q₁ * κ) : GA D (c.V j) × GA D (c.V (j + 1))) = (g, q₁) * (1, κ) := by simp
    rw [this, map_mul, Module.End.mul_apply, e₁]
  have a₂ : t.om (j + 1) (q₁ * κ, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) =
      t.om (j + 1) (q₁, q₂) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) := by
    have : ((q₁ * κ, q₂) : GA D (c.V (j + 1)) × GA D (c.V (j + 1 + 1))) = (q₁, q₂) * (κ, 1) := by simp
    rw [this, map_mul, Module.End.mul_apply, e₂]
  rw [← (ht.sBF j (σ + 1) h).1] at a₁
  rw [← (ht.sFB j σ h).1] at a₂
  unfold integ Chain.hand
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  erw [a₁ g, a₂]

end GlobalTheory.DStepOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstOffLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_offLevel : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ κ, InK (c.V (j + 1)) (v.N (j + 1)) (offP v w) κ → ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * κ) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepOff.main | exact GlobalTheory.DStepOff.main | (intros; apply GlobalTheory.DStepOff.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstFixedLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstFixedLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepLev
variable {D : D7}

theorem vac_of_all {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : Pl D → Prop)
    {f : WO S T → ℂ} (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT P f := by
  have hle : latO S T (↑LS) (↑LT) P ≤ latO S T (↑LS) (↑LT) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, hr⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, hr⟩
  exact ⟨hf.1, fun u hu => hf.2.1 u (hle hu), fun e he u hu => hf.2.2 e he u (hle hu)⟩

theorem hand_mul_right {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ}
    (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank)
    (Φ₁ : WO B.V J.W → ℂ) (Φ₂ : WO J.W B'.V → ℂ) (φ : GA D B.A → ℂ) (k : GA D J.W) (a : ℂ) (ha : a ≠ 0)
    (h₁ : s₁.om (1, k) Φ₁ = a⁻¹ • Φ₁) (h₂ : s₂.om (k, 1) Φ₂ = a • Φ₂) (g : GA D B.V) (q₁ : GA D J.W) (q₂ : GA D B'.V) :
    Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g (q₁ * k) q₂ = Chain.hand s₁ s₂ l vL Φ₁ Φ₂ φ g q₁ q₂ := by
  have e₁ : s₁.om (g, q₁ * k) Φ₁ = a⁻¹ • s₁.om (g, q₁) Φ₁ := by
    rw [show ((g, q₁ * k) : GA D B.V × GA D J.W) = (g, q₁) * (1, k) from by simp, map_mul, Module.End.mul_apply, h₁,
      LinearMap.map_smul]
  have e₂ : s₂.om (q₁ * k, q₂) Φ₂ = a • s₂.om (q₁, q₂) Φ₂ := by
    rw [show ((q₁ * k, q₂) : GA D J.W × GA D B'.V) = (q₁, q₂) * (k, 1) from by simp, map_mul, Module.End.mul_apply, h₂,
      LinearMap.map_smul]
  unfold Chain.hand
  rw [e₁, e₂, (GlobalTheory.HandHom.hand_hom D ψ σ B J B' s₁ s₂ l vL φ).1, inv_mul_cancel₀ ha, one_smul]

theorem integ_lev : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * k) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ _ G x a _ f _ k hk q₁ q₂
  obtain ⟨b, hb, l₁, l₂, -⟩ := hF.lawG j (by omega) k hk
  have hd : ∀ p, p ∈ w.Q → ¬ p ∈ v.gP := fun p hp => Finset.disjoint_left.1 hF.disjG hp
  have v₁ := ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· ∈ w.Q) (· ∈ v.gP) hd).2.1 (w.eQ j) (hF.atQ j).1).2 _ _ _
    (vac_of_all (· ∈ v.gP) hΨ₁)
  have v₂ := ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· ∈ w.Q) (· ∈ v.gP) hd).2.1 (w.eQ (j + 1)) (hF.atQ (j + 1)).1).2 _ _ _
    (vac_of_all (· ∈ v.gP) hΨ₂)
  have m₁ := l₁ _ v₁
  have m₂ := l₂ (by omega) _ v₂
  rw [← (ht.sBF j (σ + 1) h).1] at m₁
  rw [← (ht.sFB j σ h).1] at m₂
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  exact congrArg (fun y => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ y (rTrans q₂ f))
    (hand_mul_right (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ (φ α) k b hb m₁ m₂ g q₁ q₂)

end GlobalTheory.DStepLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandRightInvariantFirstFixedLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_fixedLevel : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ k ∈ v.JG (j + 1), ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (q₁ * k) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  first | exact @GlobalTheory.DStepLev.integ_lev | exact GlobalTheory.DStepLev.integ_lev | (intros; apply GlobalTheory.DStepLev.integ_lev <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepCell


set_option maxHeartbeats 4000000 in
theorem cell_collapse : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) ρ₁ μ₁ ρ₂ μ₂, IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁ → IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂ → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ z, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) (v.kap j σ h * z) := by
  classical
  intro D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h ρ₁ μ₁ ρ₂ μ₂ hN₁ hN₂ Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf z hz
  change Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) z at hz
  change Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
    (fun q₁ q₂ => integ v w j σ h Ψ₁ Ψ₂ φ f q₁.1 q₂.1) (v.kap j σ h * z)
  have hA1 := GlobalTheory.T.doubleStep_integrand_leftInvariant_fourierJacobi_first D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hA2 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hA3 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_first_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hB := GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_fourierJacobi D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC1 := GlobalTheory.T.doubleStep_integrand_leftInvariant_bessel_second D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC2 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_offLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC3 := GlobalTheory.T.doubleStepIntegrand_rightInvariant_second_fixedLevel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  have hC4 := GlobalTheory.T.seeSaw_doubleStep_integrand_vanishes_off_bessel D c v t w hc hv ht hVF hWe hOff hGS hQF hCL hFL j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂ φ hφ G x a ha f hf
  set F := integ v w j σ h Ψ₁ Ψ₂ φ f with hFdef
  obtain ⟨f₁', hf₁', hinn⟩ := hz

  obtain ⟨-, hfc₁, -, -, -, hd₁⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1))
  obtain ⟨-, hfc₂, -, -, -, hd₂⟩ := GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular D (c.V (j + 1 + 1))
  have invJ : (c.ρJ j (σ + 1) h).IsInvInvariant := (hd₁ _ _ (c.jac j (σ + 1) h).d).1.2.2 _ (hc.ρJ j (σ + 1) h)
  have invB : (c.ρB (j + 1 + 1) σ (idx_step h)).IsInvInvariant :=
    ((hd₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o).2.2 _ (hc.ρB _ _ _)
  obtain ⟨hQc₁, hQ'c₁, hQle₁, hQ'le₁, hcm₁, he₁, -, -, -, hR₁⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1)) w.Q
  obtain ⟨hQc₂, hQ'c₂, hQle₂, hQ'le₂, hcm₂, he₂, -, -, -, hR₂⟩ := GlobalTheory.T.unitaryFiniteAdelicGroup_split_finitePlaceSet D (c.V (j + 1 + 1)) w.Q
  have splitJ := (hR₁ _ _ (c.jac j (σ + 1) h).d).1
  have splitB := (hR₂ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d).2 _ _ (c.bes (j + 1 + 1) σ (idx_step h)).o
  have hJcl := GlobalTheory.jacGrp_isClosed D _ _ _ (c.jac j (σ + 1) h).d
  have hBcl := GlobalTheory.BesClosed.besGrp_isClosed D _ _ _ _ _ (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o

  obtain ⟨hJG₁, hJG₁c, hJG₁o⟩ := hv.JG (j + 1) (by omega)
  obtain ⟨hJG₂, hJG₂c, hJG₂o⟩ := hv.JG (j + 1 + 1) (by omega)
  obtain ⟨K₁, K₂, hK₁, hK₁Q, hK₂Q, hK₁c, hK₂c, hK₁o, hK₂o, hK₂, hKK⟩ :=
    GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away D _ (v.N (j + 1)) v.gP w.Q (v.JG (j + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₁ hJG₁c hJG₁o
  obtain ⟨K₁', K₂', hK₁', hK₁Q', hK₂Q', hK₁c', hK₂c', hK₁o', hK₂o', hK₂', hKK'⟩ :=
    GlobalTheory.T.exists_latticeStabilizer_twist_and_level_away D _ (v.N (j + 1 + 1)) v.gP w.Q (v.JG (j + 1 + 1)) (hv.sd _ (by omega)) hVF.disjG hJG₂ hJG₂c hJG₂o
  have hμ₁K : μ₁ {g | (g : GA D (c.V (j + 1))) ∈ K₁} = 1 := by
    rw [show {g : grpAt (c.V (j + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1))) ∈ K₁} =
      {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁ g.1]
    exact hN₁.2.2.1
  have hρ₁K : ρ₁ {g | ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} = 1 := by
    rw [show {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (grpAt (c.V (j + 1)) (· ∈ w.Q)) |
      ((g : grpAt (c.V (j + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1))) ∈ K₁} =
      {g | InK _ (v.N (j + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁ g.1.1]
    exact hN₁.2.2.2
  have hμ₂K : μ₂ {g | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1 := by
    rw [show {g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q) | (g : GA D (c.V (j + 1 + 1))) ∈ K₁'} =
      {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1} from Set.ext fun g => hK₁' g.1]
    exact hN₂.2.2.1
  have hρ₂K : ρ₂ {g | ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} = 1 := by
    rw [show {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
        (grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) |
      ((g : grpAt (c.V (j + 1 + 1)) (· ∈ w.Q)) : GA D (c.V (j + 1 + 1))) ∈ K₁'} =
      {g | InK _ (v.N (j + 1 + 1)) (· ∈ w.Q) g.1.1} from Set.ext fun g => hK₁' g.1.1]
    exact hN₂.2.2.2

  have hinner : ∀ q₁ : grpAt (c.V (j + 1)) (· ∈ w.Q), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F q₁.1 g.1) (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * f₁' q₁) := by
    intro q₁
    have hl : ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o,
        r ∈ GfC (c.V (j + 1 + 1)) → ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (r * g) = F q₁.1 g :=
      fun r hr _ g _ => hC1 r hr q₁.1 g
    have hr : ∀ k ∈ K₂', ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 (g * k) = F q₁.1 g := by
      intro k hk g _
      obtain ⟨κ, hκ, k', hk', rfl⟩ := (hK₂' k).1 hk
      rw [← mul_assoc, hC3 k' hk', hC2 κ hκ]
    have hs : ∀ g ∈ GfC (c.V (j + 1 + 1)), F q₁.1 g ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d
        (c.bes (j + 1 + 1) σ (idx_step h)).o, r ∈ GfC (c.V (j + 1 + 1)) ∧ ∃ y ∈ grpAt (c.V (j + 1 + 1)) (· ∈ w.Q),
        ∃ k ∈ K₂', g = r * y * k := by
      intro g hg hne
      obtain ⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩ := hC4 q₁.1 q₁.2 g hg hne
      exact ⟨r, hr, hrG, y, hy, κ * k, (hK₂' _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩
    have H := GlobalTheory.T.integral_quotient_eq_integral_factor_quotient (GA D (c.V (j + 1 + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q))
      (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) K₁' K₂'
      hfc₂ hQc₂ hQ'c₂ hBcl hQle₂ hQ'le₂ hcm₂ he₂ splitB hK₁Q' hK₂Q' hK₁c' hK₂c' hK₁o' hK₂o'
      (c.ρB _ _ _) (c.μf _) ρ₂ μ₂ (hc.ρB _ _ _) (hc.μf _) hN₂.2.1 hN₂.1 invB hμ₂K hρ₂K (F q₁.1) (f₁' q₁) hl hr hs (hinn q₁)
    have e1 : {g : GfC (c.V (j + 1 + 1)) | ∃ a ∈ K₁', ∃ b ∈ K₂', (g : GA D (c.V (j + 1 + 1))) = a * b} =
        {g | g.1 ∈ v.K (j + 1 + 1)} := Set.ext fun g => hKK' g.1
    have e2 : {g : (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
        (GfC (c.V (j + 1 + 1))) | ∃ a ∈ K₁', ∃ b ∈ K₂', ((g : GfC (c.V (j + 1 + 1))) : GA D (c.V (j + 1 + 1))) = a * b} =
        {g | g.1.1 ∈ v.K (j + 1 + 1)} := Set.ext fun g => hKK' g.1.1
    rw [e1, e2] at H
    exact H

  haveI : LocallyCompactSpace (GfC (c.V (j + 1 + 1))) := hfc₂.locallyCompactSpace
  haveI := hc.μf (j + 1 + 1)
  haveI := hc.ρB (j + 1 + 1) σ (idx_step h)
  haveI := invB
  have hBcl' : IsClosed (((besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o).subgroupOf
      (GfC (c.V (j + 1 + 1))) : Subgroup _) : Set (GfC (c.V (j + 1 + 1)))) := hBcl.preimage continuous_subtype_val
  have huniq : ∀ (Φ : GfC (c.V (j + 1 + 1)) → ℂ) (z₁ z₂ : ℂ), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h))
      (c.μf (j + 1 + 1)) Φ z₁ → IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) Φ z₂ → z₁ = z₂ :=
    fun Φ z₁ z₂ h1 h2 => IsQuotIntL1.unique hBcl' h1 h2

  have hex : ∀ q : GfC (c.V (j + 1)), ∃ z', IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F q.1 g.1) z' := by
    intro q
    by_cases hq : ∃ q₂, F q.1 q₂ ≠ 0
    · obtain ⟨q₂, hq₂⟩ := hq
      obtain ⟨r, hr, -, y, hy, κ, hκ, k, hk, e⟩ := hB q.1 q.2 q₂ hq₂
      have e' : F q.1 = F y := funext fun q₂ => by rw [e, ← mul_assoc, hA3 k hk, hA2 κ hκ, hA1 r hr]
      exact ⟨_, by rw [e']; exact hinner ⟨y, hy⟩⟩
    · push_neg at hq
      refine ⟨0, ?_⟩
      have e : (fun g : GfC (c.V (j + 1 + 1)) => F q.1 g.1) = 0 := funext fun g => hq g.1
      rw [e]
      exact IsQuotIntL1.zero
  let fo : GA D (c.V (j + 1)) → ℂ := fun y => if hy : y ∈ GfC (c.V (j + 1)) then (hex ⟨y, hy⟩).choose else 0
  have hfo_spec : ∀ y (hy : y ∈ GfC (c.V (j + 1))), IsQuotIntL1 (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1))
      (fun g => F y g.1) (fo y) := by
    intro y hy
    have e : fo y = (hex ⟨y, hy⟩).choose := dif_pos hy
    rw [e]
    exact (hex ⟨y, hy⟩).choose_spec
  have hleft : ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) → ∀ g ∈ GfC (c.V (j + 1)), fo (r * g) = fo g := by
    intro r hr hrG g hg
    have e : F (r * g) = F g := funext fun q₂ => hA1 r hr g q₂
    have h1 := hfo_spec _ (mul_mem hrG hg)
    rw [e] at h1
    exact huniq _ _ _ h1 (hfo_spec g hg)
  have hright : ∀ k ∈ K₂, ∀ g ∈ GfC (c.V (j + 1)), fo (g * k) = fo g := by
    intro k hk g hg
    have hkG : k ∈ GfC (c.V (j + 1)) := hQ'le₁ (hK₂Q hk)
    obtain ⟨κ, hκ, k', hk', e0⟩ := (hK₂ k).1 hk
    have e : F (g * k) = F g := funext fun q₂ => by rw [e0, ← mul_assoc, hA3 k' hk', hA2 κ hκ]
    have h1 := hfo_spec _ (mul_mem hg hkG)
    rw [e] at h1
    exact huniq _ _ _ h1 (hfo_spec g hg)
  have hsupp : ∀ g ∈ GfC (c.V (j + 1)), fo g ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, r ∈ GfC (c.V (j + 1)) ∧
      ∃ y ∈ grpAt (c.V (j + 1)) (· ∈ w.Q), ∃ k ∈ K₂, g = r * y * k := by
    intro g hg hne
    have hq : ∃ q₂, F g q₂ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hne
      have e : (fun g' : GfC (c.V (j + 1 + 1)) => F g g'.1) = 0 := funext fun g' => hcon g'.1
      have h0 := hfo_spec g hg
      rw [e] at h0
      exact huniq _ _ _ h0 IsQuotIntL1.zero
    obtain ⟨q₂, hq₂⟩ := hq
    obtain ⟨r, hr, hrG, y, hy, κ, hκ, k, hk, e⟩ := hB g hg q₂ hq₂
    exact ⟨r, hr, hrG, y, hy, κ * k, (hK₂ _).2 ⟨κ, hκ, k, hk, rfl⟩, e⟩
  have hint : IsQuotIntL1 ρ₁ μ₁ (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1)
      (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z) := by
    have e : (fun y : grpAt (c.V (j + 1)) (· ∈ w.Q) => fo y.1) =
        v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) • f₁' := funext fun y => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact huniq _ _ _ (hfo_spec y.1 (hQle₁ y.2)) (hinner y)
    rw [e]
    exact hf₁'.smul _
  have Hout := GlobalTheory.T.integral_quotient_eq_integral_factor_quotient (GA D (c.V (j + 1))) (GfC _) (grpAt _ (· ∈ w.Q)) (grpAt _ (· ∉ w.Q))
    (jacGrp (c.jac j (σ + 1) h).d) K₁ K₂ hfc₁ hQc₁ hQ'c₁ hJcl hQle₁ hQ'le₁ hcm₁ he₁ splitJ hK₁Q hK₂Q hK₁c hK₂c hK₁o hK₂o
    (c.ρJ j (σ + 1) h) (c.μf _) ρ₁ μ₁ (hc.ρJ _ _ _) (hc.μf _) hN₁.2.1 hN₁.1 invJ hμ₁K hρ₁K fo _ hleft hright hsupp hint
  have e1 : {g : GfC (c.V (j + 1)) | ∃ a ∈ K₁, ∃ b ∈ K₂, (g : GA D (c.V (j + 1))) = a * b} =
      {g | g.1 ∈ v.K (j + 1)} := Set.ext fun g => hKK g.1
  have e2 : {g : (jacGrp (c.jac j (σ + 1) h).d).subgroupOf (GfC (c.V (j + 1))) |
      ∃ a ∈ K₁, ∃ b ∈ K₂, ((g : GfC (c.V (j + 1))) : GA D (c.V (j + 1))) = a * b} =
      {g | g.1.1 ∈ v.K (j + 1)} := Set.ext fun g => hKK g.1.1
  rw [e1, e2] at Hout
  refine ⟨fun q => fo q.1, ?_, fun q => hfo_spec q.1 q.2⟩
  have ek : v.kap j σ h * z = v.vr (j + 1) _ (c.ρJ j (σ + 1) h) * (v.vr (j + 1 + 1) _ (c.ρB (j + 1 + 1) σ (idx_step h)) * z) := by
    unfold VCom.kap; ring
  rw [ek]
  exact Hout

end GlobalTheory.DStepCell

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawDoubleStep_finiteIntegral_collapse_twistPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) ρ₁ μ₁ ρ₂ μ₂, IsNormAt (c.V (j + 1)) (jacGrp (c.jac j (σ + 1) h).d) (v.N (j + 1)) (· ∈ w.Q) ρ₁ μ₁ → IsNormAt (c.V (j + 1 + 1)) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o) (v.N (j + 1 + 1)) (· ∈ w.Q) ρ₂ μ₂ → ∀ Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ z, Iter2 ρ₁ μ₁ ρ₂ μ₂ (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) z → Iter2 (c.ρJ j (σ + 1) h) (c.μf (j + 1)) (c.ρB (j + 1 + 1) σ (idx_step h)) (c.μf (j + 1 + 1)) (fun q₁ q₂ : _ => ∑ α, ∑ g ∈ (w.ε j α).support, w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ (Chain.hand (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (comb c.ψ _ _ (v.eG j) (comb c.ψ _ _ (w.eQ j) Ψ₁)) (comb c.ψ _ _ (v.eG (j + 1)) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)) (φ α) g q₁.1 q₂.1) (rTrans q₂.1 f)) (v.kap j σ h * z) := by
  first | exact @GlobalTheory.DStepCell.cell_collapse | exact GlobalTheory.DStepCell.cell_collapse | (intros; apply GlobalTheory.DStepCell.cell_collapse <;> assumption)
