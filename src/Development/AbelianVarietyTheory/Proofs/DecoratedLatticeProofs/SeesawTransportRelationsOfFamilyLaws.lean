module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTwistPlaceLevelSinglePlaceCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriods
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftReductionToFockVectorsUniform

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

variable {D : D7}

theorem sum_support_comb {Y Z G : Type*} [AddCommMonoid G] [Module ℂ G] (n : ℕ) (a : Fin n → Y →₀ ℂ)
    (b : Fin n → Y → Z →₀ ℂ) (R : Z → G) :
    ∑ z ∈ (∑ i, ∑ y ∈ (a i).support, a i y • b i y).support, (∑ i, ∑ y ∈ (a i).support, a i y • b i y) z • R z =
      ∑ i, ∑ y ∈ (a i).support, a i y • ∑ z ∈ (b i y).support, b i y z • R z := by
  change Finsupp.sum _ (fun z r => r • R z) = _
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finsupp.sum_finsetSum_index (by simp) (by intros; exact add_smul _ _ _)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.sum_smul_index' (by simp)]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem twoX_of_laws : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), BiAct D → CenFock D → LiftSum D → c.Is →
    (∀ s, (t s).Is) → RealEq t → KerX t → RdX t → TwoX t := by
  intro D c 𝒯 t hBi hCen hLS hc ht hreal hker hrd
  intro j hj C hC y
  have hj0 : j < D.R.m := by omega
  have hj1 : j + 1 < D.R.m := by omega
  obtain ⟨χ, hχ⟩ := hrd j (by omega)
  have step1 : ∃ (n : ℕ) (P : Fin n → PolF D (c.X (j + 1)).rank (c.X j).rank)
      (P' : Fin n → PolF D (c.X (j + 1 + 1)).rank (c.X (j + 1)).rank), ∀ s, ∀ ψ ∈ (t s).Ram j, ∀ β,
        (t s).two j (fun α => (t s).rd j α ψ y) C β = ∑ i, ∑ γ,
          ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
    by_cases hex : ∃ (s : 𝒯) (_ : (t s).Ch j) (γ : (t s).Ch (j + 1)) (_ : (t s).Ch (j + 1 + 1)), True
    · obtain ⟨s₀, α₀, γ₀, β₀, -⟩ := hex
      obtain ⟨n, P, P', hF⟩ := GlobalTheory.T.doubleLift_reduction_to_fockVectors_uniform D hBi hCen hLS c.ψ c.θ hc.inf (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))
        (c.x j) (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x j (by omega)) (hc.x (j + 1) (by omega)) (hc.x (j + 1 + 1) (by omega))
        ((t s₀).ker j α₀ γ₀) ((t s₀).ker (j + 1) γ₀ β₀) ((ht s₀).ker j hj0 α₀ γ₀) ((ht s₀).ker (j + 1) hj1 γ₀ β₀) χ C hC.1 hC.2
      refine ⟨n, P, P', fun s ψ hψ β => ?_⟩
      have hrdψ := fun α => hχ s ψ hψ α y
      have e1 : ∀ α γ, biLift ((t s).kom j) ((t s).kom (j + 1)) (c.x j).vol (c.x (j + 1)).vol ((t s).rd j α ψ y)
          (biComb c.ψ _ _ _ ((t s).dd j α γ) ((t s).dd (j + 1) γ β) C) =
          ∑ i, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := fun α γ =>
        hF ((t s).ker j α γ) ((t s).ker (j + 1) γ β) ((ht s).ker j hj0 α γ) ((ht s).ker (j + 1) hj1 γ β) rfl rfl
          (fun a ha b hb f hf => hreal j hj0 s s₀ a ha b hb f hf)
          (fun a ha b hb f hf => hreal (j + 1) hj1 s s₀ a ha b hb f hf) _ (hrdψ α).1 (hrdψ α).2
      have e2 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
          ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) := by
        intro i γ
        have h := (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
          ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 ((t s).Ch j) Finset.univ (fun _ => 1)
          (fun α => ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y))
          (fun α _ => (hLS c.ψ c.θ hc.inf _ _ (c.x j) (c.x (j + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
            ((ht s).ker j hj0 α γ) (P i)).2.1 _ (hrdψ α).1)
        simpa using h
      simp only [Tup.two, e1, e2]
      rw [Finset.sum_comm]
      calc _ = ∑ γ, ∑ i, ∑ α, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
            (((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) :=
            Finset.sum_congr rfl fun γ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    · push Not at hex
      refine ⟨0, Fin.elim0, Fin.elim0, fun s ψ _ β => ?_⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun γ _ => ?_
      exact ((hex s α γ β).elim)
  obtain ⟨n, P, P', hstep⟩ := step1
  choose a ha using fun i : Fin n => hker j hj0 y (P i)
  choose b hb using fun (i : Fin n) (y' : c.Fr (j + 1)) => hker (j + 1) hj1 y' (P' i)
  obtain ⟨χ', hχ'⟩ := hrd (j + 1) (by omega)
  refine ⟨∑ i, ∑ y' ∈ (a i).support, a i y' • b i y', fun s ψ hψ β => ?_⟩
  rw [hstep s ψ hψ β, sum_support_comb]
  have hKψ := (ht s).stabK j hj0 ψ hψ
  have e3 : ∀ i γ, ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1)) (P' i)
        (∑ α, ((t s).ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P i) ((t s).rd j α ψ y)) =
      ∑ y' ∈ (a i).support, ((t s).cK j * a i y') • ((t s).ker (j + 1) γ β).lift c.ψ c.θ (c.x (j + 1)) (c.x (j + 1 + 1))
        (P' i) ((t s).rd (j + 1) γ ((t s).K j ψ) y') := by
    intro i γ
    rw [ha i s ψ hψ γ, Finset.smul_sum]
    simp only [smul_smul]
    exact (hLS c.ψ c.θ hc.inf _ _ (c.x (j + 1)) (c.x (j + 1 + 1)) (hc.x _ (by omega)) (hc.x _ (by omega)) _
      ((ht s).ker (j + 1) hj1 γ β) (P' i)).2.2 _ _ _ _ (fun y' _ => (hχ' s _ hKψ γ y').1)
  simp only [e3]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [← Finset.smul_sum, hb i y' s _ hKψ β, smul_smul, smul_smul]
  congr 1
  ring

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleLiftCombinationOfLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawDoubleLiftCombination_of_laws : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), BiAct D → CenFock D → LiftSum D → c.Is → (∀ s, (t s).Is) → RealEq t → KerX t → RdX t → TwoX t := by
  first | exact @GlobalTheory.SeeSaw.twoX_of_laws | exact GlobalTheory.SeeSaw.twoX_of_laws | (intros; apply GlobalTheory.SeeSaw.twoX_of_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsTransportLinearRelations
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsTransportLinearRelations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LastStepsX

variable {D : D7}

theorem liftS_smul {S T : HSp D} (om : Om S T) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (a : ℂ)
    (G : GA D T → ℂ) (f : WO S T → ℂ) : liftS om ν 𝓕 (a • G) f = a • liftS om ν 𝓕 G f := by
  funext g
  simp only [liftS, Lift.liftInt, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext x; ring

theorem trc_smul {V : HSp D} (e : GA D V →₀ ℂ) (a : ℂ) (f : GA D V → ℂ) : trc e (a • f) = a • trc e f := by
  funext x
  simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

theorem perF_smul {c : Comm D} (t : Tup c) (j ρ : ℕ) (h : j + 2 * ρ + 2 = D.R.m) (φ : t.Ch j → GA D (c.X j) → ℂ)
    (a : ℂ) (f : GA D (c.V j) → ℂ) : t.perF j ρ h φ (a • f) = a * t.perF j ρ h φ f := by
  simp only [Tup.perF, trc_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have e := GlobalTheory.HandHom.per_smul (c.B j ρ h) c.ψ 1 a (φ α) (trc (t.e j α) f)
  rw [one_smul, one_mul] at e
  exact e

theorem contAut_trc {V : HSp D} (e : GA D V →₀ ℂ) {f : GA D V → ℂ} (hf : IsContAut V f) : IsContAut V (trc e f) := by
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hf.1 γ hγ]
  · have e : trc e f = fun x => ∑ g ∈ e.support, e g * f (x * g) := by
      funext x
      simp only [trc, rTrans, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact continuous_finsetSum _ fun g _ => continuous_const.mul (hf.2.comp (continuous_mul_const g))

theorem contAut_emb {S A B : HSp D} (o : OrthDec S A B) {f : GA D S → ℂ} (hf : IsContAut S f) :
    Continuous (fun h : GA D A => f (o.emb (h, 1))) ∧ ∀ γ ∈ GQ A, ∀ g, f (o.emb (γ * g, 1)) = f (o.emb (g, 1)) := by
  refine ⟨hf.2.comp (o.continuous_emb.comp (continuous_id.prodMk continuous_const)), fun γ hγ g => ?_⟩
  have e : o.emb (γ * g, 1) = o.emb (γ, 1) * o.emb (g, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  rw [e, hf.1 _ (o.emb_mem_GQ hγ (one_mem _))]

theorem integrableOn_contAut {V : HSp D} (hV : CoCpt V) (vol : Vol V) {f : GA D V → ℂ} (hc : Continuous f)
    (hi : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) : IntegrableOn f vol.𝓕 vol.μ :=
  (GlobalTheory.CocompactParam.continuous_integral_param D V hV vol Unit (fun g _ => f g) (hc.comp continuous_fst)
    (fun γ hγ g _ => hi γ hγ g)).1 ()

theorem io_ioT {c : Comm D} (t : Tup c) (ht : t.Is) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) (F : t.CT)
    (P₁ : PolF D (c.V (j + 1)).rank (c.V j).rank) (P₂ : PolF D c.T.rank (c.V (j + 1)).rank) (v : SmT c.MT) :
    (t.cI j * t.cI (j + 1)) • ((t.io j (t.ioT j h F)).1 (c.It j P₁ (c.ItT j h P₂ v))) =
      liftS (t.om j) (c.vol (j + 1)).μ (c.vol (j + 1)).𝓕
        (liftS (t.omT j h) c.volT.μ c.volT.𝓕 (F.1 v) (t.ptT j h P₂)) (t.pt j P₁) := by
  rw [ht.ioT j h F P₂ v, liftS_smul, ht.io j (by omega) (t.ioT j h F) P₁ (c.ItT j h P₂ v), smul_smul, mul_comm]

theorem perT_comb {c : Comm D} (t : Tup c) (n : ℕ) (h : n = D.R.m) {Y : Type} (S : Finset Y) (k : ℂ) (a : Y → ℂ)
    (φ : Y → t.Ch n → GA D (c.X n) → ℂ) (f : GA D c.T → ℂ)
    (hi : ∀ y' β, IntegrableOn (fun h' => trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) c.volT.𝓕 c.volT.μ) :
    t.perT n h (fun β => k • ∑ y' ∈ S, a y' • φ y' β) f = k * ∑ y' ∈ S, a y' * t.perT n h (φ y') f := by
  have e1 : ∀ β, ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1)) ∂c.volT.μ
      = ∑ y' ∈ S, k * a y' * ∫ h' in c.volT.𝓕, trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1)) ∂c.volT.μ := by
    intro β
    have e2 : (fun h' => trc (t.eT n h β) f h' * (k • ∑ y' ∈ S, a y' • φ y' β) ((c.oT n h).emb (h', 1))) =
        fun h' => ∑ y' ∈ S, (k * a y') * (trc (t.eT n h β) f h' * φ y' β ((c.oT n h).emb (h', 1))) := by
      funext h'
      simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y' _ => by ring
    rw [e2, integral_finsetSum _ (fun y' _ => (hi y' β).const_mul _)]
    simp_rw [integral_const_mul]
  simp only [Tup.perT, e1, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun β _ => by ring

end GlobalTheory.SeeSaw.LastStepsX


set_option maxHeartbeats 4000000 in
open GlobalTheory.SeeSaw.LastStepsX in
theorem GlobalTheory.SeeSaw.lastX_of_laws : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), RapidVal D → c.Is → (∀ s, (t s).Is) → ValLastX t → TwoX t → PerX t → RdX t → LastX t := by
  intro hHC D c 𝒯 t hRV hc ht hVL hTX hPX hRD
  intro j h I _ s α ψ F hψ hF y v
  obtain ⟨χ, hχ⟩ := hRD j (by omega)
  obtain ⟨χ₂, hχ₂⟩ := hRD (j + 1 + 1) (by omega)
  refine GlobalTheory.T.period_linear_relation_density_of_unfolding_steps hHC D c 𝒯 t hc j 0 h I s (fun i => α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)))
    (fun i β => (t (s i)).rd j β (ψ i) y) (fun i => (t (s i)).io j ((t (s i)).ioT j h (F i))) ht
    (fun i β => (hχ (s i) (ψ i) (hψ i) β y).1) c.T c.T c.parT c.MT (c.ItT j h) (hc.spanT j h) ?_ v
  intro P₁ P₂ w
  obtain ⟨C, hCr, hC⟩ := hVL j h P₁ P₂
  obtain ⟨a, ha⟩ := hTX j (by omega) C hCr y
  choose b hb using fun y' => hPX (j + 1 + 1) h y' w
  have hterm : ∀ i, α i * ((t (s i)).cI j * (t (s i)).cI (j + 1)) * (t (s i)).perF j 0 h (fun β => (t (s i)).rd j β (ψ i) y)
      (((t (s i)).io j ((t (s i)).ioT j h (F i))).1 (c.It j P₁ (c.ItT j h P₂ w))) =
      ∑ y' ∈ a.support, a y' * b y' * (α i * ((t (s i)).cV j * (t (s i)).cK j * (t (s i)).cK (j + 1) * (t (s i)).cP) *
        (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i)) := by
    intro i
    have hSψ : (t (s i)).S j (ψ i) ∈ (t (s i)).Ram j := (ht (s i)).stabS j (by omega) _ (hψ i)
    have hψ₁ := (ht (s i)).stabK j (by omega) _ hSψ
    have hψ₂ := (ht (s i)).stabK (j + 1) (by omega) _ hψ₁
    rw [mul_assoc, ← perF_smul, io_ioT (t (s i)) (ht (s i)) j h (F i) P₁ P₂ w, hC (s i) (ψ i) (hψ i) y (F i) w]
    have e2 : (t (s i)).two j (fun β => (t (s i)).rd j β ((t (s i)).S j (ψ i)) y) C = fun β =>
        ((t (s i)).cK j * (t (s i)).cK (j + 1)) • ∑ y' ∈ a.support, a y' •
          (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y' :=
      funext fun β => ha (s i) _ hSψ β
    have hE : RapidDec c.T ((F i).1 w) := by
      obtain ⟨J, χ', hle⟩ := (ht (s i)).CT
      exact hRV c.θ hc.inf c.T c.parT c.MT J χ' _ (hle (F i).2) w
    have e3 := perT_comb (t (s i)) (j + 1 + 1) h a.support ((t (s i)).cK j * (t (s i)).cK (j + 1)) a
      (fun y' β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w)
      (fun y' β => by
        have ht' := contAut_trc ((t (s i)).eT (j + 1 + 1) h β) ⟨hE.1, hE.2.1⟩
        obtain ⟨hcont, hinv⟩ := contAut_emb (c.oT (j + 1 + 1) h) (hχ₂ (s i) _ hψ₂ β y').1
        exact integrableOn_contAut hc.cpt c.volT (ht'.2.mul hcont) (fun γ hγ g => by rw [ht'.1 γ hγ g, hinv γ hγ g]))
    beta_reduce at e3
    have hb' : ∀ y', (t (s i)).perT (j + 1 + 1) h
        (fun β => (t (s i)).rd (j + 1 + 1) β ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) y') ((F i).1 w) =
        (t (s i)).cP * b y' * (t (s i)).tail (j + 1 + 1) h ((t (s i)).K (j + 1) ((t (s i)).K j ((t (s i)).S j (ψ i)))) (F i) :=
      fun y' => hb y' (s i) _ hψ₂ (F i)
    rw [e2, e3]
    simp only [hb', Finset.mul_sum]
    exact Finset.sum_congr rfl fun y' _ => by ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_comm]
  refine Finset.sum_eq_zero fun y' _ => ?_
  rw [← Finset.mul_sum, hF, mul_zero]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsTransportLinearRelationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_lastTwoSteps_transport_linear_relations : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), RapidVal D → c.Is → (∀ s, (t s).Is) → ValLastX t → TwoX t → PerX t → RdX t → LastX t := by
  first | exact @GlobalTheory.SeeSaw.lastX_of_laws | exact GlobalTheory.SeeSaw.lastX_of_laws | (intros; apply GlobalTheory.SeeSaw.lastX_of_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MainXOfStepXLastX
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.DoubleInd

variable {D : D7} {c : Comm D}

def W (t : Tup c) (k : ℕ) : ℂ :=
  ∏ l ∈ Finset.range k, t.cV (2 * l) * t.cK (2 * l) * t.cK (2 * l + 1)

theorem up_succ (t : Tup c) (k : ℕ) (ψ : t.Col 0) :
    t.up (k + 1) ψ = t.K (2 * k + 1) (t.K (2 * k) (t.S (2 * k) (t.up k ψ))) := rfl

theorem up_mem (t : Tup c) (ht : t.Is) (ψ : t.Col 0) (hψ : ψ ∈ t.Ram 0) :
    ∀ k, 2 * k ≤ D.R.m → t.up k ψ ∈ t.Ram (2 * k) := by
  intro k
  induction k with
  | zero => intro _; exact hψ
  | succ k ih =>
    intro hk
    rw [up_succ]
    have h0 := ih (by omega)
    have h1 := ht.stabS (2 * k) (by omega) _ h0
    have h2 := ht.stabK (2 * k) (by omega) _ h1
    exact ht.stabK (2 * k + 1) (by omega) _ h2

theorem up_ind {𝒯 : Type} (t : 𝒯 → Tup c) (ht : ∀ s, (t s).Is) (hS : StepX t) :
    ∀ k ρ (h : 2 * k + 2 * ρ + 2 = D.R.m) (I : Type) [Fintype I] (s : I → 𝒯) (β : I → ℂ) (ψ : ∀ i, (t (s i)).Col 0)
      (G : ∀ i, (t (s i)).CC (2 * k)), (∀ i, ψ i ∈ (t (s i)).Ram 0) →
      (∀ y v, ∑ i, β i * W (t (s i)) k * (t (s i)).per (2 * k) ρ h ((t (s i)).up k (ψ i)) (G i) y v = 0) →
      ∀ ρ₀ (h₀ : 0 + 2 * ρ₀ + 2 = D.R.m) y v,
        ∑ i, β i * (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) *
          (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * k) (G i)) y v = 0 := by
  intro k
  induction k with
  | zero =>
    intro ρ h I _ s β ψ G hψ hyp ρ₀ h₀ y v
    have hρ : ρ₀ = ρ := by omega
    subst hρ
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
    rw [show (∏ j ∈ Finset.range (2 * 0), (t (s i)).cI j) = (1 : ℂ) by simp,
      show W (t (s i)) 0 = 1 by simp [W]]
    rfl
  | succ k ih =>
    intro ρ h I _ s β ψ G hψ hyp ρ₀ h₀ y v
    have h' : 2 * k + 2 * (ρ + 1) + 2 = D.R.m := by omega
    have hmem : ∀ i, (t (s i)).up k (ψ i) ∈ (t (s i)).Ram (2 * k) :=
      fun i => up_mem _ (ht _) _ (hψ i) k (by omega)
    have hst := hS (2 * k) ρ h' I s (fun i => β i * W (t (s i)) k) (fun i => (t (s i)).up k (ψ i)) G hmem (by
      intro y v
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hyp y v)
      have hp : (t (s i)).per (2 * k + 1 + 1) ρ (idx_step h')
          ((t (s i)).K (2 * k + 1) ((t (s i)).K (2 * k) ((t (s i)).S (2 * k) ((t (s i)).up k (ψ i))))) (G i) y v =
          (t (s i)).per (2 * (k + 1)) ρ h ((t (s i)).up (k + 1) (ψ i)) (G i) y v := rfl
      rw [hp]
      simp only [W, Finset.prod_range_succ]
      ring)
    have hi := ih (ρ + 1) h' I s (fun i => β i * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1))) ψ
      (fun i => (t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i))) hψ (by
        intro y v
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hst y v)
        ring) ρ₀ h₀ y v
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hi
    have hp : ∏ j ∈ Finset.range (2 * (k + 1)), (t (s i)).cI j =
        (∏ j ∈ Finset.range (2 * k), (t (s i)).cI j) * ((t (s i)).cI (2 * k) * (t (s i)).cI (2 * k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, Finset.prod_range_succ, Finset.prod_range_succ]
      ring
    have hd : (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * (k + 1)) (G i)) y v =
        (t (s i)).per 0 ρ₀ h₀ (ψ i) ((t (s i)).dn (2 * k) ((t (s i)).io (2 * k) ((t (s i)).io (2 * k + 1) (G i)))) y v := rfl
    rw [hp, hd]
    ring

end GlobalTheory.SeeSaw.DoubleInd

namespace GlobalTheory.SeeSaw


open GlobalTheory.SeeSaw.DoubleInd in
theorem mainX_of_stepX_lastX : ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), (∀ s, (t s).Is) → StepX t → LastX t → MainX t := by
  intro D c 𝒯 t ht hS hL
  intro n h h₀ I _ s α ψ F hψ hyp y v
  have hmem : ∀ i, (t (s i)).up n (ψ i) ∈ (t (s i)).Ram (2 * n) :=
    fun i => up_mem _ (ht _) _ (hψ i) n (by omega)
  have hL' := hL (2 * n) h I s (fun i => α i * W (t (s i)) n) (fun i => (t (s i)).up n (ψ i)) F hmem (by
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hyp
    have hp : (t (s i)).tail (2 * n + 1 + 1) h
        ((t (s i)).K (2 * n + 1) ((t (s i)).K (2 * n) ((t (s i)).S (2 * n) ((t (s i)).up n (ψ i))))) (F i) =
        (t (s i)).tail (2 * (n + 1)) h ((t (s i)).up (n + 1) (ψ i)) (F i) := rfl
    rw [hp]
    simp only [Tup.cTop, W, Finset.prod_range_succ]
    ring)
  have hu := up_ind t ht hS n 0 h I s (fun i => α i * ((t (s i)).cI (2 * n) * (t (s i)).cI (2 * n + 1))) ψ
    (fun i => (t (s i)).io (2 * n) ((t (s i)).ioT (2 * n) h (F i))) hψ (by
      intro y v
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (hL' y v)
      ring) n h₀ y v
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hu
  have hc : (t (s i)).cBot =
      (∏ j ∈ Finset.range (2 * n), (t (s i)).cI j) * ((t (s i)).cI (2 * n) * (t (s i)).cI (2 * n + 1)) := by
    unfold Tup.cBot
    rw [show D.R.m = 2 * n + 1 + 1 by omega, Finset.prod_range_succ, Finset.prod_range_succ]
    ring
  have hd : (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n + 1) ((t (s i)).ioT (2 * n) h (F i))) y v =
      (t (s i)).per 0 n h₀ (ψ i) ((t (s i)).dn (2 * n) ((t (s i)).io (2 * n) ((t (s i)).ioT (2 * n) h (F i)))) y v := rfl
  rw [hc, hd]
  ring

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem mainX_of_lawsX (hR : GlobalTheory.Published.CuspRapidDecay) (hH : GlobalTheory.Published.HarishChandraModules) :
    ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  intro D c 𝒯 t L
  have hTwo : TwoX t :=
    GlobalTheory.T.seeSawDoubleLiftCombination_of_laws D c 𝒯 t (GlobalTheory.T.seeSawWeilBiAction_commutes D) (GlobalTheory.T.centralEigenTheta_isFockVector_bounded_degree D) (GlobalTheory.SeeSaw.LiftSumProof.liftSum D)
      L.com L.tup L.real L.ker L.rd
  have hRap : RapidVal D := GlobalTheory.SeeSaw.rapidVal_of_cuspRapidDecay hR D
  have hStep : StepX t :=
    GlobalTheory.T.seeSaw_doubleStep_linearRelations_periods hH D c 𝒯 t (GlobalTheory.T.besselPeriod_double_step_unfolding_of_descent D (GlobalTheory.Desc.weil_data_descend D)) hRap
      (GlobalTheory.ValMoveProof.valMove D) (GlobalTheory.SeeSaw.perSum_all D) L.com L.tup L.loc L.val hTwo L.rd
  have hLast : LastX t :=
    GlobalTheory.T.seeSaw_lastTwoSteps_transport_linear_relations hH D c 𝒯 t hRap L.com L.tup L.last hTwo L.per L.rd
  exact GlobalTheory.SeeSaw.mainX_of_stepX_lastX D c 𝒯 t L.tup hStep hLast

end GlobalTheory.SeeSaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawTransportRelationsOfFamilyLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesawTransportRelations_of_familyLaws : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (c : Comm D) (𝒯 : Type) (t : 𝒯 → Tup c), LawsX t → MainX t := by
  first | exact @GlobalTheory.SeeSaw.mainX_of_lawsX | exact GlobalTheory.SeeSaw.mainX_of_lawsX | (intros; apply GlobalTheory.SeeSaw.mainX_of_lawsX <;> assumption)
end
