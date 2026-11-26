module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftLowerBoundOffBasePlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAdjointEigenvalueLowerBoundBaseEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookPlusLeMainTerm
noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopBound

theorem idem_apply {G H : Type} [Group G] [Fintype G] [AddCommGroup H] [Module ℂ H] (ρ : Representation ℂ G H) {a : G → ℂ}
    (ha : GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents.IsCentralIdem a) (u : H) :
    (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = (∑ g, a g • ρ g : H →ₗ[ℂ] H) u := by
  have h1 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) u = ∑ g, ∑ h, (a h * a (h⁻¹ * g)) • ρ g u := by
    simp only [← Finset.sum_smul, ha.2, LinearMap.sum_apply, LinearMap.smul_apply]
  have h2 : (∑ g, a g • ρ g : H →ₗ[ℂ] H) ((∑ g, a g • ρ g : H →ₗ[ℂ] H) u) = ∑ h, ∑ g, (a h * a g) • ρ h (ρ g u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  rw [h2, h1, Finset.sum_comm (f := fun g h => (a h * a (h⁻¹ * g)) • ρ g u)]
  refine Finset.sum_congr rfl fun h _ => Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, Module.End.mul_apply]

theorem le_eigenvalue {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T S : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (m l : ℝ)
    (hS : ∀ y, S y = e (T y)) (hee : ∀ y, e (e y) = e y) (hadj : ∀ x, e x = x → ∀ y, ⟪x, e y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hm : ∀ u, m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2) (x : Y) (hx : x ≠ 0) (hl : 0 < l)
    (h : S (LinearMap.adjoint S x) = (l : ℂ) • x) : m ≤ l := by
  have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hex : e x = x := by
    refine smul_right_injective Y hl' ?_
    show (l : ℂ) • e x = (l : ℂ) • x
    rw [← map_smul, ← h, hS, hee]
  have h1 : LinearMap.adjoint S x = LinearMap.adjoint T x := ext_inner_right ℂ fun f => by
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, hS, hadj x hex]
  have h2 : ‖LinearMap.adjoint T x‖ ^ 2 = l * ‖x‖ ^ 2 := by
    have h3 : ⟪LinearMap.adjoint S x, LinearMap.adjoint S x⟫_ℂ = (l : ℂ) * ⟪x, x⟫_ℂ := by
      rw [LinearMap.adjoint_inner_left, h, inner_smul_right]
    rw [h1, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ((‖LinearMap.adjoint T x‖ ^ 2 : ℝ) : ℂ) = ((l * ‖x‖ ^ 2 : ℝ) : ℂ) := by
      push_cast; exact h3
    exact_mod_cast h4
  have h5 := hm x
  rw [h2] at h5
  exact le_of_mul_le_mul_right h5 (by positivity)

theorem scalar_of_ne_bot {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (T : X →ₗ[ℂ] Y) (U U' : Y →ₗ[ℂ] X)
    (hU : U' = U) (P P' : Submodule ℂ Y) (hP : P' = P) (m m' : ℝ) (hm : m ≤ m')
    (h : P' ≠ ⊥ → ∃ l : ℝ, 0 < l ∧ (∀ x ∈ P', T (U' x) = (l : ℂ) • x) ∧ m' ≤ Real.log l) :
    ∃ l : ℝ, Real.exp m ≤ l ∧ ∀ y ∈ P, T (U y) = (l : ℂ) • y := by
  subst hU hP
  by_cases hc : P' = ⊥
  · refine ⟨_, le_rfl, fun y hy => ?_⟩
    have h0 : y = 0 := (Submodule.eq_bot_iff _).1 hc y hy
    rw [h0, map_zero, map_zero, smul_zero]
  · obtain ⟨l, hl, h1, h2⟩ := h hc
    exact ⟨l, (Real.le_log_iff_exp_le hl).1 (hm.trans h2), h1⟩

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)


include R in
theorem hookPlus_le_mainTerm (i : Fin D.R.m) : GlobalTheory.LiftLower.hookPlus D i ≤ GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm D i (sg0 D A) := by
  have hl : ∀ ρ, lab (sg0 D A) ρ = ρ := fun ρ => by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base ρ
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.mainTerm GlobalTheory.LiftLower.hookPlus GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.aPlAt
  simp only [hl]
  have hp : ∀ n a, (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a : ℝ) := fun n a => by
    have : 0 < GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf n a := GlobalTheory.Survey.LevelVectorSizeBounds.hookProd_pos _
    exact_mod_cast this
  refine Finset.sum_le_sum fun ρ _ => Real.log_le_log (lt_of_lt_of_le one_pos (hp _ _)) ?_
  exact le_mul_of_one_le_right (zero_le_one.trans (hp _ _)) (hp _ _)

end GlobalTheory.LowTopBound

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAdjointEigenvalueLowerBoundBaseEmbedding
noncomputable section

open NumberField IsDedekindDomain Module MeasureTheory
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.IndefR.Mult
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.Survey.LevelVectorSizeBounds
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LowTopCore

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem g_mem_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) {PP : Pl D.host.E} (hP : PP ∈ R.Pg) :
    ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  obtain ⟨k, hk⟩ := (h.lev.Pg PP).1 hP
  refine ⟨k, ?_⟩
  have h1 := R.C.P.pb_over k
  rw [← hk] at h1
  have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (D.host.g k : ℕ) ∈ PP.asIdeal := h1
  simpa using h2


open Classical in
theorem isConjChars_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    IsConjChars R i t (RingEquiv.refl ℂ) (R.toLevCh.mu t ((i : ℕ) + 1)) R.eta
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) := by
  refine ⟨_, _, isGalConj_refl _ _, isGalConj_refl _ _, ⟨(h.thP.ωP i t).hecS, ?_⟩, h.lev.eta, ?_⟩
  · intro P e he k x hx
    have a := (h.lev.mu0 i).2 P e he k x hx
    have b := (h.lev.xi t).2 P e he k x hx
    show (((R.mu0 ((i : ℕ) + 1) x * R.xi t x : Circle)) : ℂ) = (((R.C.mu0 i).locK P k * (R.xiH t).locK P k : ℂˣ) : ℂ)
    rw [Circle.coe_mul, a, b, Units.val_mul]
  · intro PP hPP a k u hk hu
    have ha : a ∉ PP.asIdeal := fun ha => u.ne_zero (hu.trans (Ideal.Quotient.eq_zero_iff_mem.2 ha))
    show _ = (R.C.mu0 i).locK PP k * (R.xiH t).locK PP k
    by_cases hg : PP ∈ R.Pg
    · obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
      have hun : (R.xiH t).UnrAt PP := by
        by_contra hn
        rcases (h.lev.Q_ram t PP).1 hn with hq | ⟨PP', hq, hc⟩
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
        · obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP' hq
          obtain ⟨c', hc1, hc2⟩ := hc _ (q_mem hq2)
          have : c' = (q : 𝓞 D.host.E) := by
            apply NumberField.RingOfIntegers.coe_injective
            rw [map_natCast]
            have h3 : (c' : D.host.E) = (q : D.host.E) := by simpa using hc2
            exact h3
          exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (this ▸ hc1)
      simp only [if_pos hg]
      rw [locK_eq_one hun a k hk ha, mul_one]
      exact h.lev.chi i PP hg a k u hk hu
    · have hq : PP ∈ R.Q t := hPP.resolve_left hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hq
      have hun : (R.C.mu0 i).UnrAt PP := (R.C.isMu0 i).unr PP fun l hl =>
        not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hg]
      rw [locK_eq_one hun a k hk ha, one_mul]
      exact h.lev.xiR t PP hq a k u hk hu


open Classical in
theorem isLevelVec_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i R.triv) (R.Q t)
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.vacP i) (R.vP i t) := by
  have h1 := h.thP.vP i t
  unfold Datum.IsThPVecOf at h1
  unfold IsLevelVec
  have hQ : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      Datum.omegaQ (R.Q t) (Wc D i).rank (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (-1) y =
        Datum.omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y := by
    intro y
    unfold Datum.omegaQ
    split_ifs with hy
    · refine Finset.prod_congr rfl fun PP _ => ?_
      have hn : PP.1 ∉ R.Pg := fun hg => by
        obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
        obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP.1 PP.2
        exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
      simp only [if_neg hn]
    · rfl
  simp only [omegaG_triv, hQ]
  exact h1


open Classical in
theorem chr_base_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    chrOf (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) R.triv
      (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP)) = (levEnv _ (R.βV i) (R.datVt i t)).χ := by
  ext1 x
  refine levFn_congr (R.βV i) D.R.r (r_le_V i) D.R.t 1 R.Pg (R.Q t) R.triv
    (fun _ PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (fun _ PP => (R.chi ((i : ℕ) + 1) PP)⁻¹)
    (fun PP => if PP ∈ R.Pg then (R.chi ((i : ℕ) + 1) PP)⁻¹ else R.xiR t PP) (R.xiR t) ?_ ?_ _
  · intro c PP hP
    simp only [if_pos hP]
  · intro PP hP
    have hn : PP ∉ R.Pg := fun hg => by
      obtain ⟨l, hl⟩ := g_mem_ofCore R h hg
      obtain ⟨⟨q, hq1, hq2, -, hq4⟩, -⟩ := h.lev.Q_pl t PP hP
      exact not_both (D.host.g_prime l) hq1 (hq4 l) hl (q_mem hq2)
    simp only [if_neg hn]

theorem exists_lift_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) :
    ∃ th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H, ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x :=
  GlobalTheory.BaseScalar.exists_factor (R.HW i (sg0 D A)).e (R.thF i t) (R.Wall i (sg0 D A)) (h.models.HW i (sg0 D A)).1
    (h.models.HW i (sg0 D A)).2.1 (h.thP.thF_mem i t)

theorem isLift_of_ofCore {F : Face D A} (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x) :
    IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th := by
  refine (h.thP.thF i t).elim fun thP hP => ?_
  unfold IsLift
  intro x v g
  have a := GlobalTheory.BaseScalar.integrableOn_of_isThetaLift hP.1 x (PiTensorProduct.tprod ℂ v) g
  have c := (congrFun (hP.2 x v) g).trans a.2
  refine ⟨a.1, ?_⟩
  rw [hth x]
  exact c

theorem scalar_of_lift_ofCore {F : Face D A} (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (b : ℝ)
    (hb : Sizes D i b) (t : T0) (ht : PrimeToHost R t)
    (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H)
    (hth : IsLift R i (sg0 D A) (R.ωP i t) (R.ptP i t) (R.cV i) (R.ioP i) (R.νV i t) (R.fdV i t) (R.HV i t) th)
    (ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) (hev : typePart R i (sg0 D A) t R.triv ev ≠ ⊥) :
    ∃ l : ℝ, 0 < l ∧ (∀ x ∈ typePart R i (sg0 D A) t R.triv ev, th (adjLev R.triv th x) = (l : ℂ) • x) ∧
      mainTerm D i (sg0 D A) - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b ≤ Real.log l := by
  have hσ : IsEmbOverK D (sg0 D A) (RingEquiv.refl ℂ) := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]; exact isEmbOverK_base
  have key := hA h i b hb t ht _ _ hσ R.triv (isLocal_triv R) _ _ _ (isConjChars_base_ofCore R h i t) (R.ωP i t) (h.thP.ωP i t)
    (onb (R.MW i (sg0 D A))) (fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.isONBasis_onb _ ρ _ (h.models.order i ρ)) _ _ (isLevelVec_base_ofCore R h i t)
    (h.thP.pt_theta i t) (R.cV i) (h.models.cV i) (R.ioP i) (by rw [delta_base R]; exact h.thP.ioP i t)
    (R.νV i t) (R.fdV i t) (h.models.νV i t) _ (R.B.L i t).pres.y (R.B.L i t).pres.reps (R.HV i t)
    (by rw [chr_base_ofCore R h]; exact h.models.HV i t)
  exact key.2 th hth ev hev

theorem scalar_on_part_ofCore {F : Face D A} (hA : GlobalTheory.LowRow.AdelC R F) (h : GlobalTheory.Hk3.Core R F)
    (hp : PrimeToHost R A.μ0) (i : Fin D.R.m) (b : ℝ) (hb : Sizes D i b)
    (th : (R.HV i A.μ0).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) (hth : ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i A.μ0 x)
    (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    ∃ l : ℝ, Real.exp (lowB D i b) ≤ l ∧
      ∀ y ∈ GlobalTheory.LiftLower.partH R i (sg0 D A) c, th (LinearMap.adjoint th y) = (l : ℂ) • y := by
  have e := GlobalTheory.LiftLower.typePart_base h.lev i (sg0 D A) c
  have h1 := scalar_of_lift_ofCore R hA h i b hb A.μ0 hp th (isLift_of_ofCore R h i A.μ0 th hth) c
  have h2 := GlobalTheory.BaseScalar.adjLev_triv R th
  have h3 : lowB D i b ≤ mainTerm D i (sg0 D A) -
      8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * Lp D b := sub_le_sub_right (GlobalTheory.LowTopBound.hookPlus_le_mainTerm R i) _
  exact GlobalTheory.LowTopBound.scalar_of_ne_bot th _ _ h2 _ _ e _ _ h3 h1

theorem lowTop_ofCore : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ),
    GlobalTheory.LowRow.AdelC R F → GlobalTheory.Hk3.Core R F → A.fam.Ok s → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowTop R b := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F s b hA h _ hp hb i l x hx hl hxl
  obtain ⟨th, hth⟩ := exists_lift_ofCore R h i A.μ0
  have hinj : Function.Injective (R.HW i (sg0 D A)).e := (h.models.HW i (sg0 D A)).1
  have hS : ∀ y, R.thG i A.μ0 y = GlobalTheory.LiftLower.projH R i (sg0 D A) (th y) := fun y => by
    have a1 := h.thP.thG i A.μ0 y
    have a2 := GlobalTheory.LiftLower.e_projH h.models.gW i (sg0 D A) (th y)
    have a3 := congrArg (Formalism.IndefR.Mult.postOn (R.MW i (sg0 D A)) (R.eWf i (sg0 D A))) (hth y)
    exact hinj (a1.trans (a3.symm.trans a2.symm))
  have hid := GlobalTheory.LiftScalarCompare.eC_idem (R := R) h.grp.record
  have hu := GlobalTheory.gW_norm_eq R h.models.HW h.models.gW h.models.νW i (sg0 D A)
  have htop := GlobalTheory.T.principalLevel_eigenparts_and_conjugate_characters.1 R F (GlobalTheory.Core5.of_core h) i (sg0 D A)
    (GlobalTheory.LiftLower.schurMult_of_models R h.models.HW i (sg0 D A))
  have htop' : (⨆ c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D, GlobalTheory.LiftLower.partH R i (sg0 D A) c) = ⊤ :=
    top_le_iff.1 (htop.ge.trans (iSup_mono fun c => iSup_le fun _ => le_rfl))
  have hm := GlobalTheory.mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts th _ (Real.exp (lowB D i b)) htop'
    (scalar_on_part_ofCore R hA h hp i b (hb i) th hth)
  have key := GlobalTheory.LowTopBound.le_eigenvalue th (R.thG i A.μ0) (GlobalTheory.LiftLower.projH R i (sg0 D A)) _ l hS
    (GlobalTheory.LowTopBound.idem_apply (R.gW i (sg0 D A)) hid)
    (fun x hx y => GlobalTheory.LiftScalarCompare.adjoint_idem (R.gW i (sg0 D A)) hu hid hx y) hm x hx hl hxl
  exact (Real.le_log_iff_exp_le hl).2 key

end GlobalTheory.LowTopCore

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAdjointEigenvalueLowerBoundBaseEmbeddingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAdjoint_eigenvalue_lower_bound_base_embedding : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ (s : ℕ) (b : ℝ), AdelC R F → GlobalTheory.Hk3.Core R F → A.fam.Ok s → PrimeToHost R A.μ0 → (∀ i, Sizes D i b) → GlobalTheory.BigOn.LowTop R b := by
  first | exact @GlobalTheory.LowTopCore.lowTop_ofCore | exact GlobalTheory.LowTopCore.lowTop_ofCore | (intros; apply GlobalTheory.LowTopCore.lowTop_ofCore <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundBasePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundBasePlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowRow

theorem l6m_le_log_lam3_base_place {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) : ∀ b : ℝ, R.WeakCharacterisation F → R.PThmA → R.PPos → LowTop R.toRealDat b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p, (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p A3.A.v0) := by
  intro b hC hA hP hL hB j p
  by_cases hW : R.Wp3 j p = ⊥
  · rw [hC.scal.abs0 j A3.A.μ0 p hW, Real.log_exp]
  · obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
    have hpos : 0 < R.lam3 j A3.A.μ0 p A3.A.v0 := hP.2 j A3.A.μ0 p A3.A.v0
    have heig := hA j A3.A.μ0 p x hx
    exact (hB j).trans (hL j _ x hx0 hpos heig)

end GlobalTheory.LowRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundBasePlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_liftEigenvalue_lowerBound_basePlace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ b : ℝ, R.WeakCharacterisation F → R.PThmA → R.PPos → LowTop R.toRealDat b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p, (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p A3.A.v0) := by
  first | exact @GlobalTheory.LowRow.l6m_le_log_lam3_base_place | exact GlobalTheory.LowRow.l6m_le_log_lam3_base_place | (intros; apply GlobalTheory.LowRow.l6m_le_log_lam3_base_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundOtherPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundOtherPlaces
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn

namespace GlobalTheory.LowOff

theorem le_log_of_inner_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (w : E) (m : ℂ) (lam B : ℝ)
    (hlam : 0 < lam) (hm : m ≠ 0) (hg : ⟪w, w⟫_ℂ = ((lam : ℝ) : ℂ) * m) (hl : Real.exp B * m.re ≤ ‖w‖ ^ 2) :
    B ≤ Real.log lam := by
  rw [inner_self_eq_norm_sq_to_K] at hg
  have hg' : ((‖w‖ ^ 2 : ℝ) : ℂ) = ((lam : ℝ) : ℂ) * m := by rw [Complex.ofReal_pow]; exact hg
  have hre := congrArg Complex.re hg'
  have him := congrArg Complex.im hg'
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hre him
  have him0 : m.im = 0 := by
    rcases mul_eq_zero.mp him.symm with h | h
    · exact absurd h hlam.ne'
    · exact h
  have hre0 : m.re ≠ 0 := fun h => hm (Complex.ext h him0)
  have hpos : 0 < m.re := by
    have : 0 ≤ lam * m.re := by rw [← hre]; positivity
    exact lt_of_le_of_ne (nonneg_of_mul_nonneg_right (by linarith) hlam) (Ne.symm hre0)
  rw [Real.le_log_iff_exp_le hlam]
  have : Real.exp B * m.re ≤ lam * m.re := by rw [← hre]; exact hl
  exact le_of_mul_le_mul_right this hpos

theorem partAt_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (j p v) :
    R.PartAt F j p v ↔ ∃ x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0) → D.what₂.LL,
      (R.toCx3 F).tC F.cr false j A3.A.μ0 (cpt A3.A.v0.embedding x) ∈ (R.toCx3 F).Wp j p ∧
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((lv (F.fc (R.toCx3 F).zs) false).XT j A3.A.μ0) v x x ≠ 0 := Iff.rfl


set_option maxHeartbeats 4000000 in
theorem l6m_le_log_lam3_other_places : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ b : ℝ, R.WeakCharacterisation F → (∀ i, R.phs i = 1) → R.PPos → (R.toCx3 F).GalD F.cr false → LowForm R.toRealDat F.lv2 b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p v, v ≠ A3.A.v0 → (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p v) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F b hC hph hP hG hL hb j p v hv
  by_cases hPA : R.PartAt F j p v
  · rw [partAt_iff, GlobalTheory.CharRealise.toCx3_eq_one R F hph] at hPA
    rw [GlobalTheory.CharRealise.toCx3_eq_one R F hph] at hG hb ⊢
    obtain ⟨x, hx, hne⟩ := hPA
    exact (hb j).trans (le_log_of_inner_eq _ _ _ _ (hP.2 j A3.A.μ0 p v) hne (hG j v hv p x hx x) (hL j v hv x))
  · rw [hC.scal.abs j p v hv hPA, Real.log_exp]

end GlobalTheory.LowOff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundOtherPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_liftEigenvalue_lowerBound_otherPlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), ∀ b : ℝ, R.WeakCharacterisation F → (∀ i, R.phs i = 1) → R.PPos → (R.toCx3 F).GalD F.cr false → LowForm R.toRealDat F.lv2 b → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → ∀ j p v, v ≠ A3.A.v0 → (F.Zsc (R.toCx3 F).zs).l6m j ≤ Real.log (R.lam3 j A3.A.μ0 p v) := by
  first | exact @GlobalTheory.LowOff.l6m_le_log_lam3_other_places | exact GlobalTheory.LowOff.l6m_le_log_lam3_other_places | (intros; apply GlobalTheory.LowOff.l6m_le_log_lam3_other_places <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEigenvalueLowerBoundOfWeakCharacterisation
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow

theorem lamLow_of_weak : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCR D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH hOk hsep hC hEx prim hph hstd fw hbar hio hpins hrow0 htie hsz hlow hnum hAd hPH
  obtain ⟨hcore, hok, hlinks⟩ := GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hsep hC hEx prim hph
  have hgal : ∀ i, GalOut R.toRealDat i 1 := fun i =>
    hCR D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O 1 (GlobalTheory.Core5.of_core hcore) hstd fw hbar hio prim.unif hpins i (by
      have h1 := htie i prim.unif (hrow0 i)
      simp only [hph] at h1
      simpa using h1)
  have hext : ∀ i σ, ∃ v : (R.toRealDat.MW i σ).Vec, IsExtVec (R.toRealDat.MW i σ) v := fun i σ => ⟨v₀ i σ, (fw.hv₀ i σ).1⟩
  have htop := GlobalTheory.T.liftAdjoint_eigenvalue_lower_bound_base_embedding R.toRealDat F.lv2 s b hAd hcore hok hPH hsz
  have hform := GlobalTheory.T.rationalLift_lowerBound_off_basePlace R.toRealDat F.lv2 s b hAd hgal hcore hok hext prim.unif hlinks hPH hsz
  have h0 := GlobalTheory.T.log_liftEigenvalue_lowerBound_basePlace R F b hC prim.thmA prim.posScal htop hlow
  have h1 := GlobalTheory.T.log_liftEigenvalue_lowerBound_otherPlaces R F b hC hph prim.posScal prim.scalConj hform hlow
  intro j p v
  have hn := hnum j
  by_cases hv : v = A3.A.v0
  · subst hv
    have := h0 j p
    exact le_trans hn this
  · have := h1 j p v hv
    exact le_trans hn this

end GlobalTheory.LowRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEigenvalueLowerBoundOfWeakCharacterisationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftEigenvalueLowerBound_of_weakCharacterisation : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  first | exact @GlobalTheory.LowRow.lamLow_of_weak | exact GlobalTheory.LowRow.lamLow_of_weak | (intros; apply GlobalTheory.LowRow.lamLow_of_weak <;> assumption)
end
