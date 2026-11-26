module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHolomorphicLieFrame
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin

namespace GlobalTheory.HolLieFrame

theorem differentiableAt_of_forms {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {g : ℕ} (W : V → Fin g → ℂ)
    (b₀ : V) (H : ∀ w : Fin g → ℂ, (∀ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), DifferentiableAt ℂ L b₀ →
      DifferentiableAt ℂ (fun b => L b (W b)) b₀ → L b₀ w = 0) → w = 0) : DifferentiableAt ℂ W b₀ := by
  let M : Submodule ℂ (Module.Dual ℂ (Fin g → ℂ)) :=
    { carrier := {l | ∃ L : V → ((Fin g → ℂ) →L[ℂ] ℂ), DifferentiableAt ℂ L b₀ ∧
        DifferentiableAt ℂ (fun b => L b (W b)) b₀ ∧ ∀ w, L b₀ w = l w}
      add_mem' := by
        rintro l l' ⟨L, h1, h2, h3⟩ ⟨L', h1', h2', h3'⟩
        exact ⟨fun b => L b + L' b, h1.add h1', h2.add h2', fun w => by simp [h3, h3']⟩
      zero_mem' := ⟨fun _ => 0, differentiableAt_const _, by simp, by simp⟩
      smul_mem' := by
        rintro c l ⟨L, h1, h2, h3⟩
        exact ⟨fun b => c • L b, h1.const_smul c, h2.const_smul c, fun w => by simp [h3]⟩ }
  have hM : M = ⊤ := by
    have h0 : M.dualCoannihilator = ⊥ := by
      refine eq_bot_iff.2 fun w hw => H w fun L h1 h2 => ?_
      exact (Submodule.mem_dualCoannihilator w).1 hw (L b₀).toLinearMap ⟨L, h1, h2, fun _ => rfl⟩
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := M), h0, Submodule.dualAnnihilator_bot]
  have hj : ∀ j : Fin g, LinearMap.proj j ∈ M := fun j => hM ▸ Submodule.mem_top
  choose L h1 h2 h3 using hj
  let J : V → ((Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) := fun b => ContinuousLinearMap.pi fun j => L j b
  have hJ : DifferentiableAt ℂ J b₀ :=
    (ContinuousLinearMap.piEquivL ℂ (Fin g → ℂ) (fun _ : Fin g => ℂ)).differentiableAt.comp b₀
      (differentiableAt_pi.2 h1)
  have hJ0 : IsUnit (J b₀) := by
    have : J b₀ = 1 := by
      ext1 w
      funext j
      exact h3 j w
    rw [this]; exact isUnit_one
  have hW : DifferentiableAt ℂ (fun b => J b (W b)) b₀ := differentiableAt_pi.2 h2
  refine ((hJ.inverse hJ0).clm_apply hW).congr_of_eventuallyEq ?_
  filter_upwards [hJ.continuousAt.eventually (Units.isOpen.mem_nhds hJ0)] with b hb
  have := congrArg (fun T : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ) => T (W b)) (Ring.inverse_mul_cancel _ hb)
  exact this.symm

theorem evalPt_appLE {A : Type} [CommRing A] {X Y : Scheme.{0}} (v : Sp A ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ φ ⁻¹ᵁ U) (f : Γ(Y, U)) (hV : ⊤ ≤ v ⁻¹ᵁ V) (hU : ⊤ ≤ (v ≫ φ) ⁻¹ᵁ U) :
    evalPt v V hV ((φ.appLE U V e).hom f) = evalPt (v ≫ φ) U hU f := by
  simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply (φ.appLE U V e), Scheme.Hom.appLE_comp_appLE]

theorem exists_fraction {A : Type} [CommRing A] {X : Scheme.{0}} (ψ : Sp A ⟶ X) (U : X.Opens) (f : Γ(X, U))
    (t₀ : A →+* ℂ) (h₀ : ⊤ ≤ (spMap t₀ ≫ ψ) ⁻¹ᵁ U) :
    ∃ r a : A, t₀ r ≠ 0 ∧ ∀ (C : Type) [CommRing C] (t : A →+* C), IsUnit (t r) →
      ∃ h : ⊤ ≤ (spMap t ≫ ψ) ⁻¹ᵁ U, evalPt (spMap t ≫ ψ) U h f * t r = t a := by
  have hY := isAffineOpen_top (Sp A)
  obtain ⟨s, hsU, hs⟩ := hY.exists_basicOpen_le (V := ψ ⁻¹ᵁ U)
    ⟨_, (top_le_preimage_iff_mem _ _).1 ((top_le_preimage_comp _ ψ U).1 h₀)⟩ trivial
  have hloc := hY.isLocalization_basicOpen s
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s) ((ψ.appLE U _ hsU).hom f)
  have ha' : (ψ.appLE U _ hsU).hom f * resG _ ((Sp A).basicOpen_le s) (s ^ n) =
    resG _ ((Sp A).basicOpen_le s) a := ha
  obtain ⟨s, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 s
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 a
  have hs₀ : t₀ s ≠ 0 := by
    have := (top_le_preimage_basicOpen_iff _ _ _).1 ((top_le_preimage_iff_mem (spMap t₀) _).2 hs)
    rwa [valAt'_eq_evalPt _ _ le_rfl, evalPt_spMap] at this
  refine ⟨s ^ (n + 1), a * s, by rw [map_pow]; exact pow_ne_zero _ hs₀, fun C _ t ht => ?_⟩
  have hu : IsUnit (t s) := by
    rw [map_pow] at ht
    exact (isUnit_pow_iff n.succ_ne_zero).1 ht
  have hD : ⊤ ≤ spMap t ⁻¹ᵁ (Sp A).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s) := by
    rw [← evalPt_spMap t s] at hu
    have hu' := hu.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom
    simp only [evalPt, CommRingCat.hom_comp, RingHom.comp_apply, Iso.hom_inv_id_apply] at hu'
    have := Scheme.basicOpen_appLE (spMap t) ⊤ ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of A)).inv s)
    rw [(Sp C).basicOpen_of_isUnit hu', top_inf_eq] at this
    exact this.le
  have h : ⊤ ≤ (spMap t ≫ ψ) ⁻¹ᵁ U := fun p hp => hsU (hD hp)
  refine ⟨h, ?_⟩
  have := congrArg (evalPt (spMap t) _ hD) ha'
  rw [map_mul, evalPt_appLE _ _ _ _ _ _ _ h, evalPt_res _ _ le_rfl, evalPt_res _ _ le_rfl, map_pow, evalPt_spMap,
    evalPt_spMap] at this
  rw [map_pow, pow_succ, ← _root_.mul_assoc, this, map_mul]

theorem exists_hol_snd {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    (ψ : Sp (DualNumber R) ⟶ X) (ev : V → (R →+* ℂ)) (b₀ : V) (hev : ∀ c, DifferentiableAt ℂ (fun b => ev b c) b₀)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ (spMap (Chart.dualMapR (ev b₀)) ≫ ψ) ⁻¹ᵁ U) :
    ∃ F : V → ℂ, DifferentiableAt ℂ F b₀ ∧ ∀ᶠ b in 𝓝 b₀,
      ∃ h : ⊤ ≤ (spMap (Chart.dualMapR (ev b)) ≫ ψ) ⁻¹ᵁ U, (evalPt _ U h f).snd = F b := by
  have h₁ : ⊤ ≤ (spMap (fstC.comp (Chart.dualMapR (ev b₀))) ≫ ψ) ⁻¹ᵁ U := by
    have := (top_le_preimage_iff _ U).1 h₀
    rwa [← Category.assoc, ← Spec.map_comp] at this
  obtain ⟨r, a, hr, H⟩ := exists_fraction ψ U f _ h₁
  have hf : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).fst = ev b x.fst := fun b x => by simp [Chart.dualMapR]
  have hs : ∀ b (x : DualNumber R), (Chart.dualMapR (ev b) x).snd = ev b x.snd := fun b x => by simp [Chart.dualMapR]
  have hr' : ev b₀ r.fst ≠ 0 := (hf b₀ r) ▸ hr
  refine ⟨fun b => (ev b a.snd - ev b a.fst * (ev b r.fst)⁻¹ * ev b r.snd) * (ev b r.fst)⁻¹,
    ((hev a.snd).sub (((hev a.fst).mul ((hev r.fst).inv hr')).mul (hev r.snd))).mul ((hev r.fst).inv hr'), ?_⟩
  filter_upwards [(hev r.fst).continuousAt.eventually_ne hr'] with b hb
  obtain ⟨h, e⟩ := H _ (Chart.dualMapR (ev b)) (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by rw [hf]; exact hb.isUnit))
  refine ⟨h, ?_⟩
  have e1 := congrArg TrivSqZeroExt.fst e
  have e2 := congrArg TrivSqZeroExt.snd e
  rw [TrivSqZeroExt.fst_mul, hf, hf] at e1
  rw [DualNumber.snd_mul, hf, hs, hs] at e2
  rw [← e1, ← e2]
  field_simp
  ring

theorem differentiableAt_ev {V R : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CommRing R] {X : Scheme.{0}}
    {B : Set V} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) (j : Sp R ⟶ X) [IsOpenImmersion j] (ev : V → (R →+* ℂ))
    (h : ∀ b ∈ B, y b = spMap (ev b) ≫ j) {b₀ : V} (hb : b₀ ∈ B) (c : R) :
    DifferentiableAt ℂ (fun b => ev b c) b₀ := by
  have hle : ⊤ ≤ j ⁻¹ᵁ (j ''ᵁ ⊤) := (j.preimage_image_eq ⊤).ge
  have h₀ : ⊤ ≤ y b₀ ⁻¹ᵁ (j ''ᵁ ⊤) := by
    rw [h b₀ hb]
    exact fun p _ => hle (Set.mem_univ _)
  refine (LocalLift.hol_differentiableAt hy hb h₀
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))).congr_of_eventuallyEq ?_
  filter_upwards [LocalLift.hol_eventually_mem hy hb h₀] with b hb'
  rw [h b hb'.1, ← valAt'_appLE _ j _ ⊤ hle _ le_rfl, valAt'_eq_evalPt _ _ le_rfl, ← evalPt_spMap (ev b) c,
    ← CommRingCat.comp_apply (j.appIso ⊤).inv, Scheme.Hom.appIso_inv_appLE]
  simp

theorem differentiableAt_fderiv {m g : ℕ} {X : Scheme.{0}} {B : Set (Fin m → ℂ)}
    {e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (he : IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => e bz.1 bz.2)) {b₀ : Fin m → ℂ} (hb : b₀ ∈ B)
    (U : X.Opens) (f : Γ(X, U)) (h₀ : ⊤ ≤ e b₀ 0 ⁻¹ᵁ U) :
    DifferentiableAt ℂ (fun b => fderiv ℂ (fun z => valAt' (e b z) U f) 0) b₀ := by
  have h1 := SCV.analyticOnNhd_of_differentiableOn (he U f).1 (he U f).2 (b₀, 0) ⟨⟨hb, trivial⟩, h₀⟩
  have h2 := ContDiffAt.fderiv (𝕜 := ℂ) (f := fun b z => valAt' (e b z) U f) (g := fun _ => 0) (x₀ := b₀) (m := 1)
    (n := 2) h1.contDiffAt contDiffAt_const le_rfl
  exact h2.differentiableAt one_ne_zero

section Fibre

open GlobalTheory.GrpTangent

variable {G : Over (Sp ℂ)} [GrpObj G] {X : Scheme.{0}} {ψ : G.left ⟶ X} {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}

end Fibre

end GlobalTheory.HolLieFrame

namespace GlobalTheory

open HolLieFrame
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjIsAbelianSchemeDimRigidifiedSym
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding JetR zR

noncomputable section

namespace GlobalTheory.ObjDim

open ReciprocityTheory.ChartRestriction.G.Chart (sp JetR zR IsUnivChart jetLift jetLift_zR jet_ext jetAug_zR tmap tvec eigLat)

theorem exists_isUnivChart {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    [IsCommMonObj G] (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin g) m) ⟶ G, IsUnivChart G g x := by
  obtain ⟨X, h0, hnat, hinj, hsurj⟩ := NilCoord.nilpotent_coordinates G g hG
  have nil : ∀ {A : Type} [CommRing A] (J : Ideal A) (m : ℕ), J ^ (m + 1) = ⊥ → ∀ a ∈ J, IsNilpotent a :=
    fun J m hJ a ha => ⟨m + 1, by
      have := Ideal.pow_mem_pow ha (m + 1)
      rwa [hJ, Ideal.mem_bot] at this⟩
  have hz : ∀ m (i : Fin g), IsNilpotent (zR (R := R) m i) := fun m i =>
    nil _ m (Chart.ker_jetAug_pow (Fin g) m) _ (Chart.zR_mem_ker m i)
  refine ⟨fun m => X _ (zR m), fun m => hnat _ _ _ _ (hz _), fun m => ?_, fun A _ _ aug m hJ y hy => ?_⟩
  · rw [hnat _ _ _ _ (hz _), ← h0]
    congr 1
    funext i
    have h := Ideal.pow_mem_pow (Chart.zR_mem_ker (R := R) 0 i) (0 + 1)
    rw [Chart.ker_jetAug_pow, Ideal.mem_bot] at h
    exact (pow_one _).symm.trans h
  · obtain ⟨a, ha, rfl⟩ := hsurj A R aug (fun r => ⟨algebraMap R A r, aug.commutes r⟩) (nil _ m hJ) y hy
    refine ⟨jetLift R _ hJ a ha, ⟨jet_ext fun j => ?_, ?_⟩, fun ψ hψ => jet_ext fun j => ?_⟩
    · rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact ha j
    · rw [hnat _ _ _ _ (hz _)]
      simp only [jetLift_zR]
    · rw [jetLift_zR]
      have h := hψ.2
      rw [hnat _ _ _ _ (hz _)] at h
      exact (congrFun (hinj A _ _ (fun i => nil _ m hJ _ (ha i)) (fun i => (hz m i).map ψ) h) j).symm

def tanAct {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) {O : Type} [CommRing O]
    (act : OAct O G) : O →+* Module.End R (Fin n → R) :=
  haveI := act.hom
  RingHom.mk'
    { toFun := fun a => tmap hx (act.act a)
      map_one' := LinearMap.ext fun c => Chart.tvec_inj hx (by
        rw [Chart.tvec_tmap, act.one, Category.comp_id]; rfl)
      map_mul' := fun a b => LinearMap.ext fun c => Chart.tvec_inj hx (by
        rw [Module.End.mul_apply, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, mul_comm, act.mul,
          Category.assoc]) }
    fun a b => LinearMap.ext fun c => Chart.tvec_inj hx (by
      show tvec (tmap hx (act.act (a + b)) c) = tvec (tmap hx (act.act a) c + tmap hx (act.act b) c)
      rw [Chart.tvec_add hx, Chart.tvec_tmap, Chart.tvec_tmap, Chart.tvec_tmap, act.add, MonObj.comp_mul])

theorem isGrpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let j : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e₁ : x₀ = j ≫ x := Over.OverMorphism.ext (by simp [hx, j])
  have e₂ : y₀ = j ≫ y := Over.OverMorphism.ext (by simp [hy, j])
  rw [e₁, e₂, ← MonObj.comp_mul]
  simp [j]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finrank_eq_of_eigen (H : Host E) {k : Type} [Field k] [IsAlgClosed k] [CharZero k] {N : Type} [AddCommGroup N]
    [Module k N] [Module.Finite k N] (act : 𝓞 E →+* Module.End k N) (ρ : k) (hρ : ρ ^ 2 = -(H.d : k)) (p q : ℕ)
    (h : ∀ τ : 𝓞 E →+* k, (τ H.rt = ρ → Module.finrank k (EigenSplit.eigenSub act τ) = p) ∧
      (τ H.rt ≠ ρ → Module.finrank k (EigenSplit.eigenSub act τ) = q)) :
    Module.finrank k N = Module.finrank ℚ E / 2 * (p + q) := by
  classical
  let σ : (E →+* k) → (𝓞 E →+* k) := fun φ => φ.comp (algebraMap (𝓞 E) E)
  have hc := NumberField.Embeddings.card E k
  obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) hc
  have hs : EigenSplit.IsSplitting σ :=
    EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  have h1 : Module.finrank k N = ∑ φ, Module.finrank k (EigenSplit.eigenSub act (σ φ)) := by
    rw [(EigenSplit.eigenEquiv hs act).finrank_eq, Module.finrank_pi_fintype]
  let c : (E →+* k) → (E →+* k) := fun φ => φ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hcc : Function.Involutive c := fun φ => RingHom.ext fun a => by
    simp [c]
  have hrt : ∀ φ, σ (c φ) H.rt = -σ φ H.rt := fun φ => by
    rw [← map_neg, ← HostModel.bar_rt]
    exact congrArg φ (H.bar_eq H.rt).symm
  have hd : (H.d : k) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have h2 : ∀ φ, Module.finrank k (EigenSplit.eigenSub act (σ φ)) +
      Module.finrank k (EigenSplit.eigenSub act (σ (c φ))) = p + q := fun φ => by
    have hsq : σ φ H.rt ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, map_neg, map_natCast, hρ]
    have hne : -ρ ≠ ρ := fun e => hd (by
      have : ρ = 0 := by linear_combination (-1 / 2 : k) * e
      rw [this] at hρ
      simpa using hρ)
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with e | e
    · rw [(h _).1 e, (h _).2 (by rw [hrt, e]; exact hne)]
    · rw [(h _).2 (by rw [e]; exact hne), (h _).1 (by rw [hrt, e, neg_neg]), add_comm]
  have h3 : 2 * Module.finrank k N = Module.finrank ℚ E * (p + q) := by
    have := Equiv.sum_comp hcc.toPerm fun φ => Module.finrank k (EigenSplit.eigenSub act (σ φ))
    rw [two_mul, h1]
    conv_lhs => arg 2; rw [← this]
    rw [← Finset.sum_add_distrib, ← hc]
    exact (Finset.sum_congr rfl fun φ _ => h2 φ).trans (by simp)
  rw [← (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E),
    Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h3 ⊢
  rw [Nat.mul_div_cancel _ two_pos]
  linarith

variable {H : Host E} {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
  {s : S ⟶ Sp B}

theorem dim_geometric_fibre (o : Obj D l b s) {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) {d : ℕ}
    (hd : SmoothOfRelativeDimension d ((Over.pullback x).obj o.t.G).hom) :
    d = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  let β : B →+* k := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have : CharZero k := ⟨fun n m e => by
    have := CharP.exists k
    obtain ⟨r, hr⟩ := this
    have hr0 : r = 0 := by
      by_contra h
      have := (b.unit r (Nat.pos_of_ne_zero h)).map β
      rw [map_natCast, CharP.cast_eq_zero] at this
      exact not_isUnit_zero this
    subst hr0
    have := CharP.charP_to_charZero k
    exact Nat.cast_injective e⟩
  obtain ⟨hdet, -⟩ := o.geom k x β hβ
  have := o.t.semi.comm
  have : IsCommMonObj ((Over.pullback x).obj o.t.G) := inferInstance
  obtain ⟨z, hz⟩ := exists_isUnivChart ((Over.pullback x).obj o.t.G) d hd
  let act := OAct.pullback x o.t.G o.t.act
  have := act.hom
  have key : ∀ (τ : 𝓞 E →+* k) N, LieMult o.t.act x τ N →
      Module.finrank k (EigenSplit.eigenSub (tanAct hz act) τ) = N := fun τ N hL => by
    have e : EigenSplit.eigenSub (tanAct hz act) τ = eigLat hz act.act fun a => τ a := by
      ext c
      rw [EigenSplit.mem_eigenSub, Chart.mem_eigLat_iff]
      rfl
    rw [e]
    exact Chart.finrank_of_lieMult (isGrpPullback_id o.t.G) (Category.comp_id x) hz o.t.act o.t.act.act
      (fun a => by simp) act.act (fun a => rfl) τ hL
  have := finrank_eq_of_eigen H (tanAct hz act) (β b.ρ) (by rw [← map_pow, b.ρ_sq, map_neg, map_natCast]) D.p D.q
    fun τ => ⟨fun h => key τ _ ((hdet τ).1 h), fun h => key τ _ ((hdet τ).2 h)⟩
  simpa using this

theorem smoothOfRelativeDimension (o : Obj D l b s) :
    SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom := by
  have := o.t.semi.smooth
  have := o.t.semi.geomConnected
  choose n W hW hd using H1.exists_dim o.t.G.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q))) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let κ := S.residueField (o.t.G.hom y)
  let k := AlgebraicClosure κ
  let x : Sp k ⟶ S := spMap (algebraMap κ k) ≫ S.fromSpecResidueField (o.t.G.hom y)
  have hp := (isGrpPullback_pullback o.t.G x).1
  obtain ⟨y', hy', -⟩ := Scheme.exists_preimage_of_isPullback hp y (default : PrimeSpectrum k)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have : Smooth ((Over.pullback x).obj o.t.G).hom := by
    change Smooth (pullback.snd o.t.G.hom x)
    infer_instance
  have : ConnectedSpace ((Over.pullback x).obj o.t.G).left :=
    GeometricallyConnected.geometrically_connectedSpace (f := o.t.G.hom) x _ _ hp
  obtain ⟨d, hd'⟩ := exists_dim_of_preconnected ((Over.pullback x).obj o.t.G).hom y'
  rw [← dim_geometric_fibre o x hd', ← H1.dim_base hp (hd y) hd' y' (by rw [hy']; exact hW y)]
  exact hd y

end GlobalTheory.ObjDim

namespace GlobalTheory

theorem obj_isAbelianScheme_dim_rigidified_sym :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type)
      [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧
      SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧
      Out.Sym o.t.G o.t.PP.L := by
  intro E _ _ _ H D l B _ b S s o
  obtain ⟨-, ws, gs', -⟩ := o.t.sym
  exact ⟨⟨inferInstance, o.t.semi.smooth, o.proper, o.t.semi.geomConnected⟩, ObjDim.smoothOfRelativeDimension o,
    ⟨o.t.PP.rig, o.t.PP.rigGen⟩, fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩⟩

def objPolAV {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {B : Type}
    [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s) : Out.PolAV S where
  A := o.t.G
  isAb := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).1
  g := Module.finrank ℚ E / 2 * (D.p + D.q)
  smoothDim := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.1
  L := o.t.PP.L
  isLB := o.t.PP.isLB
  rigid := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.2.1
  sym := (obj_isAbelianScheme_dim_rigidified_sym E H D l B b S s o).2.2.2
  ample := o.ample
  ktriv := o.ktriv

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionOtherModelSameValues
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionOtherModelSameValues
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.FibreSection

variable {X X' Y : Scheme.{0}}

theorem chart_le (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ h ⁻¹ᵁ (L.pull F).U (fun _ => j 0) := fun y hy =>
  mem_pull.2 ((congrArg (fun q => q y ∈ L.U (j 0)) e).mpr (LB.wchart_le L _ j 0 hy))

theorem le_chart (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (j : L.ι) :
    h ⁻¹ᵁ (L.pull F).U (fun _ => j) ≤ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => j) := fun y hy =>
  Set.mem_iInter.2 fun _ => (congrArg (fun q => q y ∈ L.U j) e).mp (mem_pull.1 hy)

def pullAlong (L : LB X) {F : X' ⟶ X} {φ : Y ⟶ X} (h : Y ⟶ X') (e : h ≫ F = φ) (s : LB.Sec (L.pull F)) :
    LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)) where
  f := fun (j : Fin 1 → L.ι) => (h.appLE _ _ (chart_le L h e j)).hom (s.f (fun _ => j 0))
  compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
    have h₁ : h y ∈ (L.pull F).U (fun _ => j 0) := chart_le L h e j hy.1
    have h₂ : h y ∈ (L.pull F).U (fun _ => j' 0) := chart_le L h e j' hy.2
    have g : gm (𝟙 Y) y _ ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => 1)).g j j') =
        gm (𝟙 Y ≫ φ) y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) :=
      (gm_linComb L _ _ (𝟙 Y) y j j' hy.1 hy.2).trans (by rw [Fin.prod_univ_one, zpow_one])
    have eφ : (𝟙 Y ≫ h) ≫ F = 𝟙 Y ≫ φ := by rw [Category.assoc, e]
    exact (gs_res _ y _ hy _).trans ((gs_appLE h _ _ _ (𝟙 _) y hy.1 _).trans ((gs_compat s (𝟙 Y ≫ h) y h₁ h₂).trans
      (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
        ((gs_unit _ y _ hy _).trans (congrArg Units.val (g.trans ((congrArg (fun q => gm q y (L.U (j 0) ⊓ L.U (j' 0))
          (L.g (j 0) (j' 0))) eφ).symm.trans (gm_pull_g L F (𝟙 Y ≫ h) y _ _ h₁ h₂).symm))))
        ((gs_res _ y _ hy _).trans (gs_appLE h _ _ _ (𝟙 _) y hy.2 _)))))))

theorem valAt'_appLE (pt : Sp ℂ ⟶ Y) (h : Y ⟶ X') (U : X'.Opens) (W : Y.Opens) (le : W ≤ h ⁻¹ᵁ U)
    (ge : h ⁻¹ᵁ U ≤ W) (f : Γ(X', U)) :
    valAt' pt W ((h.appLE U W le).hom f) = valAt' (pt ≫ h) U f := by
  unfold valAt'
  by_cases hp : ⊤ ≤ pt ⁻¹ᵁ W
  · have hp' : ⊤ ≤ (pt ≫ h) ⁻¹ᵁ U := fun z hz => le (hp hz)
    rw [dite_eq_left hp, dite_eq_left hp']
    unfold valAt
    congr 1
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
  · have hp' : ¬ ⊤ ≤ (pt ≫ h) ⁻¹ᵁ U := fun k => hp fun z hz => ge (k hz)
    rw [dite_eq_right hp, dite_eq_right hp']

theorem exists_sec_same_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec), ∃ s' : LB.Sec (PPx y), ∀ j (pt : Sp ℂ ⟶ Gx y) (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y), x ≫ pullback.fst _ _ = pt ≫ gxFst y → x ≫ pullback.snd _ _ = 𝟙 _ → pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U (fun _ => j)) (s'.f (fun _ => j)) = valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) := by
  intro E _ _ _ H Dw l Xo y s
  have cond : gxFst y ≫ Xo.univ.t.G.hom = gxSnd y ≫ y :=
    (Over.w (CartesianMonoidalCategory.snd (Over.mk y) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk y) Xo.univ.t.G)).symm
  let h : Gx y ⟶ pullback Xo.univ.t.G.hom y := pullback.lift _ _ cond
  have hφ : h ≫ pullback.fst _ _ = gxFst y := pullback.lift_fst _ _ cond
  have hh : h ≫ pullback.snd _ _ = gxSnd y := pullback.lift_snd _ _ cond
  refine ⟨pullAlong Xo.univ.t.PP.L h hφ s, fun j pt x e₁ e₂ e₃ => ?_⟩
  have hx : x = pt ≫ h := by
    apply pullback.hom_ext
    · rw [Category.assoc, hφ, e₁]
    · rw [Category.assoc, hh, e₂, e₃]
  subst hx
  exact valAt'_appLE pt h _ _ (chart_le Xo.univ.t.PP.L h hφ (fun _ => j)) (le_chart Xo.univ.t.PP.L h hφ j) _

end GlobalTheory.FibreSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFibreSectionOtherModelSameValuesStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreSection_other_model_same_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : (Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).Sec), ∃ s' : LB.Sec (PPx y), ∀ j (pt : Sp ℂ ⟶ Gx y) (x : Sp ℂ ⟶ pullback Xo.univ.t.G.hom y), x ≫ pullback.fst _ _ = pt ≫ gxFst y → x ≫ pullback.snd _ _ = 𝟙 _ → pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U (fun _ => j)) (s'.f (fun _ => j)) = valAt' x ((Xo.univ.t.PP.L.pull (pullback.fst Xo.univ.t.G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) := by
  first | exact @GlobalTheory.FibreSection.exists_sec_same_values | exact GlobalTheory.FibreSection.exists_sec_same_values | (intros; apply GlobalTheory.FibreSection.exists_sec_same_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermEqOfNormalised
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.RiemannForm

theorem eq_of_im {g : ℕ} (h τ Hm A B : Matrix (Fin g) (Fin g) ℂ) (hA : h * A = 1) (hB : h * B = τ)
    (h1 : ∀ a b, ((Aᵀ * Hm * A.map (starRingEnd ℂ)) a b).im = 0)
    (h2 : ∀ a b, ((Aᵀ * Hm * B.map (starRingEnd ℂ)) a b).im = -(1 : Matrix (Fin g) (Fin g) ℝ) a b) :
    Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧
      Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  have hA' : A * h = 1 := mul_eq_one_comm.mp hA
  have hB' : B = A * τ := by rw [← hB, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  set M := Aᵀ * Hm * A.map (starRingEnd ℂ) with hM
  have hMB : Aᵀ * Hm * B.map (starRingEnd ℂ) = M * τ.map (starRingEnd ℂ) := by
    rw [hB', Matrix.map_mul, hM]; simp only [Matrix.mul_assoc]
  have hMY : M.map Complex.re * τ.map Complex.im = 1 := by
    ext a b
    have := h2 a b
    rw [hMB, Matrix.mul_apply, Complex.im_sum] at this
    rw [Matrix.mul_apply, ← neg_inj, ← this, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [h1 a c]
  have hinv : (τ.map Complex.im)⁻¹ = M.map Complex.re := Matrix.inv_eq_left_inv hMY
  have hMre : (M.map Complex.re).map (fun x : ℝ => (x : ℂ)) = M := by
    ext a b
    apply Complex.ext <;> simp [h1 a b]
  have hH : Hm = hᵀ * M * h.map (starRingEnd ℂ) := by
    have e1 : hᵀ * Aᵀ = 1 := by rw [← Matrix.transpose_mul, hA', Matrix.transpose_one]
    have e2 : A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hA']; simp
    calc Hm = (hᵀ * Aᵀ) * Hm * (A.map (starRingEnd ℂ) * h.map (starRingEnd ℂ)) := by
          rw [e1, e2]; simp
      _ = _ := by rw [hM]; simp only [Matrix.mul_assoc]
  refine ⟨by rw [hinv, hMre]; exact hH, ?_⟩
  have hd : M.det * (((τ.map Complex.im).det : ℝ) : ℂ) = 1 := by
    have e := congrArg Matrix.det hMY
    rw [Matrix.det_mul, Matrix.det_one] at e
    have e' : M.det = (((M.map Complex.re).det : ℝ) : ℂ) := by
      conv_lhs => rw [← hMre]
      exact (RingHom.map_det Complex.ofRealHom _).symm
    rw [e']; exact_mod_cast e
  have hc : (h.map (starRingEnd ℂ)).det = starRingEnd ℂ h.det :=
    (RingHom.map_det (starRingEnd ℂ) h).symm
  rw [hH, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc]
  have := Complex.mul_conj' h.det
  push_cast
  linear_combination (h.det * starRingEnd ℂ h.det) * hd + this

theorem entry_eq {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (u v : Fin g → Fin g → ℂ) (a b : Fin g) :
    ((Matrix.of u)ᵀᵀ * Hm * ((Matrix.of v)ᵀ).map (starRingEnd ℂ)) a b = hermForm Hm (u a) (v b) := by
  rw [Matrix.mul_assoc]
  rfl

theorem herm_eq_of_normalised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (P : D.La →+ (Fin g → ℂ)) (h τ Hm : Matrix (Fin g) (Fin g) ℂ), (∀ a b, D.EF (bas a) (bas b) = -omegaStd a b) → IsPeriod D ty P → (∀ k, h *ᵥ P (bas (Pi.single (Sum.inl k) 1)) = Pi.single k 1 ∧ h *ᵥ P (bas (Pi.single (Sum.inr k) 1)) = τ *ᵥ Pi.single k 1) → τ ∈ SiegelH (Fin g) → (∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y) → Hm = hᵀ * ((τ.map Complex.im)⁻¹).map (fun x : ℝ => (x : ℂ)) * h.map (starRingEnd ℂ) ∧ Hm.det * (((τ.map Complex.im).det : ℝ) : ℂ) = ((‖h.det‖ ^ 2 : ℝ) : ℂ) := by
  intro E _ _ _ H D g ty bas P h τ Hm hE _ hn _ hH
  refine eq_of_im h τ Hm (Matrix.of fun k => P (bas (Pi.single (Sum.inl k) 1)))ᵀ
    (Matrix.of fun k => P (bas (Pi.single (Sum.inr k) 1)))ᵀ ?_ ?_ ?_ ?_
  · ext i k
    have := congrFun (hn k).1 i
    rw [Matrix.one_apply, ← Pi.single_apply k (1 : ℂ) i, ← this]
    rfl
  · ext i k
    have := congrFun (hn k).2 i
    rw [Matrix.mulVec_single_one] at this
    exact this
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd]
  · intro a b
    rw [entry_eq, hH, hE]
    simp [omegaStd, Pi.single_apply, Matrix.one_apply]
    split_ifs <;> simp_all [eq_comm]

end GlobalTheory.RiemannForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifFibreLatticeEqOfPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifFibreLatticeEqOfPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory

namespace FibreMatch

theorem surjective_of_countable {V W L : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Countable L] (f : V →ₗ[ℂ] W) (P : L → W) (h : ∀ w, ∃ z a, w = f z + P a) : Function.Surjective f := by
  have hc : Countable (W ⧸ LinearMap.range f) :=
    Function.Surjective.countable (f := fun a => (LinearMap.range f).mkQ (P a)) fun q => by
      obtain ⟨w, rfl⟩ := (LinearMap.range f).mkQ_surjective q
      obtain ⟨z, a, rfl⟩ := h w
      refine ⟨a, ?_⟩
      have : (LinearMap.range f).mkQ (f z) = 0 := (Submodule.Quotient.mk_eq_zero _).2 ⟨z, rfl⟩
      simp only [map_add (f := _), this, zero_add]
  intro w
  by_contra hw
  have hq : (LinearMap.range f).mkQ w ≠ 0 := fun h0 => hw ((Submodule.Quotient.mk_eq_zero _).1 h0)
  have : Countable ℂ := (smul_left_injective ℂ hq).countable
  exact not_countable (α := ℝ) (Complex.ofReal_injective.countable)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem countable_La (D : Datum H) : Countable D.La := by
  have := D.fin
  have : Countable (𝓞 E) := Finsupp.Countable.of_moduleFinite (R := ℤ)
  exact Finsupp.Countable.of_moduleFinite (R := 𝓞 E)

theorem fibrewise {X : Scheme.{0}} (t : SAB H (Sp ℂ)) (t' : SAB H X) (D₁ D₂ : Datum H) {g : ℕ}
    (ty : Fin g → (E →+* ℂ))
    (P : D₁.La →+ (Fin g → ℂ)) (P' : D₂.La →+ (Fin g → ℂ)) (hP : IsPeriod D₁ ty P) (hP' : IsPeriod D₂ ty P')
    (y y' : Sp ℂ ⟶ X) (n : SABMap t t' y) (hy : (𝟙_ (Over (Sp ℂ))).hom ≫ y = y')
    (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (e' : (Fin g → ℂ) → (Over.mk y' ⟶ t'.G))
    (ha : ∀ z w, e (z + w) = e z * e w) (ha' : ∀ z w, e' (z + w) = e' z * e' w)
    (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) (hk' : ∀ z, e' z = 1 ↔ z ∈ P'.range)
    (hl : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (hl' : ∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t'.act.act a)
    (hw : ∀ (k : ℕ) (a b : D₁.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₁.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (hw' : ∀ (k : ℕ) (a b : D₂.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D₂.EF a b : ℂ) / k) →
      Out.WeilIs t'.G t'.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c))
    (hh : IsHolTo Set.univ (fun z => (e z).left)) (hh' : IsHolTo Set.univ (fun z => (e' z).left))
    (hd' : (∀ w, ∃! v : epsPt y' ⟶ t'.G, IsDerivAt0 (fun z => (e' z).left) w v.left) ∧
      ∀ v : epsPt y' ⟶ t'.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
        ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) :
    ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D₁.La ≃ₗ[𝓞 E] D₂.La), (∀ z, (e z).left ≫ n.φ = (e' (h z)).left) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ (∀ a a', D₂.EF (gam a) (gam a') = D₁.EF a a') := by
  subst hy
  have dk' : DiscreteTopology {z // e' z = 1} := by
    have h0 : (fun z => e' z = 1) = fun z => z ∈ P'.range := funext fun z => propext (hk' z)
    show DiscreteTopology (Subtype fun z => e' z = 1)
    rw [h0]
    exact hP'.2.2.1
  let ρ := pushHom n.cart (𝟙_ (Over (Sp ℂ)))
  have hρ : ∀ x, (ρ x).left = x.left ≫ n.cm.F := fun _ => rfl
  have ρi : Function.Injective ρ := fun x x' hx => Over.OverMorphism.ext <| n.cart.1.hom_ext
    (by rw [← hρ, ← hρ, hx]) (by rw [Over.w, Over.w])
  have ρs : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (n.cart.1.lift x.left (𝟙_ (Over (Sp ℂ))).hom (Over.w x)) (n.cart.1.lift_snd _ _ _),
      Over.OverMorphism.ext (n.cart.1.lift_fst _ _ _)⟩
  let ψ : pullback t.G.hom (𝟙 (Sp ℂ)) ⟶ pullback t'.G.hom ((𝟙_ (Over (Sp ℂ))).hom ≫ y) :=
    pullback.lift (pullback.fst _ _ ≫ n.cm.F) (pullback.snd _ _) (by
      rw [Category.assoc, n.cart.1.w, ← Category.assoc, pullback.condition, Category.assoc]
      rfl)
  have ψ₁ : ψ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ n.cm.F := pullback.lift_fst _ _ _
  have ψ₂ : ψ ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  obtain ⟨f, hf, -⟩ := existsUnique_linear_lift_fibre (Sp ℂ) X t.G t'.G (𝟙 _) _ g g e e' ψ ρ t'.semi.smooth ha ha'
    hh hh' hd' dk' ψ₂ (fun x => pullback.hom_ext
      (by rw [Category.assoc, ψ₁, ← Category.assoc, UniformLift.fibPt_fst, UniformLift.fibPt_fst]; rfl)
      (by rw [Category.assoc, ψ₂, UniformLift.fibPt_snd, UniformLift.fibPt_snd]))
  have hf : ∀ z, e' (f z) = ρ (e z) := hf
  have := countable_La D₂
  have fs : Function.Surjective f := surjective_of_countable f P' fun w => by
    obtain ⟨x, hx⟩ := ρs (e' w)
    obtain ⟨z, rfl⟩ := hs x
    obtain ⟨a, ha⟩ := (hk' _).1 ((ExpUniqFamily.eq_iff_sub e' ha' w (f z)).1 (hx.symm.trans (hf z).symm))
    exact ⟨z, a, by rw [ha]; abel⟩
  let fe := LinearEquiv.ofBijective f ⟨LinearMap.injective_iff_surjective.2 fs, fs⟩
  obtain ⟨h, gam, h1, h2, -⟩ := ExpUniqFamily.algebraic (fun k (a : 𝓞 E) => ty k (a : E)) P P' hP.1 hP'.1
    hP.2.1 hP'.2.1 hP.2.2.1 hP'.2.2.1 (fun z => ρ (e z)) e' (fun z w => by rw [ha, map_mul]) ha'
    (fun z => by rw [← hk, map_eq_one_iff ρ ρi]) hk' (fun a x => x ≫ t'.act.act a)
    (fun a z => by
      rw [hl]
      apply Over.OverMorphism.ext
      rw [hρ, Over.comp_left, Over.comp_left, hρ, Category.assoc, n.act, Category.assoc])
    hl' f fe.symm hf (fun z => by
      rw [← hf]
      exact congrArg e' (fe.apply_symm_apply z))
  refine ⟨h, gam, fun z => by rw [h1, hρ], h2, fun a a' => ?_⟩
  refine ExpUniqFamily.int_eq_of_exp _ _ fun k hk0 => ?_
  have hL : LBIso t.PP.L (t'.PP.L.pull n.cm.F) := by
    obtain ⟨w, hw, -⟩ := n.lin
    exact ⟨w, hw⟩
  have w1 := (weilIs_grpPullback_of_comm X (Sp ℂ) t'.G t.G y n.cm.F t'.PP.L t.PP.L t'.PP.isLB t.PP.isLB n.cart hL
    _ k _ _ (ρ _) (ρ _) _ (hρ _) (hρ _)).1 (hw k a a' (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl)
  have w2 := hw' k (gam a) (gam a') (Units.mk0 _ (Complex.exp_ne_zero _)) hk0 rfl
  rw [h2, h2, ← map_smul h, ← map_smul h, h1, h1] at w2
  exact congrArg Units.val (weilIs_unique_fieldPoint X t'.G t'.PP.L t'.PP.isLB ℂ _ k _ _ _ _ w2 w1)

end FibreMatch

theorem familyUnif_fibre_lattice_match : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (D' : Datum H) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (n : SABMap t Xo.univ.t (U.u i P)), IsPeriod (U.Di i) ty P → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ z, (e z).left ≫ n.φ = (U.ex i P (h z)).left) ∧ (∀ a, P (gam a) = h (P' a)) ∧ ∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a' := by
  intro E _ _ _ H D l Xo σ g ty U i P D' P' t e n hP hP' ⟨_, _, _, _, _, ha, hs, hk, hl, hh, hw⟩
  exact FibreMatch.fibrewise t Xo.univ.t D' (U.Di i) ty P' P hP' hP _ _ n (Category.id_comp _) e (U.ex i P) ha
    (U.ex_add i P hP) hs hk (U.ex_ker i P hP) hl (U.ex_lin i P hP) hw (U.ex_weil i P hP) hh
    (ExpUniqFamily.isHolTo_ex U i P hP) (U.ex_diff i P hP)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifFibreLatticeEqOfPullbackStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi
theorem _root_.GlobalTheory.T.familyUnif_fibre_lattice_eq_of_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)) (D' : Datum H) (P' : D'.La →+ (Fin g → ℂ)) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)) (n : SABMap t Xo.univ.t (U.u i P)), IsPeriod (U.Di i) ty P → IsPeriod D' ty P' → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D' t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P' a)) (e ((k : ℂ)⁻¹ • P' b)) (unitOn c)) → ∃ (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ z, (e z).left ≫ n.φ = (U.ex i P (h z)).left) ∧ (∀ a, P (gam a) = h (P' a)) ∧ ∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a' := by
  first | exact @GlobalTheory.familyUnif_fibre_lattice_match | exact GlobalTheory.familyUnif_fibre_lattice_match | (intros; apply GlobalTheory.familyUnif_fibre_lattice_match <;> assumption)
end
end
