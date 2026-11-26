module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PelTrivialisationIsUnitOnAbelianLocus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanish
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionValueAtTorsionPointEqSumTerms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVector
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.TestVal

open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TorusExt

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem odd_level (ρ : S.Real) : Odd (S.r * S.N) := by
  obtain ⟨j, -, hj⟩ := ρ.r_eq
  rw [hj, ρ.N_eq]
  exact ρ.n_odd.pow.mul ρ.n_odd.pow.pow

theorem powFrame_one {B : Scheme.{0}} {A T : Over B} {L : LB A.left} (x : T ⟶ A)
    (τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))) :
    powFrame A L x τ 1 = τ :=
  congrArg LB.Gen.mk (funext fun j => zpow_one (τ.s j))

theorem mk_add_smul {X : Type} [AddCommGroup X] (m : ℕ) (χ y : X) :
    (QuotientAddGroup.mk y : X ⧸ (nsmulAddMonoidHom m : X →+ X).range) = QuotientAddGroup.mk (m • χ + y) :=
  QuotientAddGroup.eq.2 ⟨χ, by simp⟩


attribute [local instance] gtGroup in
theorem exists_scale (hL : Laws) (hL₂ : Laws2) {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p}
    (u : ρ.UTest p y₀) (l : u.Lab) (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) :
    ∃ sc : ℝ, 0 ≤ sc ∧
      (∀ a, ∃ w : u.D.toPre.X, l.yy a = QuotientAddGroup.mk w ∧
        ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ sc * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) ∧
      (∀ a, sc ≠ 0 → ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = sc → a ∈ l.yy.ker) ∧
      ∀ n : ℕ, 2 ≤ n → n ∣ S.r * S.N → ∀ a ∈ l.yy.ker, ∃ a' ∈ l.yy.ker, n • (a' - a) = 0 ∧
        ‖y₀ ⟨S.th a', S.th_mem a'⟩‖ = sc := by
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have := charZero u
  have hm := odd_level ρ
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  have hB := u.D.tau_bimult
  obtain ⟨ϖ, hϖ, Q, hQ, v, hv, lam, hlam, v₁, v₂, hq⟩ := exists_val u
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.T.uniformised_model_labelled_torsion_points o Ω S ρ p y₀ u
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.T.exists_frames_on_uniformisedModel_fibre o Ω S ρ p y₀ u x hx
  obtain ⟨t, ht⟩ := hsec 1 ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW u.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ _ v hv u.A u.G
    u.semi u.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ _ v hv u.A u.G u.semi u.U w₀ rig hw₀ th ϑ hE hP
    _ hm (isUnit_level u h)
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv).2 r
  have tv : ∀ a z J, Good u.A.L z J → cst (R := u.V) (PadicAlgCl p) z sc *
      @id ((TF (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z) (sA th (ptSecT u.A.A (x a)).left z J) =
      cst (R := u.V) (PadicAlgCl p) z (y₀ ⟨S.th a, S.th_mem a⟩) * @id ((TF (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z)
        (val (powFrame u.A.A u.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := ρ.th_val a
      rw [← powFrame_one (ρ.pt a) (ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q (x a) ∧ l.yy a = QuotientAddGroup.mk q.y :=
    fun a => by
      obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
      exact ⟨q, (f₁ _ _).2 hq.symm, l.yy_eq a q _ ((f₁ _ _).2 hq.symm) (hx a)⟩
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨S.th a, S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := u.V) (F := PadicAlgCl p)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := u.V) (PadicAlgCl p)).left) u.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := u.V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    refine ⟨0, le_rfl, fun a => ?_, fun a hne => absurd rfl hne, fun n _ _ a ha => ⟨a, ha, by simp, by simp [z0]⟩⟩
    obtain ⟨q, -, hq⟩ := ex a
    exact ⟨q.y, hq, by simp [z0]⟩
  have hsc : 0 < ‖sc‖ := norm_pos_iff.2 h0
  have tv' : ∀ a z J, Good u.A.L z J → sA th (ptSecT u.A.A (x a)).left z J =
      @id ((TFK (R := u.V) (PadicAlgCl p)).left.presheaf.stalk z)
        (cst (R := u.V) (PadicAlgCl p) z (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩)) *
        (val (powFrame u.A.A u.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := u.V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨S.th a, S.th_mem a⟩) = 0 ↔ ‖y₀ ⟨S.th a, S.th_mem a⟩‖ = ‖sc‖ := fun a => by
    refine (v₁ _ 0).trans ?_
    rw [norm_mul, norm_inv, Rat.cast_zero, mul_zero, neg_zero, Real.exp_zero, inv_mul_eq_one₀ hsc.ne', eq_comm]
  refine ⟨‖sc‖, hsc.le, fun a => ?_, fun a _ ha => ?_, fun n hn hnm a ha => ?_⟩
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((S.r * S.N) • χ + q.y) = k)
      ⟨0, by
        rintro _ ⟨χ, rfl⟩
        by_cases c : (S.r * S.N) • χ + q.y = 0
        · rw [c, QForm.Q_zero hϖ u.D hQ]
        · exact zero_le_one.trans (QForm.Q_pos hϖ u.D hQ c)⟩ ⟨_, 0, rfl⟩
    refine ⟨_, hq₂.trans (mk_add_smul _ χ _), ?_⟩
    have b := (v₂ _ _).1 (((key q _ hq₁).1 _ _ (he a) (tv' a)).1
      ((Q ((S.r * S.N) • χ + q.y) : ℚ) / ((S.r * S.N) ^ 2 : ℕ)) fun χ' =>
        div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _))
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ hsc] at b
    refine b.trans (le_of_eq ?_)
    rw [hq]
    push_cast
    rw [mul_div_assoc]
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := ((key q _ hq₁).1 _ _ (he a) (tv' a)).2 ((nz a).2 ha)
    exact hq₂.trans ((QuotientAddGroup.eq_zero_iff _).2 ⟨z, hz.symm⟩)
  · obtain ⟨q, hq₁, hq₂⟩ := ex a
    obtain ⟨z, hz⟩ := (QuotientAddGroup.eq_zero_iff _).1 (hq₂.symm.trans ha)
    have hz' : (S.r * S.N) • z = q.y := hz
    letI := gtGroup (D := u.D.toPre) (F := PadicAlgCl p)
    let iota : u.D.toPre.X →+ GtPtF u.D.toPre (PadicAlgCl p) :=
      AddMonoidHom.mk' (fun x => (exists_iota (F := PadicAlgCl p) hB x).choose) fun x x' => by
        obtain ⟨b, v⟩ := (isIota_iff_val _ _).1 (exists_iota (F := PadicAlgCl p) hB x).choose_spec
        obtain ⟨b', v'⟩ := (isIota_iff_val _ _).1 (exists_iota (F := PadicAlgCl p) hB x').choose_spec
        obtain ⟨b'', v''⟩ := (isIota_iff_val _ _).1 (exists_iota (F := PadicAlgCl p) hB (x + x')).choose_spec
        refine (isAdd_iff_eq _ _ _).1 ((isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
        have C : IsCub (ReciprocityTheory.ChartRestriction.G.DVR.th u.D.toPre (T := TF (R := u.V) (PadicAlgCl p)) y J) := isCub_cubV u.D.toPre.cub hJ
        rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', C.s01, C.s12]
        exact tau_mul (𝟙 (TF (R := u.V) (PadicAlgCl p))) hJ hB x x' χ
    have iota_spec (x : u.D.toPre.X) : GtPtF.IsIota x (iota x) := (exists_iota hB x).choose_spec
    have iota_iff (x : u.D.toPre.X) (g : GtPtF u.D.toPre (PadicAlgCl p)) : GtPtF.IsIota x g ↔ g = iota x :=
      ⟨fun h => isIota_unique h (iota_spec x), fun h => h ▸ iota_spec x⟩
    have q_nsmul : (S.r * S.N) • q.g = iota q.y := by
      obtain ⟨_, h₁, h₂⟩ := q.eq
      exact ((isNsmul_iff_eq _ _ _).1 h₁).symm.trans ((iota_iff _ _).1 h₂)
    let g₀ := q.g + iota (-z)
    have hg₀ : (S.r * S.N) • g₀ = iota 0 := by
      dsimp [g₀]
      rw [smul_add, q_nsmul, ← map_nsmul, ← map_add (f := _), smul_neg, hz', add_neg_cancel]
    let q₀ : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N) :=
      ⟨0, g₀, _, (isNsmul_iff_eq _ _ _).2 rfl, (iota_iff _ _).2 hg₀⟩
    have e₀ : f q = f q₀ := (f₃ _ _).2 ⟨-z, by
      change 0 = q.y + (S.r * S.N) • (-z)
      rw [smul_neg, hz', add_neg_cancel], _, iota_spec _, (isAdd_iff_eq _ _ _).2 rfl⟩
    obtain ⟨q', x', hy', hx', hpow, hval⟩ := (key q₀ (x a) ((f₁ _ _).2 (((f₁ _ _).1 hq₁).trans e₀))).2 n hn hnm (by simp [q₀])
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    have := u.A.isAb.comm
    let X : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
      MonoidHom.mk' (fun a => x a.toAdd) fun a b => xadd _ _
    refine ⟨a', (l.yy_eq a' q' _ hx' (hx a')).trans (by rw [hy']; rfl), xinj ?_, (nz a').1 (hval _ _ (he a') (tv' a'))⟩
    have b : X ((Multiplicative.ofAdd a' * (Multiplicative.ofAdd a)⁻¹) ^ n) = X 1 := by
      rw [map_pow, map_mul, map_inv, map_one]; exact hpow
    rw [sub_eq_add_neg]
    exact b

theorem norm_le_delta {p : ℕ} [Fact p.Prime] (ρ : S.Real) (y₀ : S.R →+* PadicAlgCl p) (a : S.Gam) :
    ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ S.delta y₀ := by
  have : NeZero (S.r * S.N) := ⟨(odd_level ρ).pos.ne'⟩
  exact le_ciSup (f := fun x => ‖y₀ ⟨S.th x, S.th_mem x⟩‖) (Set.finite_range _).bddAbove a

theorem main : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
  intro hL hL₂ _ o Ω _ _ _ _ S ρ p _ y₀ u l h a _
  obtain ⟨sc, -, h₁, -, h₃⟩ := exists_scale hL hL₂ u l h
  have h2 : 2 ≤ S.r * S.N := S.N_ge.trans (Nat.le_mul_of_pos_left _ S.r_pos)
  obtain ⟨a', -, -, ha'⟩ := h₃ _ h2 dvd_rfl 0 (zero_mem _)
  obtain ⟨w, hw, b⟩ := h₁ a
  exact ⟨w, hw, b.trans (mul_le_mul_of_nonneg_right (ha' ▸ norm_le_delta ρ y₀ a') (Real.exp_pos _).le)⟩

end GlobalTheory.ZH.TestVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantBoundedByShortestVectorStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_bounded_by_shortestVector : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ x, y₀ ⟨S.th x, S.th_mem x⟩ ≠ 0 → ∃ w : u.D.toPre.X, l.yy x = QuotientAddGroup.mk w ∧ ‖y₀ ⟨S.th x, S.th_mem x⟩‖ ≤ S.delta y₀ * Real.exp (-(l.q w / ((S.r * S.N : ℕ) : ℝ) ^ 2))) := by
  first | exact @GlobalTheory.ZH.TestVal.main | exact GlobalTheory.ZH.TestVal.main | (intros; apply GlobalTheory.ZH.TestVal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImage
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImage
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

namespace GlobalTheory

theorem isAdmissibleCompleteLocalDomainPrime_maximalIdeal (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R]
    (h₁ : IsNoetherianRing R) (h₂ : IsIntegrallyClosed R) (h₃ : IsAdicComplete (IsLocalRing.maximalIdeal R) R) :
    admitted R (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨h₁, inferInstance, h₂, h₃⟩, h₃, inferInstance, (IsLocalRing.maximalIdeal.isMaximal R).isPrime, ?_⟩
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  infer_instance

theorem model_uniformisation_of_clauses : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Y.N3 := by
  intro hL hL2 hL3 hL4 hL5 hE hU hP E _ _ _ H D l Xo c W₀ Y p hN R _ _ _ _ hR₁ hR₂ hR₃ ξ t ht hne hsp
  obtain ⟨-, hpol, hloc⟩ := T.generic_point_mem_moduli_of_meets_abelian_locus hL hL2 E H D l Xo c W₀ Y p hN R ξ t ht hne
  have hθ : ThetaNZ t.G t.PP.L := T.fibrewise_nonvanishing_of_invertible_pushforward E H Y.X Y.t hN.2.2.1 R ξ t ht
  have hadm : admitted R (IsLocalRing.maximalIdeal R) := isAdmissibleCompleteLocalDomainPrime_maximalIdeal R hR₁ hR₂ hR₃
  let _ : Field (R ⧸ IsLocalRing.maximalIdeal R) := Ideal.Quotient.field _
  have hpid : IsPrincipalIdealRing (R ⧸ IsLocalRing.maximalIdeal R) := inferInstance
  have hsplit : SplitOver t.G (IsLocalRing.maximalIdeal R) := hsp
  obtain ⟨P, hP'⟩ := T.exists_uniformisation_complete_local_normal_prime hL hL2 hL3 hL4 hL5 hE hU hP E H R _ hadm hpid t hpol hsplit hθ
  have hopen : IsOpen (abLocus t.G) := by
    obtain ⟨U, hU', -⟩ := hN.2.2.2.1
    rw [← hloc, ← hU']
    exact U.isOpen.preimage ξ.continuous
  refine ⟨P, ?_, hP'⟩
  rw [hloc]
  exact T.pelTrivialisation_isUnit_on_abelianLocus hL hL2 hL3 hL4 hL5 E H R _ hadm t P hP' hopen

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelUniformisationOfAbelianLocusDirectImageStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_uniformisation_of_abelianLocus_directImage : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Ega → USt → PelSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (p : ℕ), Y.LevelStructureConditions p → Y.N3 := by
  first | exact @GlobalTheory.model_uniformisation_of_clauses | exact GlobalTheory.model_uniformisation_of_clauses | (intros; apply GlobalTheory.model_uniformisation_of_clauses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingForm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.PerpCharacter
open GlobalTheory.ZH.TorusPerp GlobalTheory.ZH.PerpTorus

theorem exists_torus_point_eStd : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → (∀ a b, x (a + b) = x a * x b) → (∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a) → ∀ t ∈ S.perp l.yy.ker, ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), pk.y = 0 ∧ IsTor τ pk.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk (x t) ∧ ∀ (a : S.Gam) (α : u.D.toPre.X), l.yy a = QuotientAddGroup.mk α → (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ t a).val))) := by
  intro hL hT o Ω _ _ _ hA S ρ p _ y₀ u l x hx hadd hsurj a ha
  have hG := hL.1.globalFns
  have hN := S.N_ge
  have hr := S.r_pos
  have hn : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : IsDomain o := hA.inj.isDomain _
  have : CharZero u.V := RingHom.charZero
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V)))
  have := ρ.P.isAb.comm
  have hB := u.D.tau_bimult
  obtain ⟨f, f₁, f₂, -, -, f₅⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn.pos

  have hζ : IsPrimitiveRoot (S.ζ ^ (S.r * S.N)) (S.r * S.N) := S.prim.pow (pow_pos hn.pos 2) (pow_two _)
  let c₀ : (S.R)ˣ := Units.map (algebraMap o S.R).toMonoidHom (hζ.isUnit hn.ne).unit
  let ω : (PadicAlgCl p)ˣ := Units.map y₀.toMonoidHom c₀
  have hωv : (ω : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N))) := rfl
  have hω : IsPrimitiveRoot ω (S.r * S.N) := by
    have : NeZero ((S.r * S.N : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hn.ne⟩
    rw [← IsPrimitiveRoot.coe_units_iff, ← Polynomial.isRoot_cyclotomic_iff,
      ← Polynomial.map_cyclotomic _ (y₀.comp (algebraMap o S.R))]
    exact Polynomial.IsRoot.map (y₀.comp (algebraMap o S.R)) (hζ.isRoot_cyclotomic hn.pos)

  have hy : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ :=
    (Spec.map_comp _ _).symm.trans (congrArg spMap u.fac)
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) (by simp)
  have hh : h.left = spMap y₀ := hy
  let Φ := ptHom u.cart (TFK (R := u.V) (PadicAlgCl p))
  have hΦ : ∀ b, Φ (x b) = h ≫ ρ.pt b := fun b => Over.OverMorphism.ext ((hx b).trans (by rw [← hh]; rfl))
  have weil : ∀ b b', WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x b) (x b') (unitOn (ω ^ (eStd S.g _ b b').val)) :=
    fun b b' => by
    have w := GlobalTheory.CommPairing.weilIs_pull hG ρ.P.isAb ρ.P.isLB h (ρ.weil b b' (c₀ ^ (eStd S.g _ b b').val) (by
      rw [pow_mul, map_pow]; rfl))
    rw [← hΦ, ← hΦ] at w
    refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ ρ.P.isLB u.A.isLB u.cart u.lb _ _ _ _
      (Φ (x b)) (Φ (x b')) _ rfl rfl).2 ?_
    convert w using 1
    rw [← map_pow, ← map_unitOn, ← hh]
  let pt : Multiplicative S.Gam →* (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) :=
    MonoidHom.mk' (fun a => x a.toAdd) fun _ _ => hadd _ _
  have pt_nsmul : ∀ (n : ℕ) b, x (n • b) = x b ^ n := fun n b => map_pow pt (Multiplicative.ofAdd b) n
  have onto : ∀ b, ∃ q, f q = x b := fun b => f₂ _ (by
    rw [← pt_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self, zero_smul]
    exact map_one pt)
  obtain ⟨m, hm⟩ := exists_form S l.yy l.yy_onto a ha
  let τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ :=
    (AddChar.zmodChar (S.r * S.N) hω.pow_eq_one).toMonoidHom.comp m.toMultiplicative
  have hτ : ∀ α, τ (Multiplicative.ofAdd α) = ω ^ (m α).val := fun _ => rfl
  have hτ1 : τ ^ (S.r * S.N) = 1 := MonoidHom.ext fun α => by
    show (ω ^ (m α.toAdd).val) ^ (S.r * S.N) = 1
    rw [pow_right_comm, hω.pow_eq_one, one_pow]
  obtain ⟨q, hq, hqτ⟩ := exists_qkPt_tor (F := PadicAlgCl p) hB τ hτ1
  have hq1 : f q ^ (S.r * S.N) = 1 := by
    obtain ⟨w, hw⟩ := u.U.ext
    exact ((f₁ _ _).2 rfl w hw).1
  obtain ⟨a', ha'⟩ := hsurj (f q) hq1
  have haa : a' = a := by
    rw [← sub_eq_zero]
    refine eq_zero_of_eStd _ _ _ fun b => ?_
    obtain ⟨q', hq'⟩ := onto b
    have w₁ := (f₅ q q' _).1 (weilQkIs_tor hG q q' hq hqτ)
    rw [ha', hq'] at w₁
    have e₁ := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG u.A.isAb u.A.isLB (weil a' b) w₁)
    rw [hτ] at e₁
    have e₂ := ZMod.val_injective _ (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) e₁)
    rw [hm b _ (l.yy_eq b q' _ ((f₁ _ _).2 hq'.symm) (hx b))] at e₂
    have e₃ := eStd_add_left S.g _ (a' - a) a b
    rw [sub_add_cancel, e₂] at e₃
    exact left_eq_add.1 (e₃.trans (add_comm _ _))
  subst haa
  refine ⟨q, τ, hq, hqτ, (f₁ _ _).2 ha'.symm, fun b α e => ?_⟩
  rw [hτ, hm b α e, Units.val_pow_eq_pow_val, hωv, ← map_pow, ← map_pow, ← pow_mul]

end GlobalTheory.ZH.PerpCharacter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingFormStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_torsionPoint_standardAlternatingForm : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → (∀ a b, x (a + b) = x a * x b) → (∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a) → ∀ t ∈ S.perp l.yy.ker, ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), pk.y = 0 ∧ IsTor τ pk.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk (x t) ∧ ∀ (a : S.Gam) (α : u.D.toPre.X), l.yy a = QuotientAddGroup.mk α → (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ t a).val))) := by
  first | exact @GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd | exact GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd | (intros; apply GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTrait
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Rig
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {A : Over S'} [GrpObj A] [IsCommMonObj A]

theorem rigidification_map_on_values (m : CubeMap A G) {L₀ : LB G.left} {L₁ : LB A.left} (w : LB.Iso L₁ (L₀.pull m.F))
    {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}
    (h : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec A) (fun _ => 1)) ρ₁ (m.rigPull L₀ ρ₀)) :
    IsRigidificationPullbackCompatibleIso w m.e ρ₁ ρ₀ := by
  have H := (maps_iff w _ (fun _ => eSec G) _ ρ₁ ρ₀ m.e _ (rigPull_le m.F m.e m.e_comm L₀) (fun _ => rfl)).1 h
  intro Z r z J J' hJ hJ'
  have e : (r ≫ m.e) ≫ eSec G = (r ≫ eSec A) ≫ m.F := by rw [Category.assoc, Category.assoc, m.e_comm]
  refine (val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ m.e) z J
    (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => congrArg J e)).trans ?_
  refine (H Z r z (fun _ => J ((r ≫ eSec A) ≫ m.F)) (fun _ => J' (r ≫ eSec A)) (fun _ => hJ _) (fun _ => hJ' _)).trans ?_
  rw [Fintype.prod_unique, zpow_one]
  rfl

end Rig

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}

theorem mem_nonzeroLocus_iff_sv {a : ℤ} (s : LB.Sec (LPow A L₁ a T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    {J} (hJ : Good L₁ z J) : r z ∈ nonzeroLocus s ↔ IsUnit (VVRank.sv A s r z J) := by
  have hz := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  constructor
  · intro h
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
    have hz' : r z ∈ (LPow A L₁ a T).U k := (T ⊗ A).left.basicOpen_le _ hk
    have hu := (MulFinite.isUnit_gs r z _ hz' _).2 hk
    have e := sec_trans (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z hz' hz
    exact isUnit_of_mul_isUnit_right (e ▸ hu :)
  · intro h
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨_, (MulFinite.isUnit_gs r z _ hz _).1 h⟩

theorem SecRel.mem_nonzeroLocus (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {a : ℤ} {s : LB.Sec (LPow A L₁ a T)}
    {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀) (y : (T ⊗ A).left)
    (hy : psi hp τ hτ y ∈ nonzeroLocus s₀) : y ∈ nonzeroLocus s := by
  obtain ⟨J, hJ⟩ := exists_good' hL₀ y
  obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
  have q := (mem_nonzeroLocus_iff_sv s₀ (𝟙 _ ≫ psi hp τ hτ) y hJ).1 hy
  rw [h _ _ _ _ _ hJ hJ'] at q
  exact (mem_nonzeroLocus_iff_sv s (𝟙 _) y hJ').2 (isUnit_of_mul_isUnit_right q)

theorem SecRel.pullS {a : ℤ} {s : LB.Sec (LPow A L₁ a T)} {s₀ : LB.Sec (LPow G L₀ a T₀)} (h : SecRel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (τ' : T'.left ⟶ T₀'.left) (hτ' : τ' ≫ T₀'.hom = T'.hom ≫ f) (ξ : T' ⟶ T)
    (ξ₀ : T₀' ⟶ T₀) (e : τ' ≫ ξ₀.left = ξ.left ≫ τ) :
    SecRel hp τ' hτ' w (VVRank.pullS A a ξ s) (VVRank.pullS G a ξ₀ s₀) := by
  intro Z r z J J' hJ hJ'
  have e' : psi hp τ' hτ' ≫ (ξ₀ ▷ G).left = (ξ ▷ A).left ≫ psi hp τ hτ := by
    refine psi_ext ?_ ?_
    · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
        Category.assoc, Category.assoc, psi_fst', e, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
        ← Over.comp_left, whiskerRight_fst]
    · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
        VVRank.whisker_snd_left]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, VVRank.sv_pullS _ _ _ _ _ _ hJ', Category.assoc, e', ← Category.assoc,
    h _ _ _ _ _ hJ hJ', Category.assoc, VVRank.whisker_snd_left]


include hp hτ in
theorem exists_pt_down (x₀ : T₀ ⟶ G) {n : ℕ} (hn : x₀ ^ n = 1) :
    ∃ x : T ⟶ A, τ ≫ x₀.left = x.left ≫ φ ∧ x ^ n = 1 := by
  have hc : (τ ≫ x₀.left) ≫ G.hom = T.hom ≫ f := by rw [Category.assoc, Over.w, hτ]
  let x : T ⟶ A := Over.homMk (hp.1.lift _ _ hc) (hp.1.lift_snd _ _ hc)
  have hx : τ ≫ x₀.left = x.left ≫ φ := (hp.1.lift_fst _ _ hc).symm
  refine ⟨x, hx, Over.OverMorphism.ext (hp.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))⟩
  rw [← over_pow hp τ hτ hx n, hn, over_one hp τ hτ]


include hp hτ in
theorem exists_pt_up [IsIso τ] (x : T ⟶ A) {n : ℕ} (hn : x ^ n = 1) :
    ∃ x₀ : T₀ ⟶ G, τ ≫ x₀.left = x.left ≫ φ ∧ x₀ ^ n = 1 := by
  let x₀ : T₀ ⟶ G := Over.homMk (inv τ ≫ x.left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hp.1.w, Over.w_assoc, ← hτ, IsIso.inv_hom_id_assoc])
  have hx : τ ≫ x₀.left = x.left ≫ φ := IsIso.hom_inv_id_assoc _ _
  refine ⟨x₀, hx, Over.OverMorphism.ext ((cancel_epi τ).1 ?_)⟩
  rw [over_pow hp τ hτ hx n, hn, over_one hp τ hτ]

end Move

theorem theta_at_trait : HV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)) (_ : SABMap t' t χ) (_ : PELUnif (maximalIdeal V) t') (σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ))), NZ t.G t.PP.L χ σ → IsGenSec t.G t.PP.L ((1 : ℕ) : ℤ) σ ∧ ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (x' : Sp F ⟶ S) (ξ : Over.mk x' ⟶ Over.mk χ), ξ.left = jFK (R := V) F ≫ jK V → (∀ x (c : F), ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hV E _ _ _ H S t V _ _ _ hC χ t' m P σ hσ
  obtain ⟨hD, hA, hZ⟩ := hC
  obtain ⟨w, hw, hr, -⟩ := m.lin
  have hR : IsRigidificationPullbackCompatibleIso w χ t'.PP.rig t.PP.rig := by
    have q := rigidification_map_on_values m.cm w hr
    rw [m.base] at q
    exact q
  have hp := m.cart
  have hL₀ := t.PP.isLB
  have hL₁ := t'.PP.isLB
  let τ : (Over.mk (𝟙 (Sp V))).left ⟶ (Over.mk χ).left := 𝟙 (Sp V)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp V)))
  have hτ : τ ≫ (Over.mk χ).hom = (Over.mk (𝟙 (Sp V))).hom ≫ χ := rfl
  obtain ⟨σ', hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ σ
  have hσ' : NZ t'.G t'.PP.L (𝟙 (Sp V)) σ' := by
    obtain ⟨g, hg, hg'⟩ := hσ
    obtain ⟨κ, -, h₂⟩ := ThetaPtUp.exists_psi_inv' hp τ hτ
    have e : psi hp τ hτ (κ g) = g := congrArg (fun q => q g) h₂
    refine ⟨κ g, ?_, SecRel.mem_nonzeroLocus hp τ hτ hL₀ hL₁ hs _ (e.symm ▸ hg')⟩
    have e' := congrArg (fun q => q (κ g)) (psi_fst' hp τ hτ)
    exact e'.symm.trans ((congrArg (fst (Over.mk χ) t.G).left e).trans hg)
  have key : ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F]
      (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → IsGenSec t'.G t'.PP.L ((1 : ℕ) : ℤ) σ' ∧ ∀ n : ℕ, Odd n →
      IsUnit (n : V) → 3 ≤ n → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))),
      (∀ x (c : F), ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) → 0 ≤ v c) ∧
      ∃ x, ∃ c : F, ThG t'.G t'.PP.L t'.PP.rig n (VVRank.pullS t'.G _ ξ σ') x (fnOf c) ∧ v c = 0 := by
    intro ϖ hϖ F _ _ _ v hv
    choose Q hQ using QForm.exists_QVal hϖ P.D
    have q := GlobalTheory.T.thetaConstants_integral_unit_of_closedFibre_nonvanishing hV V hA ϖ hϖ P.D Q hQ F v hv P.A t'.G t'.semi P.U
    dsimp only at q
    rw [P.bundle] at q
    exact q σ' hσ'
  refine ⟨?_, fun ϖ hϖ F _ _ _ v hv n h₁ h₂ h₃ x' ξ hξ => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
    obtain ⟨v, hv⟩ := GlobalTheory.adic_base_embeds_valuation_algebraic_closure.2 V ϖ hϖ
    exact ThetaPtUp.isGenSec_up hp τ hτ hw hL₀ hL₁ hs (key ϖ hϖ _ v hv).1
  · let ξ' : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V)) :=
      Over.homMk (jFK (R := V) F ≫ jK V) (Category.comp_id _)
    obtain ⟨k₁, x, c, k₂, k₃⟩ := (key ϖ hϖ F v hv).2 n h₁ h₂ h₃ ξ'
    let τ' : (Over.mk (jFK (R := V) F ≫ jK V)).left ⟶ (Over.mk x').left := 𝟙 (Sp F)
    haveI : IsIso τ' := inferInstanceAs (IsIso (𝟙 (Sp F)))
    have hτ' : τ' ≫ (Over.mk x').hom = (Over.mk (jFK (R := V) F ≫ jK V)).hom ≫ χ :=
      (Category.id_comp _).trans ((Over.w ξ).symm.trans (congrArg (· ≫ χ) hξ))
    have hs' := SecRel.pullS hp τ hτ hs τ' hτ' ξ' ξ
      ((Category.id_comp _).trans (hξ.trans (Category.comp_id _).symm))
    have hi : inv τ' = 𝟙 (Sp F) := IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    refine ⟨fun y₀ d hd => ?_, ?_⟩
    · obtain ⟨y, hy, hn⟩ := exists_pt_down hp τ' hτ' y₀ hd.1
      exact k₁ y d (ThG.move hp τ' hτ' hw hL₀ hL₁ hR hy hn hs' hd)
    · obtain ⟨x₀, hx, hn⟩ := exists_pt_up hp τ' hτ' x k₂.1
      have q := ThG.up hp τ' hτ' hw hL₀ hL₁ hR hx hn hs' k₂
      rw [hi] at q
      exact ⟨x₀, c, q, k₃⟩

end GlobalTheory.Ex.OneGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsAtUniformisedTraitStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constants_at_uniformised_trait : HV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (χ : Sp V ⟶ S) (t' : SAB H (Sp V)) (_ : SABMap t' t χ) (_ : PELUnif (maximalIdeal V) t') (σ : LB.Sec (LPow t.G t.PP.L ((1 : ℕ) : ℤ) (Over.mk χ))), NZ t.G t.PP.L χ σ → IsGenSec t.G t.PP.L ((1 : ℕ) : ℤ) σ ∧ ∀ (ϖ : V), Irreducible ϖ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (x' : Sp F ⟶ S) (ξ : Over.mk x' ⟶ Over.mk χ), ξ.left = jFK (R := V) F ≫ jK V → (∀ x (c : F), ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG t.G t.PP.L t.PP.rig m (VVRank.pullS t.G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  first | exact @GlobalTheory.Ex.OneGen.theta_at_trait | exact GlobalTheory.Ex.OneGen.theta_at_trait | (intros; apply GlobalTheory.Ex.OneGen.theta_at_trait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormThetaConstantLePrimitiveGeneratorScale
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormThetaConstantLePrimitiveGeneratorScale
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.ThetaBound

theorem le_of_sum {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨T, hT⟩ := h q
  have := v.map_le_add (hT T le_rfl) (v.map_le_sum (s := T) fun i _ => hq i)
  rwa [sub_add_cancel] at this

theorem square_nonneg {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    {D : DegData V (IsLocalRing.maximalIdeal V)} {Q : D.toPre.X → ℤ} (hϖ : Irreducible ϖ)
    (hQ : QForm.IsQ D.toPre ϖ Q) (n : ℕ) (hn : 1 ≤ n) (y χ : D.toPre.X) :
    (0 : ℚ) ≤ 0 + (Q χ : ℚ) / (1 : ℕ) + (QForm.bOf D.toPre Q y χ : ℚ) / n + (Q y : ℚ) / (n : ℚ) ^ 2 := by
  have h0 : 0 ≤ Q (n • χ + y) := by
    by_cases h : n • χ + y = 0
    · rw [h, QForm.Q_zero hϖ D hQ]
    · exact le_trans zero_le_one (QForm.Q_pos hϖ D hQ h)
  have e : Q (n • χ + y) = n ^ 2 * Q χ + n * QForm.bOf D.toPre Q y χ + Q y := by
    have e₁ : Q (n • χ + y) = Q (n • χ) + Q y + QForm.bOf D.toPre Q (n • χ) y := by
      simp only [QForm.bOf]; ring
    have e₂ : QForm.bOf D.toPre Q χ y = QForm.bOf D.toPre Q y χ := by
      simp only [QForm.bOf, add_comm χ y]; ring
    rw [e₁, DVR.Q_nsmul hϖ hQ, DVR.bOf_nsmul_left hϖ hQ, e₂]; ring
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have h1 : (0 : ℚ) ≤ (n : ℚ) ^ 2 * Q χ + n * (QForm.bOf D.toPre Q y χ : ℚ) + Q y := by
    rw [e] at h0; exact_mod_cast h0
  have e₃ : 0 + (Q χ : ℚ) / (1 : ℕ) + (QForm.bOf D.toPre Q y χ : ℚ) / n + (Q y : ℚ) / (n : ℚ) ^ 2 =
      ((n : ℚ) ^ 2 * Q χ + n * (QForm.bOf D.toPre Q y χ : ℚ) + Q y) / (n : ℚ) ^ 2 := by
    field_simp
    push_cast
    ring
  rw [e₃]
  positivity

theorem norm_theta_le : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → ∀ a, ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ ‖c‖ := by
  intro hL hL₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l _ x rig e th s _ hS ϖ Q v lam hϖ hv hN w₀ th' ϑ c hW hE hP hc a
  obtain ⟨-, htf, hth, -⟩ := hS
  obtain ⟨-, hQ, -, hle, -⟩ := hN
  obtain ⟨hLL, h₁, h₂, h₃, h₄⟩ := laws_all hL hL₂
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hn : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos (le_trans one_le_two S.N_ge)
  obtain ⟨f, hf, hsurj, -⟩ := hT u.V u.complete u.A u.G u.D u.U (PadicAlgCl p) (S.r * S.N) hn
  obtain ⟨q, hq⟩ := hsurj (x a) (htf a).1
  have hqx := (hf q (x a)).2 hq.symm
  obtain ⟨-, hmul, huniq, hex⟩ := GlobalTheory.TestFibre.CombValue.valIs_linear hL u.V u.A (PadicAlgCl p) 1 (x a) (e a)
  obtain ⟨c', hc'⟩ := hex (htf a).2.1 th'
  have hval : y₀ ⟨S.th a, S.th_mem a⟩ = c * c' := huniq th _ _ (hth a) (hmul th' th c c' hc hc')
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hLL h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv
    u.A u.G u.semi u.U w₀ rig hW (S.r * S.N) hn q (x a) hqx (e a) (htf a)
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hLL h₁ h₂ h₃ h₄ u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv q.g
  have hsv := hsum 1 le_rfl w₁ ⟨hw₁, fun z J _ => (pow_one _).symm⟩ th' ϑ c' hE hc'
  have h0 : ((0 : ℚ) : WithTop ℚ) ≤ v c' := le_of_sum hsv fun χ =>
    le_trans (WithTop.coe_le_coe.2 (square_nonneg hϖ hQ (S.r * S.N) hn q.y χ))
      ((hterm 1 le_rfl w₁ ϑ hw₁).2 _ _ 0 (hqk _ hn q) hv₁ hP.1 χ)
  have h1 : ‖c'‖ ≤ 1 := by simpa using (hle c' 0).1 h0
  rw [hval, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end GlobalTheory.ThetaBound
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormThetaConstantLePrimitiveGeneratorScaleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_thetaConstant_le_primitiveGenerator_scale : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → ∀ a, ‖y₀ ⟨S.th a, S.th_mem a⟩‖ ≤ ‖c‖ := by
  first | exact @GlobalTheory.ThetaBound.norm_theta_le | exact GlobalTheory.ThetaBound.norm_theta_le | (intros; apply GlobalTheory.ThetaBound.norm_theta_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitValue
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.SecValue
open GlobalTheory.UT.CoefBasic

theorem exists_pow {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ} (n : ℕ)
    (h : ε' = fun i => (n : ℤ) * ε i) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε'), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), val t' r z J = val t r z J ^ n := by
  subst h
  exact ⟨GeneratorPullback.powGen L φ ε t n, powGen_isGen L φ ε t ht n, fun _ _ _ _ => map_pow _ _ _⟩

theorem line_exp (k : ℕ) : DegPre.lineε k = fun i => (k : ℤ) * DegPre.lineε 1 i := by
  funext i
  fin_cases i <;> simp [DegPre.lineε]

theorem le_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (hq : ∀ i, (q : WithTop ℚ) ≤ v (x i)) : (q : WithTop ℚ) ≤ v s := by
  obtain ⟨S, hS⟩ := h q
  have := v.map_le_add (hS S le_rfl) (v.map_le_sum (s := S) fun i _ => hq i)
  rwa [sub_add_cancel] at this

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {hϖ : Irreducible ϖ}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)} {hv : ValOver ϖ F v}
  {X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ X)}

theorem genV_pow {ε ε' : K → ℤ} (n : ℕ) (h : ε' = fun i => (n : ℤ) * ε i) {t : LB.Gen (LB.LinComb L φ ε)}
    {t' : LB.Gen (LB.LinComb L φ ε')} (ht : GenV hϖ hv t 0)
    (e : ∀ z J, Good L z J → val t' (𝟙 _) z J = val t (𝟙 _) z J ^ n) : GenV hϖ hv t' 0 := by
  obtain ⟨φ₀, hφ, t₀, ht₀, x, hx, hval⟩ := ht
  obtain ⟨t₁, ht₁, hv₁⟩ := exists_pow n h t₀ ht₀
  refine ⟨φ₀, hφ, t₁, ht₁, x ^ n, ?_, fun z J hJ => ?_⟩
  · rw [v.map_pow, hx]; simp
  · rw [e z J hJ, hv₁, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hval z J hJ, mul_pow, cst_eq, cst_eq, map_pow]

end

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

abbrev kon (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem kon_surj : Function.Surjective (kon R F) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2

theorem isComb_iff {J : Type} [Fintype J] (t : J → SecA A F k) (b : J → F) (σ : SecA A F k) :
    IsComb t b σ ↔ SecM.ofSec A.A σ = ∑ l, kon R F (b l) • SecM.ofSec A.A (t l) := by
  rw [Subtype.ext_iff, funext_iff, Submodule.coe_sum]
  refine forall_congr' fun j => ?_
  rw [Finset.sum_apply]
  rfl

def ValM (σ : SecM A.A A.L k (TFK (R := R) F)) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : Prop :=
  ValAt (SecM.toSec A.A σ) x e c

theorem ValM.add {σ σ' : SecM A.A A.L k (TFK (R := R) F)} {x e} {c c' : F} (h : ValM σ x e c) (h' : ValM σ' x e c') :
    ValM (σ + σ') x e (c + c') := fun z J hJ => by
  refine (ThetaAct.sv_add σ σ' _ z hJ).trans ((congrArg₂ (· + ·) (h z J hJ) (h' z J hJ)).trans ?_)
  simp only [id, cst_eq, map_add (f := _)]
  exact (add_mul (R := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm

theorem ValM.smul {σ : SecM A.A A.L k (TFK (R := R) F)} {x e} {c : F} (h : ValM σ x e c) (b : F) :
    ValM (kon R F b • σ) x e (b * c) := fun z J hJ => by
  refine (ThetaAct.sv_smul _ σ _ z hJ).trans ?_
  rw [ThetaPtMove.ptSecT_fst]
  refine (congrArg (@id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z b) * ·) (h z J hJ)).trans ?_
  simp only [id, cst_eq, map_mul]
  exact (_root_.mul_assoc (G := (TFK (R := R) F).left.presheaf.stalk z) _ _ _).symm

theorem ValM.unique {σ : SecM A.A A.L k (TFK (R := R) F)} {x e} {c c' : F} (h : ValM σ x e c) (h' : ValM σ x e c') :
    c = c' := by
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  have := (Units.mul_left_inj _).1 ((h z J hJ).symm.trans (h' z J hJ))
  simp only [id, cst_eq] at this
  exact cstH_inj z this

theorem ValM.exists (hL : Laws) (σ : SecM A.A A.L k (TFK (R := R) F)) {x} {e : FrAt x} (he : e.IsGen) :
    ∃ c, ValM σ x e c := by
  obtain ⟨w, hw, -⟩ := hL.evVal _ A k x e he (SecM.toSec A.A σ)
  obtain ⟨c, rfl⟩ := kon_surj w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

theorem ValM.sum (hL : Laws) {x} {e : FrAt x} (he : e.IsGen) {J : Type} (s : Finset J)
    {σ : J → SecM A.A A.L k (TFK (R := R) F)} {c : J → F} (h : ∀ l, ValM (σ l) x e (c l)) :
    ValM (∑ l ∈ s, σ l) x e (∑ l ∈ s, c l) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨c, hc⟩ := ValM.exists hL (0 : SecM A.A A.L k (TFK (R := R) F)) he
    have := hc.smul 0
    rw [smul_zero, zero_mul] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

end

theorem val_sum_eq_zero {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) (i₀ : Ix) (h₀ : v (x i₀) = 0) {q : ℚ} (hq : 0 < q)
    (hx : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  obtain ⟨S, hS⟩ := h q
  have a := hS (insert i₀ S) (Finset.subset_insert _ _)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self i₀ S)] at a
  have b := v.map_le_add a (v.map_le_sum (s := (insert i₀ S).erase i₀) fun i hi => hx i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - (x i₀ + ∑ i ∈ (insert i₀ S).erase i₀, x i) + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by ring
  rw [e, v.map_add_eq_of_lt_left, h₀]
  rw [h₀]
  exact lt_of_lt_of_le (WithTop.coe_lt_coe.2 hq) b

theorem exists_unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (n k : ℕ), 1 ≤ n → 4 ≤ k → ∀ (p : QkPt D.toPre F n) x, p.y = 0 → QkToAkU U.toUnifPre F n p x → ∀ e, IsTorsFrame A ρ n x e → ∃ s : Fam D.toPre F k, NuGe D Q F v k s 0 ∧ (∀ β, (∀ z : D.toPre.X, β ≠ k • z) → ∀ j, (s.s β).f j = 0) ∧ ∀ (t : SecA A F k) (c : F), U.ExpandsF F k w₀ t s → ValAt t x e c → v c = 0 := by
  intro hL hT hVR hTW hUU V _ _ _ _ hcpl ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN n k hn hk p x hy hx e he
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.UT.TorsionValue.value_at_torsion hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv
    A G hG U w₀ ρ hN n hn p x hx e he
  rw [hy, QForm.Q_zero hϖ D hQ, Int.cast_zero, zero_div] at hv₁
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv p.g
  obtain ⟨w, hw, hwv⟩ := exists_pow k (line_exp k) w₁ hw₁
  have hw0 : GenV hϖ hv w 0 := genV_pow k (line_exp k) hv₁ fun z J _ => hwv _ _ z J
  have b0 : ∀ χ, QForm.bOf D.toPre Q p.y χ = 0 := fun χ => by
    rw [hy, QForm.bOf, zero_add, QForm.Q_zero hϖ D hQ]; ring
  have hg := hqk n hn p
  obtain ⟨s, hν, hsupp, hc₀⟩ := GlobalTheory.UT.CoefUnit.exists_fam_coef_val hL hT hVR hTW hUU V hcpl ϖ hϖ D Q hQ F v hv k hk
    p.g w _ 0 hw hg hw0 0
  refine ⟨s, hν, fun β hβ => hsupp β fun z => by simpa using hβ z, fun t c ht hc => ?_⟩
  have hS : SumV v (coef s p.g w) c := hsum k hk1 w ⟨hw, fun z J _ => hwv _ _ z J⟩ t s c ht hc
  have hk0 : (0 : ℚ) < k := by exact_mod_cast hk1
  refine val_sum_eq_zero hS 0 ?_ (q := 1 / k) (by positivity) fun χ hχ => ?_
  · rw [hc₀, b0, QForm.Q_zero hϖ D hQ]; simp
  · refine le_trans (WithTop.coe_le_coe.2 ?_) ((hterm k hk1 w s hw).2 _ 0 0 hg hw0 hν χ)
    rw [b0]
    have : (1 : ℚ) ≤ Q χ := by exact_mod_cast QForm.Q_pos hϖ D hQ hχ
    simpa using div_le_div_of_nonneg_right this hk0.le

theorem act_fix : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) τ x, p.y = 0 → IsTor τ p.g → QkToAkU U.toUnifPre F N p x → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (t t' : SecA A F N) s, U.ExpandsF F N w₀ t s → (∀ β, τ (Multiplicative.ofAdd β) = 1 ∨ ∀ j, (s.s β).f j = 0) → IsActOf A.A A.L N θ t t' → t' = t := by
  intro hL R _ _ _ I hA D A G _ _ hG U F _ _ _ N hN p τ x hy hτ hx θ hθ w₀ hw₀ t t' s hs hsupp hact
  obtain ⟨hb₁, hb₂⟩ := (GlobalTheory.UT.expBijF_and_expandsF_lin hL R I hA D A G hG U).1 F N hN.pos w₀ hw₀
  obtain ⟨s', hs', -⟩ := hb₁ t'
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL R I hA D F N hN p).1
  have hφ := GlobalTheory.UT.symLift_acts_as_phi hL R I hA D A G hG U F N hN p x hx θ hθ w₀ hw₀ w hw t t' s s' hs hs' hact
  have e := ((GlobalTheory.UT.TorusWeight.torus_weight hL R I hA D A G hG U F N hN p τ hy hτ w hw).2 s s').1 hφ
  obtain rfl : s' = s := fam_ext fun α j => by
    rw [e α j]
    rcases hsupp α with h | h
    · rw [h, Units.val_one, DegPre.constBF, map_one, map_one, map_one, _root_.one_mul]
    · rw [h j, mul_zero]
  exact (hb₂ s').unique hs' hs

end GlobalTheory.ZH.SecValue
end
end
