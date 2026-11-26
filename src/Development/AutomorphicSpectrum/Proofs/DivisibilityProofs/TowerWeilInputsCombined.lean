module

public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestHeightBound
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PBlockRatioAlg
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightTestBound
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT2
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilTheorem
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HodgeComponentFactorPoint
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatement
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem existsUnique_rat (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι :=
  (GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers ℚ K ι).1

end GlobalTheory.CompanionTheory.Ar.Link
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueRationalStatementStatement
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_rational_statement : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ExistsUniqueStatement ℚ ι := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | exact GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.existsUnique_rat <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DivSuppArithHolds
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem divSuppArith_holds : ReciprocityTheory.ChartRestriction.G.Geo.DivSuppArithStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith

end GlobalTheory.CompanionTheory.Ar.Link
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.MeanSlopeOfProportionalVolume
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem mean_slope_of_proportional_volume : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval := by
  intro II Ψ _ _ N T C rd Lval hP hV hT u g hu B hB hB0 hbad
  have hfd : 0 < flagDeg u := (GlobalTheory.T.flag_degree_weight_formula Ψ N u).2.1 hu.2.1
  obtain ⟨c0⟩ := T.neC
  have hv : 0 < T.vol c0 := hP.1 c0
  have hvc : ∀ c, T.vol c = T.vol c0 := fun c => hV c c0
  have hcard : (0:ℝ) < Fintype.card T.Comp := by exact_mod_cast Fintype.card_pos
  have hvolT : T.volT = Fintype.card T.Comp * T.vol c0 := by
    rw [RootTower.volT, Finset.sum_congr rfl fun c _ => hvc c]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hD : (0:ℝ) < (dimFl Ψ N : ℝ) + 1 := by positivity
  have key : (∑ c, T.slope II B c u) / Fintype.card T.Comp
      = T.PB II B u / (((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u)) := by
    have hs : ∀ c, T.slope II B c u
        = T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)) / (((dimFl Ψ N : ℝ) + 1) * (T.vol c0 * flagDeg u)) := by
      intro c
      rw [RootTower.slope, hvc c]
    rw [Finset.sum_congr rfl fun c _ => hs c, ← Finset.sum_div, RootTower.PB, RootTower.PPt, hvolT,
      div_div]
    congr 1
    ring
  have hpos : 0 < ((dimFl Ψ N : ℝ) + 1) * (T.volT * flagDeg u) := by
    rw [hvolT]
    exact mul_pos hD (mul_pos (mul_pos hcard hv) hfd)
  rw [key, le_div_iff₀ hpos]
  have h := hT u g hu B hB hB0 hbad
  linarith

end RootFieldNumerics
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.DegFlSymmetryInvariance
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem pa_relabel_injective {Ψ : Type} {N : ℕ} (σ : Equiv.Perm Ψ) :
    Function.Injective (fun x : Ψ × Fin N => (σ x.1, x.2)) := by
  intro x y hxy
  simp only [Prod.mk.injEq] at hxy
  exact Prod.ext (σ.injective hxy.1) hxy.2

theorem pa_degFl_relabel {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (σ : Equiv.Perm Ψ) (F : RP Ψ N) :
    degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F := by
  have hinj := pa_relabel_injective (N := N) σ
  have hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ =
      Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (permExp (fun t => ρ (σ t))) := by
    intro ρ
    ext ⟨t, i⟩
    have ht : ((t, i) : Ψ × Fin N) = (fun x : Ψ × Fin N => (σ x.1, x.2)) (σ.symm t, i) := by simp
    rw [ht, Finsupp.mapDomain_apply_of_injective hinj]
    simp [permExp]
  unfold degFl
  congr 1
  have hterm : ∀ ρ : Ψ → Equiv.Perm (Fin N),
      (∏ τ, ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ)) *
          (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F).coeff (permExp ρ) =
        (fun ρ' : Ψ → Equiv.Perm (Fin N) =>
          (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ')) (fun t => ρ (σ t)) := by
    intro ρ
    rw [hexp ρ, coeff_rename_mapDomain _ hinj]
    congr 1
    exact (Equiv.prod_comp σ (fun τ => ((Equiv.Perm.sign (ρ τ) : ℤ) : ℝ))).symm
  rw [Finset.sum_congr rfl (fun ρ _ => hterm ρ)]
  exact Equiv.sum_comp (Equiv.arrowCongr σ.symm (Equiv.refl (Equiv.Perm (Fin N))))
    (fun ρ' : Ψ → Equiv.Perm (Fin N) =>
      (∏ τ, ((Equiv.Perm.sign (ρ' τ) : ℤ) : ℝ)) * F.coeff (permExp ρ'))

theorem degFl_symmetry_invariance : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F := by
  intro Ψ _ _ N
  refine ⟨?_, ?_⟩
  · intro τ a b F hab
    have hinv : ∀ x : Ψ × Fin N,
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)
          ((fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) x) = x := by
      rintro ⟨t, i⟩
      by_cases ht : t = τ <;> simp [ht]
    have hinj : Function.Injective
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) := by
      intro x y hxy
      exact (hinv x).symm.trans ((congrArg
        (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) hxy).trans (hinv y))
    have hexp : ∀ ρ : Ψ → Equiv.Perm (Fin N), permExp ρ =
        Finsupp.mapDomain (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x)
          (permExp (ρ * Pi.mulSingle τ (Equiv.swap a b))) := by
      intro ρ
      ext y
      conv_rhs => rw [← hinv y]
      rw [Finsupp.mapDomain_apply_of_injective hinj]
      rcases y with ⟨t, i⟩
      by_cases ht : t = τ
      · subst ht
        simp [permExp]
      · simp [permExp, ht, Pi.mulSingle_apply]
    have hsgn : ∀ ρ : Ψ → Equiv.Perm (Fin N),
        (∏ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ)) =
          -∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) := by
      intro ρ
      have hfac : ∀ t, ((Equiv.Perm.sign ((ρ * Pi.mulSingle τ (Equiv.swap a b) : Ψ → Equiv.Perm (Fin N)) t) : ℤ) : ℝ) =
          ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ) * (if t = τ then -1 else 1) := by
        intro t
        by_cases ht : t = τ
        · subst ht
          simp [Equiv.Perm.sign_swap hab]
        · simp [ht]
      rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_mul_distrib]
      simp
    unfold degFl
    rw [← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    rw [← Equiv.sum_comp (Equiv.mulRight (Pi.mulSingle τ (Equiv.swap a b)))
      (fun ρ => -((∏ t, ((Equiv.Perm.sign (ρ t) : ℤ) : ℝ)) * F.coeff (permExp ρ)))]
    apply Finset.sum_congr rfl
    intro ρ _
    simp only [Equiv.coe_mulRight]
    rw [hexp ρ, coeff_rename_mapDomain _ hinj, hsgn ρ]
    ring
  · intro σ F
    have hinj := pa_relabel_injective (N := N) σ
    refine ⟨pa_degFl_relabel σ F, fun j τ => ⟨?_, ?_⟩⟩
    · unfold Sh
      conv_rhs => rw [← pa_degFl_relabel σ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact pderiv_rename hinj (τ, i) F
    · unfold Tot
      conv_rhs => rw [← pa_degFl_relabel σ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact pderiv_rename hinj (τ, i) F

end RootFieldNumerics
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightI9Properties
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightI9Properties
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_gap_eq_sub {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (lam : Wt Ψ N) (τ : Ψ) (a : Fin N)
    (h : (a : ℕ) + 1 < N) :
    PB.gap (fun x : Ψ × Fin N => lam x.1 x.2) (τ, a) = lam τ a - lam τ ⟨(a : ℕ) + 1, h⟩ := by
  simp [PB.gap, PB.gapX, h]

theorem flag_dim_eq_antisymmetric_degree (Ψ : Type) [Fintype Ψ] (N : ℕ) :
    dimFl Ψ N = GroundTheory.Heights₂.Heights.antisymDegree Ψ N := by
  simp [dimFl, GroundTheory.Heights₂.Heights.antisymDegree, Nat.choose_two_right]

theorem flag_height_I9 : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N →
      I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro hFH hIn II hII Ψ _ _ N _ hN
  have hA : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) := by
    rw [flag_dim_eq_antisymmetric_degree]
    exact (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  have hev : ∀ lam : Wt Ψ N, hhFl Ψ N II (linRoot lam ^ (dimFl Ψ N + 1)) =
      eval (fun x => lam x.1 x.2) (PB.hFlPoly Ψ N II) := fun lam =>
    GlobalTheory.T.flag_height_polynomial_eval II hII Ψ N lam hN hA
  obtain ⟨-, hgap, hdom⟩ := hFH hIn II hII Ψ N hN
  refine ⟨?_, ?_, ?_⟩
  · rintro lam - ⟨τ, a, b, hab, heq⟩
    have h : (a : ℕ) + 1 < N := hab ▸ b.2
    have hb : b = ⟨(a : ℕ) + 1, h⟩ := Fin.ext hab
    rw [hev]
    refine hgap _ (τ, a) h ?_
    rw [flag_gap_eq_sub lam τ a h, ← hb, heq, sub_self]
  · intro lam hlam
    rw [hev]
    refine hdom _ fun p hp => ?_
    obtain ⟨τ, a⟩ := p
    rw [flag_gap_eq_sub lam τ a hp, sub_nonneg]
    exact hlam τ a ⟨(a : ℕ) + 1, hp⟩ (Fin.le_def.2 (Nat.le_succ _))
  · intro τ Q hQ
    exact GlobalTheory.T.flag_height_power_sum_one_zero II hII Ψ N τ Q hN hA hQ

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightI9PropertiesStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_I9_properties : PB.FlagHeight → PB.Inputs → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N → I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 | exact GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flag_height_I9 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightLabelInvariant
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightLabelInvariant
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (FlBlock FlIdx PFl xLine xDeg yFl fsHerm ΩFl refNorm)
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Top.HhLabel

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def blockMap (σ : Equiv.Perm Ψ) : FlBlock Ψ N → FlBlock Ψ N := fun q => (σ q.1, q.2)

def coordMap (σ : Equiv.Perm Ψ) : (Σ q : FlBlock Ψ N, FlIdx Ψ N q) → (Σ q : FlBlock Ψ N, FlIdx Ψ N q) :=
  fun p => ⟨(σ p.1.1, p.1.2), p.2⟩

theorem blockMap_bijective (σ : Equiv.Perm Ψ) : Function.Bijective (blockMap (N := N) σ) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    simp only [blockMap, Prod.mk.injEq] at h
    rw [σ.injective h.1, h.2]
  · rintro ⟨τ, i⟩
    exact ⟨(σ.symm τ, i), by simp [blockMap]⟩

theorem coordMap_injective (σ : Equiv.Perm Ψ) : Function.Injective (coordMap (N := N) σ) := by
  rintro ⟨⟨τ, i⟩, A⟩ ⟨⟨τ', i'⟩, A'⟩ h
  simp only [coordMap, Sigma.mk.inj_iff, Prod.mk.injEq] at h
  obtain ⟨⟨h1, rfl⟩, h2⟩ := h
  obtain rfl := σ.injective h1
  cases eq_of_heq h2
  rfl

theorem coordMap_surjective (σ : Equiv.Perm Ψ) : Function.Surjective (coordMap (N := N) σ) := by
  rintro ⟨⟨τ, i⟩, A⟩
  refine ⟨⟨(σ.symm τ, i), A⟩, Sigma.ext (by simp [coordMap]) HEq.rfl⟩

theorem isBlockMap (σ : Equiv.Perm Ψ) : IsBlockMap (blockMap (N := N) σ) (coordMap σ) :=
  ⟨(blockMap_bijective σ).1, coordMap_injective σ, fun _ => rfl, fun q _ => coordMap_surjective σ q⟩

def matEquiv (N : ℕ) (σ : Equiv.Perm Ψ) : (Ψ × Fin N × Fin N) ≃ (Ψ × Fin N × Fin N) :=
  Equiv.prodCongr σ (Equiv.refl _)

def fieldAut (σ : Equiv.Perm Ψ) : ΩFl Ψ N ≃+* ΩFl Ψ N :=
  IsFractionRing.ringEquivOfRingEquiv (renameEquiv ℚ (matEquiv N σ)).toRingEquiv

theorem yFl_coordMap (σ : Equiv.Perm Ψ) (p : Σ q : FlBlock Ψ N, FlIdx Ψ N q) :
    yFl Ψ N (coordMap σ p) = fieldAut σ (yFl Ψ N p) := by
  unfold yFl fieldAut
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  show _ = (renameEquiv ℚ (matEquiv N σ)).toRingEquiv.toRingHom _
  rw [RingHom.map_det]
  congr 1
  refine Matrix.ext fun a b => ?_
  exact (rename_X (R := ℚ) (matEquiv N σ) (p.1.1, Fin.castLE (GroundTheory.Heights₂.Heights.LowerBoundFree.step_le p.1.2) a, p.2.1 b)).symm

theorem mCoordIdeal_ringHom {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    (i : Ω₀ →+* Ω) (y₀ : (Σ k, J k) → Ω₀) : mCoordIdeal (fun p => i (y₀ p)) = mCoordIdeal y₀ := by
  have key : ∀ f : MRing J, mConeMap (fun p => i (y₀ p)) f = MvPolynomial.map i (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp => simp only [map_mul, hp]; simp [mConeMap]
  ext f
  show mConeMap _ f = 0 ↔ mConeMap _ f = 0
  rw [key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective i i.injective)

theorem imageZ_PFl (σ : Equiv.Perm Ψ) : imageZ (coordMap σ) (PFl Ψ N) = PFl Ψ N := by
  unfold PFl
  rw [← GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v (isBlockMap σ),
    ← mCoordIdeal_ringHom (fieldAut (N := N) σ : ΩFl Ψ N →+* ΩFl Ψ N) (yFl Ψ N)]
  congr 1
  funext p
  exact yFl_coordMap σ p

theorem blockFnField_coordMap (σ : Equiv.Perm Ψ) :
    blockFnField (yFl Ψ N ∘ coordMap σ) = blockFnField (yFl Ψ N) := by
  unfold blockFnField
  congr 1
  ext t
  constructor
  · rintro ⟨p, q, hpq, rfl⟩
    exact ⟨coordMap σ p, coordMap σ q, by simp [coordMap, hpq], rfl⟩
  · rintro ⟨p, q, hpq, rfl⟩
    obtain ⟨p', rfl⟩ := coordMap_surjective σ p
    obtain ⟨q', rfl⟩ := coordMap_surjective σ q
    exact ⟨p', q', (blockMap_bijective σ).1 hpq, rfl⟩

theorem xDeg_blockMap (σ : Equiv.Perm Ψ) (p : Ψ × Fin N) (q : FlBlock Ψ N) :
    xDeg Ψ N (σ p.1, p.2) (blockMap σ q) = xDeg Ψ N p q := by
  by_cases h : q.1 = p.1 <;> simp [xDeg, blockMap, h]

theorem isPullHerm_xLine (σ : Equiv.Perm Ψ) (p : Ψ × Fin N) :
    IsPullHerm (blockMap σ) (coordMap σ) (xLine Ψ N p) (xLine Ψ N (σ p.1, p.2)) := by
  refine ⟨?_, fun z' => ?_⟩
  · show xDeg Ψ N (σ p.1, p.2) = pullDeg (blockMap σ) (xDeg Ψ N p)
    funext q
    obtain ⟨q', rfl⟩ := (blockMap_bijective σ).2 q
    unfold pullDeg
    rw [(blockMap_bijective σ).1.extend_apply, xDeg_blockMap]
  · show refNorm (xDeg Ψ N (σ p.1, p.2)) z' = refNorm (xDeg Ψ N p) fun r => z' (coordMap σ r)
    unfold refNorm
    refine (Fintype.prod_bijective (blockMap σ) (blockMap_bijective σ) _ _ fun k => ?_).symm
    rw [xDeg_blockMap]
    rfl

theorem degree_mapDomain {J J' : Type} (f : J → J') (m : J →₀ ℕ) : (m.mapDomain f).degree = m.degree := by
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), ha, hb]
  | single a n => simp [Finsupp.mapDomain_single, Finsupp.degree_single]

end GlobalTheory.CompanionTheory.Ar.Top.HhLabel

namespace GlobalTheory.CompanionTheory.Ar.Top


open HhLabel in
theorem hhFl_labelInv : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ]
    (N : ℕ) [Nonempty Ψ], 2 ≤ N → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) →
    LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  intro II hII Ψ _ _ N _ _ hP σ F
  have key : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N,
      II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (σ (w k).1, (w k).2)) =
        II (FlBlock Ψ N) (FlIdx Ψ N) (PFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) := by
    intro w
    have himg := imageZ_PFl (N := N) σ
    have hPF := hII.2.2.1 (FlBlock Ψ N) (FlIdx Ψ N) (FlBlock Ψ N) (FlIdx Ψ N) (blockMap σ) (coordMap σ) (ΩFl Ψ N)
      (yFl Ψ N) (dimFl Ψ N + 1) (fun k => xLine Ψ N (w k)) (fun k => xLine Ψ N (σ (w k).1, (w k).2))
      (isBlockMap σ) hP (by show ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (imageZ (coordMap σ) (PFl Ψ N)) _; rw [himg]; exact hP)
      (fun _ => GroundTheory.Heights₂.Heights.LowerBoundFree.FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (fun j => isPullHerm_xLine σ (w j))
    rw [blockFnField_coordMap, IntermediateField.relfinrank_self, Nat.cast_one, one_mul] at hPF
    exact hPF.trans (congrArg (fun P => II (FlBlock Ψ N) (FlIdx Ψ N) P (dimFl Ψ N + 1) fun k => xLine Ψ N (w k)) himg)
  induction F using MvPolynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | monomial m c =>
    rw [rename_monomial]
    by_cases hm : m.degree = dimFl Ψ N + 1
    · obtain ⟨w, rfl⟩ := RootFieldNumerics.HH.exists_word _ m hm
      have hmap : (∑ k, Finsupp.single (w k) (1 : ℕ)).mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) =
          ∑ k, Finsupp.single (σ (w k).1, (w k).2) 1 := by
        rw [Finsupp.mapDomain_finsetSum]
        simp only [Finsupp.mapDomain_single]
      have hwd := RootFieldNumerics.HH.hhFl_word II hII.1 hP (fun k => (σ (w k).1, (w k).2)) c
      rw [hmap, hwd, RootFieldNumerics.HH.hhFl_word II hII.1 hP w c, key w]
    · rw [HhModel.hhFl_monomial_of_ne II _ _ (by rwa [degree_mapDomain]), HhModel.hhFl_monomial_of_ne II _ _ hm]

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightLabelInvariantStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_label_invariant : ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ], 2 ≤ N → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (GroundTheory.Heights₂.Heights.LowerBoundFree.PFl Ψ N) (dimFl Ψ N + 1) → LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.hhFl_labelInv | exact GlobalTheory.CompanionTheory.Ar.Top.hhFl_labelInv | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.hhFl_labelInv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerI3OfSemipositiveNef
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GapNonnegOfDominant
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem gap_nonneg_of_dominant {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) (τ : Ψ) : 0 ≤ gap j mu τ := by
  have h1 : j - 1 < N := by omega
  have hle : mu τ ⟨j, hjN⟩ ≤ mu τ ⟨j - 1, h1⟩ := hd τ ⟨j - 1, h1⟩ ⟨j, hjN⟩ (by rw [Fin.mk_le_mk]; omega)
  simp only [gap, ent, dif_pos h1, dif_pos hjN]
  exact sub_nonneg.mpr hle

theorem NefThreshold.mono {Ψ : Type} [Fintype Ψ] {N : ℕ} {j : ℕ} (hj1 : 1 ≤ j) (hjN : j < N)
    {mu : Wt Ψ N} (hd : Dominant mu) {b b' : ℝ} (hb : b ≤ b') (h : NefThreshold j b mu) :
    NefThreshold j b' mu := by
  intro τ
  have hg : 0 ≤ gap j mu τ := gap_nonneg_of_dominant hj1 hjN hd τ
  calc 4 * (Fintype.card Ψ : ℝ) * ‖mu‖ ≤ (b - 2) * gap j mu τ := h τ
    _ ≤ (b' - 2) * gap j mu τ := mul_le_mul_of_nonneg_right (by linarith) hg

theorem RootTower.nefFib_of_nefThreshold :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.ModelNefStatement → T.M2 →
      ∀ (B : ℕ) (c : T.Comp) (mu : Wt Ψ N), Dominant mu → NefThreshold T.j B mu →
        (T.M B c).NefFib mu 0 := by
  intro Ψ _ _ N T h1 h2 B c mu hd hB p hp
  by_cases hS : T.InS B p
  · exact h1 B c p hS mu hd
  · have hBp : B < p := by
      by_contra hc
      exact hS (show p.Prime ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hp, Or.inl (not_lt.mp hc)⟩)
    refine h2 B c p hp hS mu hd ?_
    exact NefThreshold.mono T.j_pos T.j_lt hd (by exact_mod_cast hBp.le) hB

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerI3OfSemipositiveNef
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem RootTower.tower_I3_of_nef_inputs :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  intro Ψ _ _ N T hA1 hM1 hM2 hAN abelian₂
  obtain ⟨s₀, hs₀, h⟩ := hA1 abelian₂
  refine ⟨s₀, hs₀, fun B hB c lam s hl hs hss hd ht => ⟨?_, h B hB c lam s hl hs hss hd⟩⟩
  intro p hp
  have hn := RootTower.nefFib_of_nefThreshold Ψ N T hM1 hM2 B c (T.lamS lam s) hd ht p hp
  exact (GlobalTheory.T.curve_degree_linear_nef_cone Ψ N (T.M B c) (T.lamS lam s) 0 s 0 0).2.2.1 p hs.le hn (hAN B c p hp)

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerI3OfSemipositiveNefStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_I3_of_semipositive_nef : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I3 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.RootTower.tower_I3_of_nef_inputs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremB
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremB
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem thmB_functional : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh :=
  @RootFieldNumerics.antisymmetry_tower_theorem

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_theorem_B : GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.Proportional → T.ThmW II → T.I8 II hh → I9 (Ψ := Ψ) (N := N) hh → T.ThmB II hh := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmB_functional | exact GlobalTheory.CompanionTheory.Ar.Top.thmB_functional | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmB_functional <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MeanSlopeProportionalVolume
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MeanSlopeProportionalVolume
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem mean_slope_of_volume_eq : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval :=
  @RootFieldNumerics.mean_slope_of_proportional_volume

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MeanSlopeProportionalVolumeStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mean_slope_proportional_volume : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (C rd Lval : ℝ), T.Proportional → T.VolEq → T.T2 II C rd Lval → T.MeanSlope II C rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq | exact GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.mean_slope_of_volume_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBAveraged
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeSymmetries
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeSymmetries
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem flag_integral_permutations : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F :=
  @RootFieldNumerics.degFl_symmetry_invariance

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagDegreeSymmetriesStatement
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_degree_symmetries : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ), (∀ (τ : Ψ) (a b : Fin N) (F : RP Ψ N), a ≠ b → degFl (rename (fun x : Ψ × Fin N => if x.1 = τ then (x.1, Equiv.swap a b x.2) else x) F) = -degFl F) ∧ ∀ (σ : Equiv.Perm Ψ) (F : RP Ψ N), degFl (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = degFl F ∧ ∀ (j : ℕ) (τ : Ψ), Sh j (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Sh j τ F ∧ Tot (σ τ) (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = Tot τ F := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.flag_integral_permutations | exact GlobalTheory.CompanionTheory.Ar.Top.flag_integral_permutations | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.flag_integral_permutations <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBAveraged
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem sum_group_apply_eq {Ψ : Type} (Γ : Subgroup (Equiv.Perm Ψ)) [Fintype Γ]
    (htr : ∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') (f : Ψ → ℝ) (τ τ' : Ψ) :
    ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ) = ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ') := by
  obtain ⟨ρ, hρ, rfl⟩ := htr τ' τ
  exact Fintype.sum_equiv (Equiv.mulRight (⟨ρ, hρ⟩ : Γ)) _ _ (fun g => by simp [Equiv.Perm.mul_apply])

theorem exists_group_mean {Ψ : Type} (Γ : Subgroup (Equiv.Perm Ψ)) [Fintype Γ]
    (htr : ∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') (f : Ψ → ℝ) :
    ∃ A : ℝ, ∀ τ, ∑ g : Γ, f ((g : Equiv.Perm Ψ) τ) = (Fintype.card Γ : ℝ) * A := by
  rcases isEmpty_or_nonempty Ψ with h | ⟨⟨τ₀⟩⟩
  · exact ⟨0, fun τ => (h.false τ).elim⟩
  · have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    refine ⟨(∑ g : Γ, f ((g : Equiv.Perm Ψ) τ₀)) / (Fintype.card Γ : ℝ), fun τ => ?_⟩
    rw [mul_div_cancel₀ _ hc]
    exact sum_group_apply_eq Γ htr f τ τ₀

theorem mean_estimate {G Ψ : Type} [Fintype G] [Nonempty G] [Fintype Ψ] (P V H bd A Bs : ℝ) (S U : Ψ → ℝ)
    (a b : G → Ψ → ℝ) (hA : ∀ τ, ∑ g, a g τ = (Fintype.card G : ℝ) * A)
    (hB : ∀ τ, ∑ g, b g τ = (Fintype.card G : ℝ) * Bs)
    (h : ∀ g, |P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)| ≤ bd) :
    |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)| ≤ bd := by
  have hn : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  set n : ℝ := (Fintype.card G : ℝ) with hndef
  have h1 : ∑ g, ∑ τ, (a g τ - b g τ) * S τ = n * ((A - Bs) * ∑ τ, S τ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hA, hB]
    ring
  have h2 : ∑ g, ∑ τ, b g τ * U τ = n * (Bs * ∑ τ, U τ) := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_mul, hB]
    ring
  have key : ∑ g : G, (P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)) =
      n * (P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)) := by
    have : ∀ g : G, P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ) =
        (P - V * H) + V * ∑ τ, (a g τ - b g τ) * S τ + V * ∑ τ, b g τ * U τ := fun g => by ring
    simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    rw [← hndef]
    ring
  have hle : n * |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)| ≤ n * bd := by
    calc n * |P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ)|
        = |n * (P - V * (H - (A - Bs) * ∑ τ, S τ - Bs * ∑ τ, U τ))| := by
          rw [abs_mul, abs_of_pos hn]
      _ = |∑ g : G, (P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ))| := by rw [key]
      _ ≤ ∑ g : G, |P - V * (H - ∑ τ, (a g τ - b g τ) * S τ - ∑ τ, b g τ * U τ)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g : G, bd := Finset.sum_le_sum fun g _ => h g
      _ = n * bd := by simp [hndef]
  exact le_of_mul_le_mul_left hle hn

theorem thmBA_of_thmB_propA : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II →
    LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  intro II Ψ _ _ N T hh hB hA hL
  obtain ⟨C, B₁, hC⟩ := hB
  obtain ⟨Γ, htr, hinv⟩ := hA
  have : Fintype Γ := Fintype.ofFinite _
  refine ⟨C, max B₁ 2, fun B hBge => ?_⟩
  obtain ⟨α, β, hm⟩ := hC B (le_trans (le_max_left _ _) hBge)
  obtain ⟨A, hAm⟩ := exists_group_mean Γ htr α
  obtain ⟨Bs, hBm⟩ := exists_group_mean Γ htr β
  refine ⟨A, Bs, fun m hdeg => ?_⟩
  refine mean_estimate (G := Γ) _ _ _ _ A Bs _ _ (fun g τ => α ((g : Equiv.Perm Ψ) τ))
    (fun g τ => β ((g : Equiv.Perm Ψ) τ)) hAm hBm fun g => ?_
  set F : RP Ψ N := monomial m 1 with hF
  set φ : Ψ × Fin N → Ψ × Fin N := fun x => ((g : Equiv.Perm Ψ) x.1, x.2) with hφ
  have hR : (monomial (m.mapDomain φ) 1 : RP Ψ N) = rename φ F := (rename_monomial φ m 1).symm
  have hest := hm (m.mapDomain φ) (by rw [Finsupp.degree_mapDomain]; exact hdeg)
  have anti := fun τ j => ((GlobalTheory.T.flag_degree_symmetries Ψ N).2 (g : Equiv.Perm Ψ) F).2 j τ
  have hS : ∑ τ, (α τ - β τ) * Sh T.j τ (rename φ F) =
      ∑ τ, (α ((g : Equiv.Perm Ψ) τ) - β ((g : Equiv.Perm Ψ) τ)) * Sh T.j τ F := by
    rw [← Equiv.sum_comp (g : Equiv.Perm Ψ)]
    exact Finset.sum_congr rfl fun τ _ => by rw [(anti τ T.j).1]
  have hU : ∑ τ, β τ * Tot τ (rename φ F) = ∑ τ, β ((g : Equiv.Perm Ψ) τ) * Tot τ F := by
    rw [← Equiv.sum_comp (g : Equiv.Perm Ψ)]
    exact Finset.sum_congr rfl fun τ _ => by rw [(anti τ T.j).2]
  rw [hR, hS, hU, hinv g g.2 B (le_trans (le_max_right _ _) hBge) F, hL g F] at hest
  exact hest

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBAveragedStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_theorem_B_averaged : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II → LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA | exact GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT1Limit
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT1Limit
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace LimitVolumeRatio

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem linRoot_sub_smul (lam nu : Wt Ψ N) (s : ℝ) :
    linRoot (lam - s • nu) = linRoot lam - C s * linRoot nu := by
  simp only [linRoot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, sub_mul,
    Finset.sum_sub_distrib, Finset.mul_sum, mul_neg, mul_assoc]
  ring

theorem linA_lamS (T : RootTower Ψ N) (u : Wt Ψ N) (s : ℝ) :
    linA (T.lamS u s) s = toA (linRoot u) + C s * (X none - toA (linRoot T.nu)) := by
  simp only [linA, RootTower.lamS, linRoot_sub_smul, toA, map_sub, map_mul, rename_C]
  ring

theorem cont_pow (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (P0 P1 : RPA Ψ N) (d : ℕ) :
    Continuous fun s : ℝ => Φ ((P0 + C s * P1) ^ d) := by
  have h : ∀ s : ℝ, Φ ((P0 + C s * P1) ^ d) =
      ∑ m ∈ Finset.range (d + 1), s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) := by
    intro s
    set_option synthInstance.maxHeartbeats 100000 in
      rw [add_pow, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) =
      Φ (s ^ (d - m) • (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N))) by rw [map_smul, smul_eq_mul]]
    congr 1
    rw [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow]
    ring
  rw [show (fun s : ℝ => Φ ((P0 + C s * P1) ^ d)) = fun s : ℝ => ∑ m ∈ Finset.range (d + 1),
      s ^ (d - m) * Φ (P0 ^ m * P1 ^ (d - m) * (d.choose m : RPA Ψ N)) from funext h]
  fun_prop

theorem tendsto_lin (Φ : RPA Ψ N →ₗ[ℝ] ℝ) (T : RootTower Ψ N) (u : Wt Ψ N) (d : ℕ) :
    Tendsto (fun s => Φ (linA (T.lamS u s) s ^ d)) (𝓝[>] 0) (𝓝 (Φ (toA (linRoot u ^ d)))) := by
  have hc := (cont_pow Φ (toA (linRoot u)) (X none - toA (linRoot T.nu)) d).tendsto 0
  simp only [map_zero, zero_mul, add_zero] at hc
  rw [show toA (linRoot u ^ d) = toA (linRoot u) ^ d by simp [toA, map_pow]]
  exact (hc.mono_left nhdsWithin_le_nhds).congr fun s => by rw [linA_lamS]

theorem gap_sub_smul (j : ℕ) (lam nu : Wt Ψ N) (s : ℝ) (τ : Ψ) :
    gap j (lam - s • nu) τ = gap j lam τ - s * gap j nu τ := by
  simp only [gap, ent]
  split_ifs <;> simp <;> ring

end LimitVolumeRatio

end GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top

namespace LimitVolumeRatio

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem eventually_dominant (T : RootTower Ψ N) (u : Wt Ψ N) (hu : RegDominant u) :
    ∀ᶠ s in 𝓝 (0 : ℝ), Dominant (T.lamS u s) := by
  have key : ∀ τ (a b : Fin N), ∀ᶠ s in 𝓝 (0 : ℝ), a ≤ b → (T.lamS u s) τ b ≤ (T.lamS u s) τ a := by
    intro τ a b
    by_cases hab : a < b
    · have h1 : Tendsto (fun s : ℝ => u τ b - s * T.nu τ b) (𝓝 0) (𝓝 (u τ b - 0 * T.nu τ b)) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
      have h2 : Tendsto (fun s : ℝ => u τ a - s * T.nu τ a) (𝓝 0) (𝓝 (u τ a - 0 * T.nu τ a)) :=
        (continuous_const.sub (continuous_id.mul continuous_const)).tendsto 0
      filter_upwards [h1.eventually_lt h2 (by simpa using hu τ a b hab)] with s hs _
      simpa [RootTower.lamS] using hs.le
    · exact Eventually.of_forall fun s h => by
        have : a = b := le_antisymm h (not_lt.mp hab)
        subst this
        exact le_rfl
  exact eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => key τ a b

theorem eventually_threshold [Nonempty Ψ] (T : RootTower Ψ N) (u : Wt Ψ N) (g : ℝ) (hw : WeightHyp T.j u g)
    (B : ℕ) (hB : bigB0 u g < B + 1) :
    ∀ᶠ s in 𝓝 (0 : ℝ), NefThreshold T.j B (T.lamS u s) := by
  have hF : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by have := T.j_pos; have := T.j_lt; omega)
  have hg : 0 < g := hw.1
  have hx : 0 ≤ ‖u‖ := norm_nonneg _
  set F : ℝ := (Fintype.card Ψ : ℝ)
  set x : ℝ := ‖u‖
  have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hB' : 4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3 < (B : ℝ) - 2 := by
    simp only [bigB0] at hB
    nlinarith
  have hxg : x / g * g = x := div_mul_cancel₀ x hg.ne'
  have hFN : (4 : ℝ) ≤ F * (N : ℝ) ^ 2 := by
    have := mul_le_mul hF hn2 (by norm_num) (by linarith)
    linarith
  have hpos : 0 < 4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3 := by
    have : 0 ≤ x / g := div_nonneg hx hg.le
    have h' : 0 ≤ 4 * F * (N : ℝ) ^ 2 * (x / g) := mul_nonneg (by positivity) this
    linarith
  have hB2 : 0 ≤ (B : ℝ) - 2 := by linarith
  have at0 : ∀ τ, 4 * F * x < ((B : ℝ) - 2) * gap T.j u τ := by
    intro τ
    have h1 : ((B : ℝ) - 2) * g ≤ ((B : ℝ) - 2) * gap T.j u τ :=
      mul_le_mul_of_nonneg_left (hw.2.2.1 τ) hB2
    have h2 := mul_lt_mul_of_pos_right hB' hg
    have h3 : (4 * F * (N : ℝ) ^ 2 + 4 * F * (N : ℝ) ^ 2 * (x / g) - 3) * g =
        4 * F * (N : ℝ) ^ 2 * g + 4 * F * (N : ℝ) ^ 2 * x - 3 * g := by
      rw [sub_mul, add_mul, mul_assoc (4 * F * (N : ℝ) ^ 2), hxg]
    have h4 : 4 * F * x ≤ 4 * F * (N : ℝ) ^ 2 * x := by
      have e : 4 * F * (N : ℝ) ^ 2 * x - 4 * F * x = (4 * F * x) * ((N : ℝ) ^ 2 - 1) := by ring
      have := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * F) hx) (by linarith : (0 : ℝ) ≤ (N : ℝ) ^ 2 - 1)
      linarith
    have h5 : 0 < 4 * F * (N : ℝ) ^ 2 * g - 3 * g := by
      have e : 4 * F * (N : ℝ) ^ 2 * g - 3 * g = g * (4 * (F * (N : ℝ) ^ 2) - 3) := by ring
      rw [e]
      exact mul_pos hg (by linarith)
    linarith
  have key : ∀ τ, ∀ᶠ s in 𝓝 (0 : ℝ), 4 * F * ‖T.lamS u s‖ ≤ ((B : ℝ) - 2) * gap T.j (T.lamS u s) τ := by
    intro τ
    have h1 : Tendsto (fun s : ℝ => 4 * F * ‖T.lamS u s‖) (𝓝 0) (𝓝 (4 * F * ‖T.lamS u 0‖)) :=
      ((continuous_const.mul (continuous_const.sub (continuous_id.smul continuous_const)).norm)).tendsto 0
    have h2 : Tendsto (fun s : ℝ => ((B : ℝ) - 2) * (gap T.j u τ - s * gap T.j T.nu τ)) (𝓝 0)
        (𝓝 (((B : ℝ) - 2) * (gap T.j u τ - 0 * gap T.j T.nu τ))) :=
      (continuous_const.mul (continuous_const.sub (continuous_id.mul continuous_const))).tendsto 0
    have h0 : 4 * F * ‖T.lamS u 0‖ < ((B : ℝ) - 2) * (gap T.j u τ - 0 * gap T.j T.nu τ) := by
      simpa [RootTower.lamS] using at0 τ
    filter_upwards [h1.eventually_lt h2 h0] with s hs
    rw [RootTower.lamS, gap_sub_smul]
    exact hs.le
  exact eventually_all.2 key

theorem tower_T1_limit_of_inputs : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ]
    (T : RootTower Ψ N), T.Proportional → T.I2 II → T.I3 → T.T1 II := by
  intro II Ψ _ _ N _ T hProp hI2 hI3 u g hw B hB c
  have hF : (1 : ℝ) ≤ Fintype.card Ψ := by exact_mod_cast Fintype.card_pos
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by have := T.j_pos; have := T.j_lt; omega)
  have hB2 : 2 ≤ B := by
    have hq : 0 ≤ ‖u‖ / g := div_nonneg (norm_nonneg _) hw.1.le
    have : (16 : ℝ) ≤ bigB0 u g := by
      simp only [bigB0]
      have hn2 : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
      have hFN : (4 : ℝ) ≤ (Fintype.card Ψ : ℝ) * (N : ℝ) ^ 2 := by nlinarith
      have h1q : (1 : ℝ) ≤ 1 + ‖u‖ / g := by linarith
      have := mul_le_mul hFN h1q zero_le_one (by positivity)
      nlinarith
    have : (15 : ℝ) < B := by linarith
    exact_mod_cast (show (2 : ℝ) ≤ B by linarith)
  have hdom := eventually_dominant T u hw.2.1
  have hthr := eventually_threshold T u g hw B hB
  have hpos : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := eventually_mem_nhdsWithin

  obtain ⟨s₁, hs₁, C₂, hag⟩ := hI2 (l1 u)
  have hdiff : Tendsto (fun s => T.mbarTop II B c u s - T.PBs II B c (T.lamS u s) s) (𝓝[>] 0) (𝓝 0) := by
    have hlin : Tendsto (fun s : ℝ => C₂ * s) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlin
    filter_upwards [hpos, (eventually_le_nhds hs₁).filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds] with s h0 h1 h2
    exact hag B hB2 c u s le_rfl h0 h1 h2
  have hPB : Tendsto (fun s => T.PBs II B c (T.lamS u s) s) (𝓝[>] 0)
      (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) :=
    LimitVolumeRatio.tendsto_lin ((T.M B c).PP II) T u (dimFl Ψ N + 1)
  have hbar : Tendsto (fun s => T.mbarTop II B c u s) (𝓝[>] 0)
      (𝓝 (T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)))) := by
    have h := hPB.add hdiff
    rw [add_zero] at h
    exact h.congr fun s => by ring
  have hdeg : Tendsto (fun s => T.mDeg B c u s) (𝓝[>] 0) (𝓝 (T.vol c * flagDeg u)) := by
    have h := LimitVolumeRatio.tendsto_lin (T.M B c).geoFun T u (dimFl Ψ N)
    rwa [hProp.2.1 B c] at h
  have hvpos : 0 < T.vol c * flagDeg u :=
    mul_pos (hProp.1 c) ((flagDeg_eq_weyl Ψ N u).2.1 hw.2.1)
  refine ⟨?_, hbar, hdeg, hvpos, ?_⟩
  · obtain ⟨s₀, hs₀, h3⟩ := hI3 (l1 u)
    filter_upwards [hpos, (eventually_le_nhds hs₀).filter_mono nhdsWithin_le_nhds,
      hdom.filter_mono nhdsWithin_le_nhds, hthr.filter_mono nhdsWithin_le_nhds] with s h0 h1 h2 h4
    exact h3 B hB2 c u s le_rfl h0 h1 h2 h4
  · have hne : ((dimFl Ψ N : ℝ) + 1) * (T.vol c * flagDeg u) ≠ 0 :=
      (mul_pos (by positivity) hvpos).ne'
    exact hbar.div (hdeg.const_mul _) hne

end LimitVolumeRatio

end GlobalTheory.CompanionTheory.Ar.Top
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerT1LimitStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_T1_limit : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N), T.Proportional → T.I2 II → T.I3 → T.T1 II := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.LimitVolumeRatio.tower_T1_limit_of_inputs | exact GlobalTheory.CompanionTheory.Ar.Top.LimitVolumeRatio.tower_T1_limit_of_inputs | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.LimitVolumeRatio.tower_T1_limit_of_inputs <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilInputsCombined
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem chain_tower : PB.FlagHeight → PB.Inputs → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound →
    GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement →
    ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
    [Nonempty Ψ] (T : RootTower Ψ N) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd →
    FrobShape frob → T.Proportional → T.I1 II → T.I2 II → T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I5 II → T.I6 II →
    T.I7 → T.I8 II (hhFl Ψ N II) → T.Prop6 II frob → T.PropA II → T.PropF II C' rd Lval → T.VolEq →
    T.SlopeLower II C rd Lval → T.T1 II ∧ T.ThmB II (hhFl Ψ N II) ∧ T.T2 II (2 * C + 3 * C' + 5) rd Lval ∧
      T.MeanSlope II (2 * C + 3 * C' + 5) rd Lval := by
  intro hFH hIn hZ1 hZ2 hAP hG II hII Ψ _ _ N _ T frob C C' rd Lval hC hC' hrd hfs hP hI1 hI2 hA1 hM1 hM2 hAN
    hI5 hI6 hI7 hI8 hP6 hPA hPF hVol hSL
  have hN : 2 ≤ N := by have := T.j_pos; have := T.j_lt; omega
  have hI3 : T.I3 := GlobalTheory.T.tower_I3_of_semipositive_nef Ψ N T hA1 hM1 hM2 hAN
  have hT1 : T.T1 II := GlobalTheory.T.tower_T1_limit II Ψ N T hP hI2 hI3
  have hW : T.ThmW II := GlobalTheory.T.tower_weil_theorem hIn.2.2.2.2.2.1 GlobalTheory.T.exists_unique_rational_statement GlobalTheory.CompanionTheory.Ar.Link.divSuppArith_holds hZ1 hZ2
    II hII Ψ N T hP hI1 hI2 hI3 hI5 hI6 hI7
  have hI9 : I9 (Ψ := Ψ) (N := N) (hhFl Ψ N II) := GlobalTheory.T.flag_height_I9_properties hFH hIn II hII Ψ N hN
  have hB : T.ThmB II (hhFl Ψ N II) := GlobalTheory.T.tower_theorem_B hAP II Ψ N T (hhFl Ψ N II) hP hW hI8 hI9
  have he : GroundTheory.Heights₂.Heights.antisymDegree Ψ N = dimFl Ψ N := by
    simp [GroundTheory.Heights₂.Heights.antisymDegree, dimFl, Nat.choose_two_right]
  have hAr := (GlobalTheory.T.flag_variety_boundary_dimension_drop Ψ N hN).1
  rw [he] at hAr
  have hLab : LabelInv (Ψ := Ψ) (N := N) (hhFl Ψ N II) := GlobalTheory.T.flag_height_label_invariant II hII Ψ N hN hAr
  have hBA : T.ThmBA II (hhFl Ψ N II) := GlobalTheory.T.tower_theorem_B_averaged II Ψ N T (hhFl Ψ N II) hB hPA hLab
  have hTest : HhTestBound T.j (hhFl Ψ N II) := GlobalTheory.T.flag_height_test_bound hG hIn II hII Ψ N T.j T.j_pos T.j_lt
  have hA0 : T.LowerBoundAtBase II (hhFl Ψ N II) frob (2 * (C + C') + 3) rd Lval :=
    GlobalTheory.T.test_height_bound II Ψ N T (hhFl Ψ N II) frob C C' rd Lval hC hC' hrd hP hI9 hPF hSL hTest
  have hK : (0 : ℝ) ≤ 2 * (C + C') + 3 := by linarith
  have hT2' := GlobalTheory.T.tower_T2 II Ψ N T (hhFl Ψ N II) frob (2 * (C + C') + 3) C' rd Lval hK hC' hrd hP hfs hI9 hP6
    hBA hPF hA0
  have hEq : 2 * (C + C') + 3 + C' + 2 = 2 * C + 3 * C' + 5 := by ring
  rw [hEq] at hT2'
  exact ⟨hT1, hB, hT2', GlobalTheory.T.mean_slope_proportional_volume II Ψ N T _ rd Lval hP hVol hT2'⟩

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerWeilInputsCombinedStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_weil_inputs_combined : PB.FlagHeight → PB.Inputs → SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → GroundTheory.Heights₂.Heights.AntisymPerturbation.Statement → GroundTheory.Heights₂.Heights.LowerBoundFree.GrassmannianHeightZTwo.Statement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) [Nonempty Ψ] (T : RootTower Ψ N) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (C C' rd Lval : ℝ), 0 ≤ C → 0 ≤ C' → 1 ≤ rd → FrobShape frob → T.Proportional → T.I1 II → T.I2 II → T.A1 → T.ModelNefStatement → T.M2 → T.ANef → T.I5 II → T.I6 II → T.I7 → T.I8 II (hhFl Ψ N II) → T.Prop6 II frob → T.PropA II → T.PropF II C' rd Lval → T.VolEq → T.SlopeLower II C rd Lval → T.T1 II ∧ T.ThmB II (hhFl Ψ N II) ∧ T.T2 II (2 * C + 3 * C' + 5) rd Lval ∧ T.MeanSlope II (2 * C + 3 * C' + 5) rd Lval := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.chain_tower | exact GlobalTheory.CompanionTheory.Ar.Top.chain_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.chain_tower <;> assumption)
end
