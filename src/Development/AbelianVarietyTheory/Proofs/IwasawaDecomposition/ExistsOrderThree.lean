module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Formalism.LocalToGlobal.GlobalTheory.NormSqLatticeFunctionEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeanSquareEvenThetaTwelfthRootInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemInvMulDifferent
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.Mem.EigenLine

variable {R : Ranks} (H : Host R)

theorem half_ne_zero :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
  refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
  intro h0
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  apply hd
  have := H.𝔟_spec.1
  rw [h0, Ideal.bot_mul] at this
  exact this

theorem half_mul_inv :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) * H.AA0 = 1 :=
  mul_inv_cancel₀ (half_ne_zero H)

theorem inv_mul_different :
    H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have h : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, mul_comm H.AA0, half_mul_inv, one_mul]

theorem mem_inv_mul_different (x : H.E) :
    x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∃ b ∈ H.𝔟, x = H.conj ((b : 𝓞 H.E) : H.E) := by
  rw [inv_mul_different, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Ideal.pointwise_smul_def] at hc
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj).surjective).1 hc
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨H.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, rfl⟩

theorem map_mem_ellLat {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL)
    (g : R.GG) (x : H.E)
    (hx : x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
    embE (H.sigmaOf g x) ∈ ellLat H embE g := by
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro i hi j hj
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    exact Submodule.subset_span ⟨i, hi, b, hb, rfl⟩
  · intro a b ha hb
    rw [map_add (f := _), map_add (f := _)]
    exact Submodule.add_mem _ ha hb

theorem ellT_eq_ellLat : ∀ (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (embE : D.host.E →+* M),
    (∀ x, ((embE x : M) : ℂ) = D.host.φ₀ x) → ∀ τ : D.what₂.Tau,
      ellT D M τ = ellLat D.host embE (D.eTau τ).1 := by
  intro D M _ embE hE τ
  have hτ : ∀ (τ : D.what₂.Tau) x, embT D τ x = ((embE (D.host.sigmaOf (D.eTau τ).1 x) : M) : ℂ) := by
    intro τ x
    rw [hE]
    rfl
  have hM : ∀ τ x, embT D τ x ∈ M := fun τ x => by
    rw [hτ]
    exact Subtype.property _
  let φ : D.host.E →+* M := embE.comp (((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)).comp
    (D.host.conj : D.host.E →+* D.host.E))
  have hφ : ∀ y, φ y = embE (D.host.sigmaOf (D.eTau τ).1 (D.host.conj y)) := fun _ => rfl
  have hone := half_mul_inv D.host
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM] at hx
    have key : ∀ z ∈ ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0,
        x * φ z ∈ ellLat D.host embE (D.eTau τ).1 := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have hint : IsIntegral ℤ (x * φ j) := by
          refine (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 ?_
          have := hx j hj
          rw [hτ] at this
          exact this
        let c : 𝓞 M := ⟨x * φ j, hint⟩
        have : c • φ (b : D.host.E) ∈ ellLat D.host embE (D.eTau τ).1 :=
          Submodule.smul_mem _ _ (map_mem_ellLat D.host embE _ _
            ((mem_inv_mul_different D.host _).2 ⟨b, hb, rfl⟩))
        convert this using 1
        change x * φ (b * j) = x * φ j * φ b
        rw [map_mul]; ring
      · intro a b ha hb
        rw [map_add (f := _), mul_add]
        exact Submodule.add_mem _ ha hb
    have := key 1 (hone ▸ FractionalIdeal.one_mem_one _)
    simpa using this
  · unfold ellLat
    rw [Submodule.span_le]
    rintro x ⟨a, ha, d, hd, rfl⟩
    obtain ⟨b, hb, hab⟩ := (mem_inv_mul_different D.host (a * (d : D.host.E))).1
      (FractionalIdeal.mul_mem_mul ha ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩))
    rw [SetLike.mem_coe, GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    have h1 : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hone ▸ FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩) hy
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← hτ, hab, ← map_mul, ← map_mul, ← hr]
    exact map_isIntegral_int ((embT D τ).comp (D.host.conj : D.host.E →+* D.host.E)) r.isIntegral_coe

end GlobalTheory.Mem.EigenLine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodPairBaseLat
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.Per.ConjCM

open GlobalTheory.ConjPoint

variable {R : Ranks} (H : Host R)

theorem mem_baseLat (w : ℂ) :
    w ∈ baseLat H ↔ ∃ c ∈ H.ccK, w = H.φ₀ (((c : H.K) : H.E)) := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, H.ccK.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', H.ccK.add_mem hc hc', by simp⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, H.ccK.neg_mem hc, by simp⟩
  · exact fun hw => AddSubgroup.subset_closure hw

theorem exists_periodPair_baseLat : ∃ L : PeriodPair, ∀ z, z ∈ baseLat H ↔ z ∈ L.lattice := by
  have hr : Module.finrank ℚ H.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K H.hyp.2.1.pos (H.sqd_sq)
  have hd : NumberField.discr H.K = -(H.d : ℤ) :=
    GlobalTheory.discr_eq_neg_of_sq_eq hr H.hyp.2.1.squarefree
      (by have := H.hyp.2.2.2.1; omega)
      (Formalism.FrobeniusOrbits.SplitK.bK_sq (H.sqd_sq))
  let σ : H.K →+* ℂ := H.φ₀.comp H.K.val.toRingHom
  let I : (Ideal (𝓞 H.K))⁰ := ⟨H.ccK, mem_nonZeroDivisors_of_ne_zero H.ccK_ne_bot⟩
  obtain ⟨L, hL⟩ := GlobalTheory.QuadraticZeta.exists_periodPair hr hd σ (FractionalIdeal.mk0 H.K I)
  refine ⟨L, fun z => ?_⟩
  rw [mem_baseLat, ← SetLike.mem_coe (p := L.lattice), hL]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨(c : H.K), FractionalIdeal.mem_coeIdeal_of_mem _ hc, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨c, hc, rfl⟩

end GlobalTheory.Mem.Per.ConjCM
end

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob

namespace GlobalTheory.Mem.TruePeriods

theorem area_map_unit (Λ : AddSubgroup ℂ) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    area (Λ.map (AddMonoidHom.mulLeft ζ)) = area Λ := by
  have e : ∀ x y : ℂ, (starRingEnd ℂ) (ζ * x) * (ζ * y) = (starRingEnd ℂ) x * y := fun x y => by
    have : (starRingEnd ℂ) ζ * ζ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]; simp
    rw [map_mul]; linear_combination ((starRingEnd ℂ) x * y) * this
  unfold area
  congr 1
  ext a
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨ha, _, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨ha, x, hx, y, hy, congrArg (fun z : ℂ => |z.im|) (e x y)⟩
  · rintro ⟨ha, x, hx, y, hy, rfl⟩
    exact ⟨ha, ζ * x, ⟨x, hx, rfl⟩, ζ * y, ⟨y, hy, rfl⟩, congrArg (fun z : ℂ => |z.im|) (e x y).symm⟩

theorem isLat_of_discr_one {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ = 1) : GlobalTheory.ThetaConj.IsLat Λ := by
  obtain ⟨L, hL⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_discr_ne_zero (Λ := Λ) (by rw [h]; exact one_ne_zero)
  refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
  ext z
  rw [hL, AddSubgroup.mem_closure_pair, PeriodPair.mem_lattice]
  simp only [zsmul_eq_mul]

theorem exists_root_of_jLat_eq {Λ Λ' : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ = 1) (h' : TaylorLogMetric.discr Λ' = 1)
    (hj : jLat Λ = jLat Λ') : ∃ ζ : ℂ, ζ ^ 12 = 1 ∧ Λ' = Λ.map (AddMonoidHom.mulLeft ζ) := by
  have h2 : g2 Λ ^ 3 = g2 Λ' ^ 3 := by
    unfold jLat at hj
    rw [h, h'] at hj
    linear_combination hj / 1728
  have h3 : g3 Λ ^ 2 = g3 Λ' ^ 2 := by
    unfold TaylorLogMetric.discr at h h'
    linear_combination (h' - h + h2) / 27
  obtain ⟨u, hu, hu2⟩ : ∃ u : ℂ, u ^ 3 = 1 ∧ g2 Λ = u * g2 Λ' := by
    by_cases h0 : g2 Λ' = 0
    · refine ⟨1, one_pow _, ?_⟩
      rw [h0] at h2 ⊢
      simpa using h2
    · exact ⟨g2 Λ / g2 Λ', by rw [div_pow, h2, div_self (pow_ne_zero _ h0)], by field_simp⟩
  obtain ⟨ζ, h4, h6⟩ : ∃ ζ : ℂ, ζ ^ 4 = u ∧ g3 Λ = ζ ^ 6 * g3 Λ' := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with e | e
    · exact ⟨u, by linear_combination u * hu, by rw [e]; linear_combination (-(u ^ 3 + 1) * g3 Λ') * hu⟩
    · have i4 : Complex.I ^ 4 = 1 := Complex.I_pow_four
      have i6 : Complex.I ^ 6 = -1 := by
        rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, i4, Complex.I_sq, one_mul]
      refine ⟨u * Complex.I, ?_, ?_⟩
      · rw [mul_pow, i4]; linear_combination u * hu
      · rw [mul_pow, i6, e]; linear_combination ((u ^ 3 + 1) * g3 Λ') * hu
  have h12 : ζ ^ 12 = 1 := by rw [show ζ ^ 12 = (ζ ^ 4) ^ 3 by ring, h4, hu]
  have h0 : ζ ≠ 0 := by rintro rfl; simp at h12
  refine ⟨ζ, h12, ?_⟩
  obtain ⟨L, hL⟩ := (isLat_of_discr_one h').exists_periodPair
  refine ((GlobalTheory.LatticeInvariants.invariants_dictionary L Λ' hL).2.2.2.2.2.1 _ ?_ ?_).symm
  · rw [← h4] at hu2
    unfold g2 at hu2 ⊢
    rw [Model.eisG_map _ _ h0]
    field_simp
    linear_combination hu2 / 60
  · unfold g3 at h6 ⊢
    rw [Model.eisG_map _ _ h0]
    field_simp
    linear_combination h6 / 140

theorem norm_eq_one_of_pow {ζ : ℂ} (h : ζ ^ 12 = 1) : ‖ζ‖ = 1 := by
  have := congrArg norm h
  rw [norm_pow, norm_one] at this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this

theorem meanSquare_evenTheta_twelfthRoot_invariant {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ = 1) {ζ : ℂ} (hζ : ζ ^ 12 = 1) (t : ℂ) :
    nrm1Sq (Λ.map (AddMonoidHom.mulLeft ζ)) (GL3Theta.th0 (Λ.map (AddMonoidHom.mulLeft ζ)) (ζ * t)) =
      nrm1Sq Λ (GL3Theta.th0 Λ t) := by
  have h0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hn := norm_eq_one_of_pow hζ
  have h' : TaylorLogMetric.discr (Λ.map (AddMonoidHom.mulLeft ζ)) = 1 := by rw [Model.discr_map _ _ h0, hζ, h]; simp
  have ha := area_map_unit Λ hn
  have hc : ζ * (starRingEnd ℂ) ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  have hU : U1 (Λ.map (AddMonoidHom.mulLeft ζ)) (ζ * t) (sgStar (Λ.map (AddMonoidHom.mulLeft ζ))) 0 =
      ζ * U1 Λ t (sgStar Λ) 0 := by
    unfold U1
    rw [zero_add, zero_add, (GlobalTheory.OddTheta.sgStar_laws Λ (isLat_of_discr_one h)).2.2.2.2 ζ h0, ha, mul_assoc,
      show (Real.pi : ℂ) * (ζ * t) * (starRingEnd ℂ) (ζ * t) = (Real.pi : ℂ) * t * (starRingEnd ℂ) t by
        rw [map_mul]; linear_combination ((Real.pi : ℂ) * t * (starRingEnd ℂ) t) * hc]
    simp
  obtain ⟨a1, a2⟩ := GlobalTheory.OddThetaNorm.odd_theta_norm_sigma_star Λ (isLat_of_discr_one h) h
  obtain ⟨b1, b2⟩ := GlobalTheory.OddThetaNorm.odd_theta_norm_sigma_star _ (isLat_of_discr_one h') h'
  by_cases hz : U1 Λ t (sgStar Λ) 0 = 0
  · unfold GL3Theta.th0
    rw [hU, hz]
    simp [nrm1Sq]
  · rw [a2 t hz, b2 _ (by rw [hU]; exact mul_ne_zero h0 hz), hU, norm_mul, hn, one_mul]
    congr 1
    rw [ha, ← a1] at b1
    refine (pow_left_inj₀ ?_ ?_ two_ne_zero).1 b1 <;>
      (rw [← normSq1_eq_nrm1Sq]; exact normSq1_nonneg _ _)

variable {D : D7} {δ : ℂ} {M : IntermediateField ℚ ℂ}

theorem isCurveIdeal_ccK (D : D7) : IsCurveIdeal D D.host.ccK :=
  ⟨D.host.ccK_ne_bot, Nat.Coprime.mul_right (D.host.ccK_coprime 2 (by simp)) (D.host.ccK_coprime _ (by simp))⟩

theorem exists_discriminantTwelfthRoot_of_ideal (D : D7) : ∃ δ, IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ :=
  IsAlgClosed.exists_pow_nat_eq _ (by norm_num)

theorem lamOf_one (D : D7) : lamOf D D.host.ccK 1 = baseLat D.host := by
  unfold lamOf baseLat
  simp only [one_mul]

theorem lamOf_eq_map (D : D7) (δ : ℂ) :
    lamOf D D.host.ccK δ = (baseLat D.host).map (AddMonoidHom.mulLeft δ) := by
  unfold lamOf baseLat
  rw [AddMonoidHom.map_closure]
  congr 1
  ext w
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨c, hc, rfl⟩

theorem discr_baseLat_ne_zero (D : D7) : TaylorLogMetric.discr (baseLat D.host) ≠ 0 := by
  obtain ⟨L, hL⟩ := GlobalTheory.Mem.Per.ConjCM.exists_periodPair_baseLat D.host
  exact (GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL).2.2.1

theorem delta_ne_zero (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : δ ≠ 0 := by
  rintro rfl
  apply discr_baseLat_ne_zero D
  rw [← lamOf_one, ← h]; simp

theorem discr_lamOf (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : TaylorLogMetric.discr (lamOf D D.host.ccK δ) = 1 := by
  rw [lamOf_eq_map, Model.discr_map _ _ (delta_ne_zero h), ← lamOf_one, ← h,
    inv_mul_cancel₀ (pow_ne_zero _ (delta_ne_zero h))]

theorem jLat_lamOf (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ) : jLat (lamOf D D.host.ccK δ) = jLat (baseLat D.host) := by
  rw [lamOf_eq_map, Model.jLat_map _ _ (delta_ne_zero h)]

theorem lamConj_spec {Λ : AddSubgroup ℂ} (h : TaylorLogMetric.discr Λ = 1) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) (ρ : M →ₐ[ℚ] ℂ) :
    g2 (lamConj M ρ Λ) = ρ ⟨_, h2⟩ ∧ g3 (lamConj M ρ Λ) = ρ ⟨_, h3⟩ ∧ TaylorLogMetric.discr (lamConj M ρ Λ) = 1 := by
  have h1 : ρ ⟨_, h2⟩ ^ 3 - 27 * ρ ⟨_, h3⟩ ^ 2 = 1 := by
    have : (⟨_, h2⟩ : M) ^ 3 - 27 * (⟨_, h3⟩ : M) ^ 2 = 1 := Subtype.ext h
    have e := congrArg ρ this
    rwa [map_sub, map_mul, map_pow, map_pow, map_ofNat, map_one] at e
  obtain ⟨L, e2, e3⟩ := GlobalTheory.LatticeInvariants.exists_periodPair_of_invariants (a := ρ ⟨_, h2⟩) (b := ρ ⟨_, h3⟩)
    (by rw [h1]; exact one_ne_zero)
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L L.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have l2 : liftM M (g2 Λ) = ⟨_, h2⟩ := dif_pos h2
  have l3 : liftM M (g3 Λ) = ⟨_, h3⟩ := dif_pos h3
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (liftM M (g2 Λ)) ∧ g3 Λ' = ρ (liftM M (g3 Λ)))
    ⟨L.lattice.toAddSubgroup, by rw [hd.1, e2, l2], by rw [hd.2.1, e3, l3]⟩
  have a2 : g2 (lamConj M ρ Λ) = ρ ⟨_, h2⟩ := hs.1.trans (by rw [l2])
  have a3 : g3 (lamConj M ρ Λ) = ρ ⟨_, h3⟩ := hs.2.trans (by rw [l3])
  exact ⟨a2, a3, by rw [TaylorLogMetric.discr, a2, a3, h1]⟩

def into (D : D7) (M : IntermediateField ℚ ℂ) (hL : ∀ x, D.what₂.embLL x ∈ M) : D.what₂.LL →+* M :=
  D.what₂.embLL.codRestrict M hL

theorem conjLat_eq (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (hL : ∀ x, D.what₂.embLL x ∈ M) (hM : DataIn D (tor0 D D.host.ccK δ) M) (ρ : M →ₐ[ℚ] ℂ)
    (s : D.what₂.LL →+* ℂ) (hs : ∀ x, s x = ρ (into D M hL x)) :
    ∃ ζ : ℂ, ζ ^ 12 = 1 ∧ conjLat D.host D.what₂.embLL s =
      (lamConj M ρ (lamOf D D.host.ccK δ)).map (AddMonoidHom.mulLeft ζ) := by
  obtain ⟨c1, a, ha, ha'⟩ := Model.conjLat_spec D.host hF s
  obtain ⟨a2, -, a1⟩ := lamConj_spec (discr_lamOf h) hM.2.1 hM.2.2 ρ
  refine exists_root_of_jLat_eq a1 c1 ?_
  have : into D M hL a = 1728 * (⟨_, hM.2.1⟩ : M) ^ 3 := by
    apply Subtype.ext
    change D.what₂.embLL a = 1728 * g2 (lamOf D D.host.ccK δ) ^ 3
    rw [ha, ← jLat_lamOf h, jLat, discr_lamOf h, div_one]
  rw [← ha', hs, this, jLat, a1, a2, div_one, map_mul, map_pow, map_ofNat]
  rfl

theorem data_of_fieldOK (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (hL : ∀ x, D.what₂.embLL x ∈ M) :
    (∀ τ x, embT D τ x ∈ M) ∧ g2 (lamOf D D.host.ccK δ) ^ 3 ∈ M ∧ g3 (lamOf D D.host.ccK δ) ^ 2 ∈ M := by
  obtain ⟨a, ha⟩ := hF.1
  have h1 := discr_lamOf h
  have h2 : g2 (lamOf D D.host.ccK δ) ^ 3 = D.what₂.embLL (a / 1728) := by
    rw [map_div₀, ha, ← jLat_lamOf h, jLat, h1, map_ofNat]; ring
  refine ⟨fun τ x => ?_, h2 ▸ hL _, ?_⟩
  · have := hL (D.embE (D.host.sigmaOf (D.eTau τ).1 x))
    rwa [← RingHom.comp_apply, D.embE_φ₀] at this
  · have : g3 (lamOf D D.host.ccK δ) ^ 2 = D.what₂.embLL ((a / 1728 - 1) / 27) := by
      rw [map_div₀, map_sub, ← h2, map_one, map_ofNat]
      unfold TaylorLogMetric.discr at h1
      linear_combination -h1 / 27
    exact this ▸ hL _

theorem span_gen [NumberField M] (hF : FieldOK D.host D.what₂.embLL D.embE) (hL : ∀ x, D.what₂.embLL x ∈ M)
    (τ : D.what₂.Tau) :
    Submodule.span (𝓞 M) {into D M hL (gen D.host D.embE (D.eTau τ).1)} = ellT D M τ := by
  rw [GlobalTheory.Mem.EigenLine.ellT_eq_ellLat D M ((into D M hL).comp D.embE) (fun x => by rw [← D.embE_φ₀]; rfl) τ]
  have hg := Model.gen_spec D.host hF (D.eTau τ).1
  have key : ∀ (S : Set D.what₂.LL) (N : Submodule (𝓞 M) M), (∀ y ∈ S, into D M hL y ∈ N) →
      ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) S, into D M hL y ∈ N := by
    intro S N hS y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact hS y hy
    | zero => rw [map_zero]; exact N.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact N.add_mem hx hy
    | smul r y _ hy =>
      have := N.smul_mem (RingOfIntegers.mapRingHom (into D M hL) r) hy
      rw [Algebra.smul_def, map_mul]
      exact this
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem]
    refine key _ _ ?_ _ (hg.le (Submodule.mem_span_singleton_self _))
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine key {gen D.host D.embE (D.eTau τ).1} _ ?_ _ (hg.ge (Submodule.subset_span ⟨a, ha, b, hb, rfl⟩))
    rintro _ rfl
    exact Submodule.mem_span_singleton_self _

theorem om_eq (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (hL : ∀ x, D.what₂.embLL x ∈ M) (hM : DataIn D (tor0 D D.host.ccK δ) M) (ρ : M →ₐ[ℚ] ℂ)
    (s : D.what₂.LL →+* ℂ) (hs : ∀ x, s x = ρ (into D M hL x)) (τ : D.what₂.Tau) :
    (retie D).gx.Om τ s = Real.exp (-logMet M (lamOf D D.host.ccK δ) ρ
      (into D M hL (gen D.host D.embE (D.eTau τ).1))) := by
  obtain ⟨ζ, hζ, e⟩ := conjLat_eq hF h hL hM ρ s hs
  have h0 := (retie D).gx.Om_pos τ s
  have h1 : (retie D).gx.Om τ s = _ := Model.om_eq D.host hF D.eTau τ s
  rw [e, area_map_unit _ (norm_eq_one_of_pow hζ), hs] at h1
  rw [logMet, ← Real.log_inv, inv_div, ← h1, Real.exp_log h0]

theorem thOne_sq (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (hL : ∀ x, D.what₂.embLL x ∈ M) (hM : DataIn D (tor0 D D.host.ccK δ) M) (ρ : M →ₐ[ℚ] ℂ)
    (s : D.what₂.LL →+* ℂ) (hs : ∀ x, s x = ρ (into D M hL x)) (t : ℂ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D D.host.ccK δ)) t) :
    (retie D).gx.thOne s ^ 2 = GL3Theta.normSq1 (lamConj M ρ (lamOf D D.host.ccK δ))
      (GL3Theta.th0 (lamConj M ρ (lamOf D D.host.ccK δ)) t) := by
  obtain ⟨ζ, hζ, e⟩ := conjLat_eq hF h hL hM ρ s hs
  have hc : Crv D D.host.ccK δ := ⟨isCurveIdeal_ccK D, h⟩
  have h0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hd := (lamConj_spec (discr_lamOf h) hM.2.1 hM.2.2 ρ).2.2
  have hm : ∀ c z : ℂ, c * (ζ * z) ∈ conjLat D.host D.what₂.embLL s ↔
      c * z ∈ lamConj M ρ (lamOf D D.host.ccK δ) := fun c z => by
    rw [e, mul_left_comm]
    constructor
    · rintro ⟨y, hy, hy'⟩
      exact mul_left_cancel₀ h0 hy' ▸ hy
    · exact fun hz => ⟨_, hz, rfl⟩
  have hT : ∀ z, IsHalfPt D.host.d (conjLat D.host D.what₂.embLL s) (ζ * z) ↔
      GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D D.host.ccK δ)) z := fun z => by
    unfold IsHalfPt GL3Theta.IsTwoTorsionPointUnkilled
    rw [hm, hm, hm]
  have hε := Classical.epsilon_spec (p := IsHalfPt D.host.d (conjLat D.host D.what₂.embLL s)) ⟨_, (hT t).2 ht⟩
  have hv : thAt D.host D.what₂.embLL s = Real.sqrt (GL3Theta.normSq1 (lamConj M ρ (lamOf D D.host.ccK δ))
      (GL3Theta.th0 (lamConj M ρ (lamOf D D.host.ccK δ)) t)) := by
    unfold thAt
    generalize Classical.epsilon (IsHalfPt D.host.d (conjLat D.host D.what₂.embLL s)) = u at hε
    obtain ⟨v, rfl⟩ : ∃ v, u = ζ * v := ⟨ζ⁻¹ * u, by field_simp⟩
    rw [e, meanSquare_evenTheta_twelfthRoot_invariant hd hζ, normSq1_eq_nrm1Sq, thetaZero_eq_of_isThetaZero hc hM ρ ((hT v).1 hε) ht]
  have hp := normSq_thetaZero_pos hc hM ρ ht
  change posOr1 (thAt D.host D.what₂.embLL s) ^ 2 = _
  rw [posOr1, hv, if_pos (Real.sqrt_pos.2 hp), Real.sq_sqrt hp.le]

theorem perTie_retie (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (h2 : g2 (lamOf D D.host.ccK δ) ∈ coefM D) (h3 : g3 (lamOf D D.host.ccK δ) ∈ coefM D) :
    PerTie (retie D) D.host.ccK δ := by
  have hL : ∀ x, D.what₂.embLL x ∈ coefM D := fun x => ⟨x, rfl⟩
  have hM : DataIn D (tor0 D D.host.ccK δ) (coefM D) := ⟨(data_of_fieldOK hF h hL).1, h2, h3⟩
  have hs : ∀ (s : D.what₂.LL →+* ℂ) x, s x = rhoOf D.what₂.embLL s (into D (coefM D) hL x) := fun s x =>
    (rhoOf_imEquiv D.what₂.embLL s x).symm
  exact ⟨⟨isCurveIdeal_ccK D, h⟩, hM,
    fun τ => ⟨_, span_gen hF hL τ, fun s => om_eq hF h hL hM _ s (hs s) τ⟩,
    fun s t ht => thOne_sq hF h hL hM _ s (hs s) t ht⟩

end GlobalTheory.Mem.TruePeriods
end
end

noncomputable section

namespace GlobalTheory.Mem.PeriodTie

section Lattice

open PeriodPair GlobalTheory.ConjPoint

theorem exists_action (L : PeriodPair) (σ : ℂ ≃+* ℂ) (h2 : σ (L.g₂ ^ 3) = L.g₂ ^ 3) (h3 : σ (L.g₃ ^ 2) = L.g₃ ^ 2) :
    ∃ η : ℂ, σ L.g₂ = η ^ 2 * L.g₂ ∧ σ L.g₃ = η ^ 3 * L.g₃ ∧ ∀ t, ∃ t', ∀ c : ℂ, σ c = c →
      (∀ l ∈ L.lattice, c * l ∈ L.lattice) → (c * t ∈ L.lattice ↔ c * t' ∈ L.lattice) ∧
        (c * t ∉ L.lattice → σ (℘[L] (c * t)) = η * ℘[L] (c * t')) := by
  rw [map_pow] at h2 h3
  obtain ⟨u, hu, hu2⟩ : ∃ u : ℂ, u ^ 3 = 1 ∧ σ L.g₂ = u * L.g₂ := by
    by_cases h0 : L.g₂ = 0
    · exact ⟨1, one_pow _, by simp [h0]⟩
    · exact ⟨σ L.g₂ / L.g₂, by rw [div_pow, h2, div_self (pow_ne_zero _ h0)], by field_simp⟩
  obtain ⟨η, hη, e2, e3⟩ : ∃ η : ℂ, η ≠ 0 ∧ σ L.g₂ = η ^ 2 * L.g₂ ∧ σ L.g₃ = η ^ 3 * L.g₃ := by
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with e | e
    · exact ⟨u ^ 2, pow_ne_zero _ hu0, by rw [hu2]; linear_combination -u * L.g₂ * hu,
        by rw [e]; linear_combination -(u ^ 3 + 1) * L.g₃ * hu⟩
    · exact ⟨-u ^ 2, neg_ne_zero.2 (pow_ne_zero _ hu0), by rw [hu2]; linear_combination -u * L.g₂ * hu,
        by rw [e]; linear_combination (u ^ 3 + 1) * L.g₃ * hu⟩
  obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq η⁻¹ (n := 2) (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hη (by simpa using hm.symm)
  have hmu : (m ^ 2)⁻¹ = η := by rw [hm, inv_inv]
  have H := isHomothetic_scalePeriods L m hm0
  generalize scalePeriods L m hm0 = L' at H
  have f2 : L'.g₂ = σ L.g₂ := by rw [H.g₂_eq, e2, ← hmu]; ring
  have f3 : L'.g₃ = σ L.g₃ := by rw [H.g₃_eq, e3, ← hmu]; ring
  refine ⟨η, e2, e3, fun t => ?_⟩
  obtain ⟨s, -, hc⟩ := exists_conjEquiv f2 f3
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (s (latticePoint L t))
  obtain ⟨t', rfl⟩ : ∃ t', w = m * t' := ⟨m⁻¹ * w, by field_simp⟩
  refine ⟨t', fun c hσ hc' => ?_⟩
  have := IsConj.mul f2 f3 hc' ((hc _ _).2 hw.symm)
  rw [hσ, mul_left_comm] at this
  rcases this with ⟨a, b⟩ | ⟨a, b, e, -⟩
  · exact ⟨iff_of_true a ((H _).1 b), fun h => absurd a h⟩
  · exact ⟨iff_of_false a fun h => b ((H _).2 h), fun _ => by rw [← e, H.weierstrassP_mul, hmu]⟩

theorem cubic_eq_zero (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h : t + t ∈ L.lattice) :
    4 * ℘[L] t ^ 3 - L.g₂ * ℘[L] t - L.g₃ = 0 := by
  rw [← L.derivWeierstrassP_sq t ht, (derivWeierstrassP_eq_zero_iff L ht).2 h]; simp

theorem quartic_eq_zero (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) (h : 3 * t ∈ L.lattice) :
    3 * ℘[L] t ^ 4 - 3 / 2 * L.g₂ * ℘[L] t ^ 2 - 3 * L.g₃ * ℘[L] t - L.g₂ ^ 2 / 16 = 0 := by
  have h0 : 3 • latticePoint L t = 0 := by
    rw [← latticePointHom_apply, ← map_nsmul, latticePointHom_apply, latticePoint_eq_zero_iff]
    simpa using h
  rw [latticePoint_of_notMem L ht, three_nsmul_eq_zero_iff] at h0
  simp only [WeierstrassCurve.Ψ₃, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, latticeCurve, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat] at h0
  linear_combination h0

theorem cubic_discr {G T x y : ℂ} (hx : 4 * x ^ 3 - G * x - T = 0) (hy : 4 * y ^ 3 - G * y - T = 0) (hxy : x ≠ y) :
    (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) ^ 2 = G ^ 3 - 27 * T ^ 2 := by
  have h1 : G = 4 * (x ^ 2 + x * y + y ^ 2) :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination hy - hx)
  have h2 : T = 4 * x ^ 3 - G * x := by linear_combination -hx
  rw [h2, h1]; ring

theorem quartic_discr {G T x y : ℂ} (hx : 3 * x ^ 4 - 3 / 2 * G * x ^ 2 - 3 * T * x - G ^ 2 / 16 = 0)
    (hy : 3 * y ^ 4 - 3 / 2 * G * y ^ 2 - 3 * T * y - G ^ 2 / 16 = 0) (hxy : x ≠ y) :
    (G - 3 * (x + y) ^ 2) ^ 3 = G ^ 3 - 27 * T ^ 2 := by
  have h1 : T = (x + y) * (x ^ 2 + y ^ 2) - G * (x + y) / 2 :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination (hy - hx) / 3)
  have h2 : -3 * (x * y) * ((x + y) ^ 2 - x * y) + 3 / 2 * G * (x * y) - G ^ 2 / 16 = 0 :=
    mul_left_cancel₀ (sub_ne_zero.2 hxy) (by linear_combination x * hy - y * hx)
  rw [h1]
  linear_combination 36 * (x + y) ^ 2 * h2

theorem quartic_sum {A B C x y z w : ℂ} (hx : 3 * x ^ 4 - A * x ^ 2 - B * x - C = 0)
    (hy : 3 * y ^ 4 - A * y ^ 2 - B * y - C = 0) (hz : 3 * z ^ 4 - A * z ^ 2 - B * z - C = 0)
    (hw : 3 * w ^ 4 - A * w ^ 2 - B * w - C = 0) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) : z + w = -(x + y) := by
  have k : ∀ u, 3 * u ^ 4 - A * u ^ 2 - B * u - C = 0 → x ≠ u →
      3 * (x ^ 3 + x ^ 2 * u + x * u ^ 2 + u ^ 3) - A * (x + u) - B = 0 := fun u hu h =>
    mul_left_cancel₀ (sub_ne_zero.2 h) (by linear_combination hx - hu)
  have k' : ∀ u, 3 * u ^ 4 - A * u ^ 2 - B * u - C = 0 → x ≠ u → y ≠ u →
      3 * (x ^ 2 + x * (y + u) + (y ^ 2 + y * u + u ^ 2)) - A = 0 := fun u hu h h' =>
    mul_left_cancel₀ (sub_ne_zero.2 h') (by linear_combination k y hy hxy - k u hu h)
  exact mul_left_cancel₀ (sub_ne_zero.2 hzw) (by linear_combination (k' z hz hxz hyz - k' w hw hxw hyw) / 3)

theorem exists_order_three (L : PeriodPair) {β : ℂ} {d : ℕ} (hd : 0 < d) (hβ : β ^ 2 = -d)
    (hL : ∀ l ∈ L.lattice, β * l ∈ L.lattice) :
    ∃ t, 3 * t ∈ L.lattice ∧ (β - 1) * t ∉ L.lattice ∧ (β + 1) * t ∉ L.lattice := by
  have uniq : ∀ a b : ℤ, (a : ℂ) * L.ω₁ + b * L.ω₂ = 0 → a = 0 ∧ b = 0 := fun a b h => by
    have := LinearIndependent.pair_iff.1 L.indep (a : ℝ) (b : ℝ) (by simpa using h)
    exact_mod_cast this
  obtain ⟨a, b, h1⟩ := mem_lattice.1 (hL _ L.ω₁_mem_lattice)
  obtain ⟨c, e, h2⟩ := mem_lattice.1 (hL _ L.ω₂_mem_lattice)
  obtain ⟨q1, q2⟩ := uniq (a ^ 2 + b * c + d) (b * (a + e)) (by
    push_cast
    linear_combination (a + β) * h1 + b * h2 + L.ω₁ * hβ)
  have hb : b ≠ 0 := by rintro rfl; nlinarith [sq_nonneg a]
  obtain rfl : e = -a := by have := (mul_eq_zero.1 q2).resolve_left hb; omega
  have key : ∀ x y ε : ℤ, (β - ε) * ((x * L.ω₁ + y * L.ω₂) / 3) ∈ L.lattice →
      (x * a + y * c - ε * x) % 3 = 0 ∧ (x * b - y * a - ε * y) % 3 = 0 := fun x y ε h => by
    obtain ⟨m, n, h⟩ := mem_lattice.1 h
    obtain ⟨r1, r2⟩ := uniq (x * a + y * c - ε * x - 3 * m) (x * b - y * a - ε * y - 3 * n) (by
      push_cast at h2 ⊢
      linear_combination x * h1 + y * h2 - 3 * h)
    omega
  by_contra hcon
  have k : ∀ x y : ℤ, ((x * a + y * c - 1 * x) % 3 = 0 ∧ (x * b - y * a - 1 * y) % 3 = 0) ∨
      ((x * a + y * c - (-1) * x) % 3 = 0 ∧ (x * b - y * a - (-1) * y) % 3 = 0) := fun x y => by
    by_contra h
    rw [not_or] at h
    refine hcon ⟨(x * L.ω₁ + y * L.ω₂) / 3, mem_lattice.2 ⟨x, y, by ring⟩, fun h' => h.1 (key x y 1 ?_),
      fun h' => h.2 (key x y (-1) ?_)⟩
    · simpa using h'
    · simpa using h'
  have k1 := k 1 0
  have k2 := k 0 1
  have k3 := k 1 1
  omega

theorem map_g₃ (L : PeriodPair) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) {w : ℂ} {k : ℤ} (hw : w * (1 - w) = 2 * k)
    (hs : ∀ l ∈ L.lattice, w * l ∈ L.lattice) {t : ℂ} (t2 : 2 * t ∈ L.lattice) (ta : w * t ∉ L.lattice)
    (tb : (1 - w) * t ∉ L.lattice) (σ : ℂ ≃+* ℂ) (hσ : σ w = w) (h2 : σ (L.g₂ ^ 3) = L.g₂ ^ 3)
    (h3 : σ (L.g₃ ^ 2) = L.g₃ ^ 2) : σ L.g₃ = L.g₃ := by
  obtain ⟨η, -, e3, h⟩ := exists_action L σ h2 h3
  obtain ⟨t', h⟩ := h t
  have hs' : ∀ l ∈ L.lattice, (1 - w) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem hl (hs l hl)
  obtain ⟨a1, a2⟩ := h w hσ hs
  obtain ⟨b1, b2⟩ := h (1 - w) (by rw [map_sub, map_one, hσ]) hs'
  obtain ⟨c1, -⟩ := h 2 (map_ofNat σ 2) fun l hl => by rw [two_mul]; exact add_mem hl hl
  have hlat : GlobalTheory.ThetaConj.IsLat L.lattice.toAddSubgroup := by
    refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
    ext z
    rw [AddSubgroup.mem_closure_pair, Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice]
    simp only [zsmul_eq_mul]
  have hu : t - t' ∈ L.lattice := GlobalTheory.ThetaConj.two_torsion_unique hlat w k hw t2 ta tb (c1.1 t2)
    (mt a1.2 ta) (mt b1.2 tb) hs
  have ea : ℘[L] (w * t) = ℘[L] (w * t') :=
    (weierstrassP_eq_iff L ta (mt a1.2 ta)).2 (.inl (by rw [← mul_sub]; exact hs _ hu))
  have eb : ℘[L] ((1 - w) * t) = ℘[L] ((1 - w) * t') :=
    (weierstrassP_eq_iff L tb (mt b1.2 tb)).2 (.inl (by rw [← mul_sub]; exact hs' _ hu))
  have fa := a2 ta
  have fb := b2 tb
  rw [← ea] at fa
  rw [← eb] at fb
  have ha2 : w * t + w * t ∈ L.lattice := by convert hs _ t2 using 1; ring
  have hb2 : (1 - w) * t + (1 - w) * t ∈ L.lattice := by convert hs' _ t2 using 1; ring
  have hne : ℘[L] (w * t) ≠ ℘[L] ((1 - w) * t) := fun e => by
    have ht : t ∈ L.lattice := by
      rcases (weierstrassP_eq_iff L ta tb).1 e with e | e
      · convert add_mem e hb2 using 1; ring
      · convert e using 1; ring
    exact ta (hs _ ht)
  have hd := cubic_discr (cubic_eq_zero L ta ha2) (cubic_eq_zero L tb hb2) hne
  rw [hΔ] at hd
  generalize ℘[L] (w * t) = x at *
  generalize ℘[L] ((1 - w) * t) = y at *
  have hP : σ (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) = η ^ 3 * (4 * ((x - y) * (2 * x + y) * (x + 2 * y))) := by
    simp only [map_mul, map_add (f := _), map_sub, map_ofNat, fa, fb]; ring
  have : η ^ 3 = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hd.trans (one_pow 2).symm) with e | e <;> rw [e] at hP
    · simpa using hP.symm
    · simpa using hP.symm
  rw [e3, this, one_mul]

theorem exists_map_g₂ (L : PeriodPair) (hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1) {β : ℂ} {d : ℕ} (hd : d % 3 ≠ 0)
    (hβ : β ^ 2 = -d) (hs : ∀ l ∈ L.lattice, β * l ∈ L.lattice) :
    ∃ u : ℂ, u ^ 3 = 1 ∧ ∀ σ : ℂ ≃+* ℂ, σ β = β → σ (L.g₂ ^ 3) = L.g₂ ^ 3 → σ (L.g₃ ^ 2) = L.g₃ ^ 2 →
      σ (u * L.g₂) = u * L.g₂ := by
  have hββ : ∀ t, 3 * t ∈ L.lattice → β * (β * t) - t ∈ L.lattice ∨ β * (β * t) + t ∈ L.lattice := fun t ht => by
    obtain ⟨n, hn | hn⟩ : ∃ n : ℕ, d + 1 = 3 * n ∨ d = 3 * n + 1 := by
      rcases (show d % 3 = 1 ∨ d % 3 = 2 by omega) with h | h
      · exact ⟨d / 3, .inr (by omega)⟩
      · exact ⟨d / 3 + 1, .inl (by omega)⟩
    · have hn' : (d : ℂ) + 1 = 3 * n := by exact_mod_cast hn
      left
      convert neg_mem (nsmul_mem ht n) using 1
      rw [nsmul_eq_mul]; linear_combination t * hβ - t * hn'
    · have hn' : (d : ℂ) = 3 * n + 1 := by exact_mod_cast hn
      right
      convert neg_mem (nsmul_mem ht n) using 1
      rw [nsmul_eq_mul]; linear_combination t * hβ - t * hn'
  have h3β : ∀ t, 3 * t ∈ L.lattice → 3 * (β * t) ∈ L.lattice := fun t ht => by
    rw [mul_left_comm]; exact hs _ ht
  have hnβ : ∀ t, 3 * t ∈ L.lattice → t ∉ L.lattice → β * t ∉ L.lattice := fun t ht hn h => hn <| by
    rcases hββ t ht with e | e
    · simpa using sub_mem (hs _ h) e
    · simpa using sub_mem e (hs _ h)
  have hA : ∀ t, 3 * t ∈ L.lattice → t ∉ L.lattice → ℘[L] (β * (β * t)) = ℘[L] t := fun t ht hn =>
    (weierstrassP_eq_iff L (hnβ _ (h3β t ht) (hnβ t ht hn)) hn).2 (hββ t ht)
  have hB : ∀ s t, 3 * s ∈ L.lattice → s ∉ L.lattice → 3 * t ∈ L.lattice → t ∉ L.lattice → ℘[L] s = ℘[L] t →
      ℘[L] (β * s) = ℘[L] (β * t) := fun s t s3 sn t3 tn e => by
    rw [weierstrassP_eq_iff L (hnβ s s3 sn) (hnβ t t3 tn), ← mul_sub, ← mul_add]
    exact ((weierstrassP_eq_iff L sn tn).1 e).imp (hs _) (hs _)
  have hs1 : ∀ l ∈ L.lattice, (β - 1) * l ∈ L.lattice := fun l hl => by
    rw [sub_mul, one_mul]; exact sub_mem (hs l hl) hl
  have hs2 : ∀ l ∈ L.lattice, (β + 1) * l ∈ L.lattice := fun l hl => by
    rw [add_mul, one_mul]; exact add_mem (hs l hl) hl
  have hne : ∀ t, 3 * t ∈ L.lattice → (β - 1) * t ∉ L.lattice → (β + 1) * t ∉ L.lattice →
      ℘[L] t ≠ ℘[L] (β * t) := fun t ht a b e => by
    have tn : t ∉ L.lattice := fun h => a (hs1 _ h)
    rcases (weierstrassP_eq_iff L (hnβ t ht tn) tn).1 e.symm with e | e
    · exact a (by convert e using 1; ring)
    · exact b (by convert e using 1; ring)
  obtain ⟨t, t3, ta, tb⟩ := exists_order_three L (Nat.pos_of_ne_zero (by rintro rfl; simp at hd)) hβ hs
  have tn : t ∉ L.lattice := fun h => ta (hs1 _ h)
  have hx := quartic_eq_zero L tn t3
  have hy := quartic_eq_zero L (hnβ t t3 tn) (h3β t t3)
  have hv := quartic_discr hx hy (hne t t3 ta tb)
  rw [hΔ] at hv
  refine ⟨(L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2)⁻¹, by rw [inv_pow, hv, inv_one], fun σ hσ h2 h3 => ?_⟩
  obtain ⟨η, e2, -, h⟩ := exists_action L σ h2 h3
  obtain ⟨t', h⟩ := h t
  have t3' := (h 3 (map_ofNat σ 3) fun l hl => by simpa using nsmul_mem hl 3).1.1 t3
  have ta' := mt (h (β - 1) (by rw [map_sub, map_one, hσ]) hs1).1.2 ta
  have tb' := mt (h (β + 1) (by rw [map_add (f := _), map_one, hσ]) hs2).1.2 tb
  have tn' : t' ∉ L.lattice := fun h => ta' (hs1 _ h)
  have fx := (h 1 (map_one σ) fun l hl => by simpa using hl).2 (by simpa using tn)
  rw [one_mul, one_mul] at fx
  have fy := (h β hσ hs).2 (hnβ t t3 tn)
  have hsq : (℘[L] t' + ℘[L] (β * t')) ^ 2 = (℘[L] t + ℘[L] (β * t)) ^ 2 := by
    by_cases c1 : ℘[L] t = ℘[L] t'
    · rw [hB _ _ t3 tn t3' tn' c1, c1]
    by_cases c2 : ℘[L] t = ℘[L] (β * t')
    · rw [hB _ _ t3 tn (h3β _ t3') (hnβ _ t3' tn') c2, hA _ t3' tn', c2, add_comm]
    have c3 : ℘[L] (β * t) ≠ ℘[L] t' := fun e => c2 (by
      rw [← hB _ _ (h3β _ t3) (hnβ _ t3 tn) t3' tn' e, hA _ t3 tn])
    have c4 : ℘[L] (β * t) ≠ ℘[L] (β * t') := fun e => c1 (by
      rw [← hA _ t3 tn, hB _ _ (h3β _ t3) (hnβ _ t3 tn) (h3β _ t3') (hnβ _ t3' tn') e, hA _ t3' tn'])
    rw [quartic_sum hx hy (quartic_eq_zero L tn' t3') (quartic_eq_zero L (hnβ _ t3' tn') (h3β _ t3'))
      (hne t t3 ta tb) c1 c2 c3 c4 (hne t' t3' ta' tb'), neg_sq]
  have hσv : σ (L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2) = η ^ 2 * (L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2) := by
    rw [map_sub, map_mul, map_pow, map_add (f := _), map_ofNat, fx, fy, e2, ← hsq]; ring
  generalize L.g₂ - 3 * (℘[L] t + ℘[L] (β * t)) ^ 2 = v at hv hσv
  have hv0 : v ≠ 0 := by rintro rfl; simp at hv
  have hη : η ^ 2 ≠ 0 := left_ne_zero_of_mul (hσv ▸ (map_ne_zero σ).2 hv0)
  rw [map_mul, map_inv₀, hσv, e2, mul_inv, mul_mul_mul_comm, inv_mul_cancel₀ hη, one_mul]

end Lattice

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.Mem.Per GlobalTheory.Glob GlobalTheory.Mem.TruePeriods

theorem exists_delta_data (D : D7) (hF : FieldOK D.host D.what₂.embLL D.embE) :
    ∃ δ, IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ ∧ g2 (lamOf D D.host.ccK δ) ∈ coefM D ∧ g3 (lamOf D D.host.ccK δ) ∈ coefM D := by
  obtain ⟨δ, h⟩ := exists_discriminantTwelfthRoot_of_ideal D
  have hc : Crv D D.host.ccK δ := ⟨isCurveIdeal_ccK D, h⟩
  obtain ⟨-, m2, m3⟩ := data_of_fieldOK (M := coefM D) hF h fun x => ⟨x, rfl⟩
  obtain ⟨hlat, -, hΔ, -, hO⟩ :=
    GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 _ δ hc
  obtain ⟨L, hL⟩ := GlobalTheory.ThetaConj.IsLat.exists_periodPair hlat
  obtain ⟨e2, e3, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  rw [TaylorLogMetric.discr, e2, e3] at hΔ
  rw [e2] at m2
  rw [e3] at m3
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have mw : w0 D ∈ coefM D := ⟨D.embE _, by rw [← ha, ← D.embE_φ₀]; rfl⟩
  have hs : ∀ l ∈ L.lattice, w0 D * l ∈ L.lattice := fun l hl => (hL _).1 (ha ▸ hO a l ((hL l).2 hl))
  have key : ∀ x : ℂ, (∀ σ : ℂ ≃+* ℂ, (∀ y ∈ coefM D, σ y = y) → σ x = x) → x ∈ coefM D := fun x hx => by
    obtain ⟨y, rfl⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := coefM D) x
      fun σ => hx σ.toRingEquiv fun y hy => σ.commutes ⟨y, hy⟩
    exact y.2
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  obtain ⟨t, ht⟩ := (GlobalTheory.TwoTorsionPt.exists_point D _ δ hc).1
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff, hL, hL, hL] at ht
  have n3 : L.g₃ ∈ coefM D := key _ fun σ hσ =>
    map_g₃ L hΔ hk hs ht.1 ht.2.1 ht.2.2 σ (hσ _ mw) (hσ _ m2) (hσ _ m3)
  have hd : D.host.d % 3 ≠ 0 := fun h3 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three D.host.hyp.2.1).1 (Nat.dvd_of_mod_eq_zero h3)
    have := D.host.hyp.2.2.2.1
    omega
  have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = D.host.d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  obtain ⟨u, hu, hσu⟩ := exists_map_g₂ L hΔ (β := 2 * w0 D - 1) hd
    (by unfold w0; linear_combination ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 * Complex.I_sq - hsq)
    fun l hl => by
      convert sub_mem (add_mem (hs l hl) (hs l hl)) hl using 1; ring
  have n2 : u * L.g₂ ∈ coefM D := key _ fun σ hσ =>
    hσu σ (by rw [map_sub, map_mul, map_ofNat, map_one, hσ _ mw]) (hσ _ m2) (hσ _ m3)
  have hu0 : u ^ 2 ≠ 0 := by
    refine pow_ne_zero _ ?_
    rintro rfl; simp at hu
  have hmap : lamOf D D.host.ccK (u ^ 2 * δ) = (lamOf D D.host.ccK δ).map (AddMonoidHom.mulLeft (u ^ 2)) := by
    rw [lamOf_eq_map, lamOf_eq_map, AddSubgroup.map_map]
    congr 1
    ext; simp [mul_assoc]
  refine ⟨u ^ 2 * δ, ?_, ?_, ?_⟩
  · unfold IsDiscriminantTwelfthRootOfIdealLattice at h ⊢
    rw [mul_pow, h, show (u ^ 2) ^ 12 = (u ^ 3) ^ 8 by ring, hu, one_pow, one_mul]
  · rw [← e2] at n2
    convert n2 using 1
    unfold g2
    rw [hmap, Model.eisG_map _ _ hu0, inv_eq_of_mul_eq_one_right (b := u)
      (by rw [show (u ^ 2) ^ (2 * 2) * u = (u ^ 3) ^ 3 by ring, hu, one_pow])]
    ring
  · rw [← e3] at n3
    convert n3 using 1
    unfold g3
    rw [hmap, Model.eisG_map _ _ hu0, show (u ^ 2) ^ (2 * 3) = (u ^ 3) ^ 4 by ring, hu]
    simp

theorem isTheta0_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t : ℂ} (h : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t) : GL3Theta.IsTheta0 D.host.d (lamOf D cc δ) (GL3Theta.th0 (lamOf D cc δ) t) := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HalfPeriodTheta.theta_signed_translation D (GlobalTheory.InducedType.induced_type D).1 cc δ h t ht
  refine ⟨h1, fun x hx z => ?_, div_self fun h0 => ?_⟩
  · obtain ⟨m, hm, e⟩ := h2 x hx
    have : Real.sqrt D.host.d / 2 * (GL3Theta.hf1 (lamOf D cc δ) x x).re = m := by
      rw [← hm, q1, GL3Theta.hf1, Complex.mul_conj, Complex.div_ofReal_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [GL3Theta.al1, this, round_intCast, e]
  · apply GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ t h ht
    unfold GL3Theta.th0
    rw [h0]
    simp [nrm1Sq]

theorem isTheta0_conj {d : ℕ} {Λ : AddSubgroup ℂ} {G : ℂ → ℂ} (h : GL3Theta.IsTheta0 d Λ G) :
    GL3Theta.IsTheta0 d (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ ∘ G ∘ starRingEnd ℂ) := by
  refine ⟨fun z => differentiableAt_conj_conj_iff.mpr (h.1 _), ?_, by simp [h.2.2]⟩
  rintro _ ⟨x, hx, rfl⟩ z
  have e : (starRingEnd ℂ).toAddMonoidHom x = starRingEnd ℂ x := rfl
  have e' : GL3Theta.al1 d (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ x) =
      starRingEnd ℂ (GL3Theta.al1 d Λ x) := by
    unfold GL3Theta.al1 GL3Theta.hf1
    rw [GlobalTheory.ThetaConj.area_conj, Complex.conj_conj, mul_comm ((starRingEnd ℂ) x) x, map_zpow₀, map_neg, map_one]
  rw [e, e', GlobalTheory.ThetaConj.thetaTranslate_conjugateLattice]
  simp only [Function.comp]
  rw [← map_mul, h.2.1 x hx]

theorem isTheta0_lamConj {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t : ℂ} {M : IntermediateField ℚ ℂ} (h : Crv D cc δ)
    (hM : DataIn D (tor0 D cc δ) M) (ρ : M →ₐ[ℚ] ℂ) (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    GL3Theta.IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) := by
  obtain ⟨cc', δ', h', e | e⟩ := lamConj_cases h hM ρ
  · rw [e] at ht ⊢; exact isTheta0_lamOf h' ht
  · have h1 := GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht
    rw [e] at h1
    have h2 := isTheta0_conj (isTheta0_lamOf h' h1)
    rw [← GlobalTheory.ThetaConj.evenTheta_conjugateLattice (GlobalTheory.ThetaConj.isLat_lamOf h'), ← e, GlobalTheory.ThetaConj.conj_conj_lat,
      Complex.conj_conj] at h2
    exact h2


open Formalism.L2.GlobalTheoryTheory in
theorem ties_of_data {D : D7} {δ : ℂ} (hF : FieldOK D.host D.what₂.embLL D.embE) (h : IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK δ)
    (h2 : g2 (lamOf D D.host.ccK δ) ∈ coefM D) (h3 : g3 (lamOf D D.host.ccK δ) ∈ coefM D) :
    OmegaCompatible (retie D) δ ∧ DataIn D (tor0 D D.host.ccK δ) (coefM D) ∧ ∀ s : D.what₂.LL →+* ℂ,
      ∃ G, IsTheta0 D.host.d (lamConj (coefM D) (conjOf (imEquiv D.what₂.embLL).toRingEquiv s)
          (lamOf D D.host.ccK δ)) G ∧
        (retie D).gx.thOne s ^ 2 = normSq1 (lamConj (coefM D) (conjOf (imEquiv D.what₂.embLL).toRingEquiv s)
          (lamOf D D.host.ccK δ)) G := by
  obtain ⟨hc, hM, -, hth⟩ := perTie_retie hF h h2 h3
  refine ⟨⟨coefM D, inferInstance, (imEquiv D.what₂.embLL).toRingEquiv, fun _ => rfl, hM, fun τ => ?_⟩, hM,
    fun s => ?_⟩
  · have hL : ∀ x, D.what₂.embLL x ∈ coefM D := fun x => ⟨x, rfl⟩
    refine ⟨_, (span_gen hF hL τ).symm, fun s : D.what₂.LL →+* ℂ => ?_⟩
    have hs : ∀ x, s x = rhoOf D.what₂.embLL s (into D (coefM D) hL x) := fun x =>
      (rhoOf_imEquiv D.what₂.embLL s x).symm
    obtain ⟨ζ, hζ, e⟩ := conjLat_eq hF h hL hM _ s hs
    have h1 : (retie D).gx.Om τ s = _ := Model.om_eq D.host hF D.eTau τ s
    rw [e, area_map_unit _ (norm_eq_one_of_pow hζ), hs] at h1
    rw [h1, inv_div]
    rfl
  · obtain ⟨t, ht⟩ := exists_isThetaZero hc hM (rhoOf D.what₂.embLL s)
    exact ⟨_, (is_theta_zero_iff _ _ _).1 (isTheta0_lamConj hc hM _ ht), hth s t ht⟩

end GlobalTheory.Mem.PeriodTie
