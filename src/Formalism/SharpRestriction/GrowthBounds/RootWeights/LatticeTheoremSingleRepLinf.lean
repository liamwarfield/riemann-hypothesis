module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorTraceFormula
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightEntriesBetweenExtremeHighest
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.ContravariantIsotypicOrthogonal

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightMemWeightsOfNeZero
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem weight_mem_weights_of_ne_zero {E : GLOps n (KK O) V} {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) :
    nu ∈ wtsOf E ⊤ := by
  show weightSp E nu ⊓ ⊤ ≠ ⊥
  rw [inf_top_eq]
  intro hb
  rw [hb] at hx
  exact h0 ((Submodule.mem_bot _).mp hx)

theorem weight_difference_le_ell [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) (a c : Fin n) :
    nu a - nu c ≤ (ellOf E ⊤ : ℤ) := by
  by_cases hac : a = c
  · subst hac
    simp
  by_cases hpos : 0 < nu a - nu c
  · have hne : weightSp E nu ≠ ⊥ := by
      intro hb
      rw [hb] at hx
      exact h0 ((Submodule.mem_bot _).mp hx)
    obtain ⟨j, hy0, hytop⟩ := offdiag_string_reaches_top_nonzero hE hx h0 hac
    have hyw := integral_operator_pow_shifts_weight hE hx a c j
    generalize ((E a c) ^ j) x = y at hy0 hytop hyw
    have hmu : (nu + (j : ℤ) • rootW a c) a - (nu + (j : ℤ) • rootW a c) c = nu a - nu c + 2 * j := by
      simp only [rootW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply, hac,
        Ne.symm hac, if_true, if_false]
      ring
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = nu a - nu c + 2 * j :=
      ⟨(nu a - nu c + 2 * j).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hcomm : ∀ w : V, E a c (E c a w) = E c a (E a c w) + (E a a w - E c c w) := by
      intro w
      have h1 := hE.1 a c c a
      rw [if_pos rfl, if_pos rfl] at h1
      have h2 := LinearMap.congr_fun h1 w
      first
        | simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
        | simp only [LinearMap.sub_apply, LinearMap.mul_apply] at h2
      rw [← h2]
      abel
    have hps : ∀ (r : ℕ) (w : V), E c a (((E c a) ^ r) w) = ((E c a) ^ (r + 1)) w := by
      intro r w
      rw [pow_succ']
      rfl
    have hwt : ∀ r : ℕ, E a a (((E c a) ^ r) y) - E c c (((E c a) ^ r) y) =
        (((N : ℤ) - 2 * (r : ℤ) : ℤ) : KK O) • ((E c a) ^ r) y := by
      intro r
      have hm := integral_operator_pow_shifts_weight hE hyw c a r
      simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply] at hm
      have ha := sub_eq_zero.mp (hm a)
      have hc' := sub_eq_zero.mp (hm c)
      simp only [Module.End.one_apply] at ha hc'
      rw [ha, hc', ← sub_smul]
      congr 1
      have hω : (nu + (j : ℤ) • rootW a c + (r : ℤ) • rootW c a) a -
          (nu + (j : ℤ) • rootW a c + (r : ℤ) • rootW c a) c = (N : ℤ) - 2 * (r : ℤ) := by
        simp [rootW, Pi.single_apply, hac, Ne.symm hac]
        omega
      rw [← hω]
      push_cast
      ring
    have hkey : ∀ r : ℕ, E a c (((E c a) ^ (r + 1)) y) =
        ((((r + 1 : ℕ) : KK O) * ((N : KK O) - r))) • ((E c a) ^ r) y := by
      intro r
      induction r with
      | zero =>
        have h0' := hwt 0
        have e1 : ((E c a) ^ (0 + 1)) y = E c a y := by rw [zero_add, pow_one]
        rw [e1, hcomm, hytop, map_zero, zero_add]
        simp only [pow_zero, Module.End.one_apply] at h0' ⊢
        rw [h0']
        congr 1
        push_cast
        ring
      | succ r ih =>
        rw [← hps (r + 1) y, hcomm, ih, map_smul, hps, hwt (r + 1), ← add_smul]
        congr 1
        push_cast
        ring
    have hz : ∀ r : ℕ, r ≤ N → ((E c a) ^ r) y ≠ 0 := by
      intro r
      induction r with
      | zero => intro _; simpa using hy0
      | succ r ih =>
        intro hr hz0
        have hk := hkey r
        rw [hz0, map_zero] at hk
        have hc : (((r + 1 : ℕ) : KK O) * ((N : KK O) - r)) ≠ 0 := by
          refine mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero r) ?_
          have e : ((N : KK O) - r) = ((N - r : ℤ) : KK O) := by push_cast; ring
          rw [e]
          exact_mod_cast (show (N - r : ℤ) ≠ 0 by omega)
        exact ih (by omega) ((smul_eq_zero.mp hk.symm).resolve_left hc)
    have hzN := hz N le_rfl
    have hzw := integral_operator_pow_shifts_weight hE hyw c a N
    have hmem : N ∈ {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule (KK O) V), ∃ nu ∈ wtsOf E (⊤ : Submodule (KK O) V),
        ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
      refine ⟨nu + (j : ℤ) • rootW a c, weight_mem_weights_of_ne_zero hyw hy0,
        nu + (j : ℤ) • rootW a c + (N : ℤ) • rootW c a, weight_mem_weights_of_ne_zero hzw hzN, a, c, hac, ?_⟩
      funext i
      simp only [rootW, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hle : N ≤ ellOf E ⊤ := by
      unfold ellOf
      exact le_csSup (root_differences_bddAbove E hE ⊤) hmem
    have hle' : (N : ℤ) ≤ (ellOf E ⊤ : ℤ) := by exact_mod_cast hle
    omega
  · push_neg at hpos
    have : (0 : ℤ) ≤ (ellOf E ⊤ : ℤ) := Nat.cast_nonneg _
    omega

theorem linf_homRep_le_ell_add [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V)
    (hE : IsGLRep E) (lam : Fin n → ℤ) (hdom : Dominant lam) (v0 : V) (hv0 : IsHWV E lam v0)
    (hL : IsSubrepresentation E (cyclicSubmodule E v0)) :
    linf (homRepresentation (restrictRepresentation E _ hL) E) ⊤ ≤ ellOf E ⊤ + ellWt lam := by
  refine csSup_le' ?_
  rintro k ⟨ka, hk, hsum, a, rfl⟩
  have hres := restrictRepresentation_isRep E hE _ hL
  have hne : weightSp (homRepresentation (restrictRepresentation E _ hL) E) ka ≠ ⊥ := by
    intro h0; apply hk; rw [h0, bot_inf_eq]
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hex : ∃ nu, ∃ x ∈ weightSp (restrictRepresentation E _ hL) nu, g x ≠ 0 := by
    by_contra hc
    apply hg0
    refine linearMap_ext_on_weightSpaces _ hres g 0 fun nu x hx => ?_
    by_contra h1
    exact hc ⟨nu, x, hx, h1⟩
  obtain ⟨nu, x, hx, hgx⟩ := hex
  have hx0 : x ≠ 0 := by
    intro h0
    apply hgx
    rw [h0, map_zero]
  have hgw : g x ∈ weightSp E (ka + nu) := by
    rw [mem_weightSp_iff_diagonal_apply]
    intro c
    have h1 := congrArg (fun f : cyclicSubmodule E v0 →ₗ[KK O] V => f x) ((mem_weightSp_iff_diagonal_apply _ _ g).1 hg c)
    simp only [homRepresentation_apply, LinearMap.smul_apply] at h1
    have h2 : restrictRepresentation E _ hL c c x = (nu c : KK O) • x := (mem_weightSp_iff_diagonal_apply _ _ x).1 hx c
    rw [h2, map_smul, sub_eq_iff_eq_add] at h1
    rw [h1, Pi.add_apply, Int.cast_add, add_smul]
  have hI : IsIrrHW (restrictRepresentation E _ hL) lam (⟨v0, self_mem_cyclicSubmodule E v0⟩ : cyclicSubmodule E v0) :=
    ⟨hres, hdom, highest_vector_restrict E _ hL lam v0 (self_mem_cyclicSubmodule E v0) hv0, cyclicSubmodule_restrict_eq_top E v0 hL⟩
  have hent := fun c => weight_entries_between_extreme_highest hI hx hx0 c
  have hdif := fun c c' => weight_difference_le_ell hE hgw hgx c c'

  have hc1 : ∃ c, ka c ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < ∑ c, ka c := Finset.sum_pos (fun c _ => hcon c) ⟨0, Finset.mem_univ _⟩
    omega
  have hc2 : ∃ c, 0 ≤ ka c := by
    by_contra hcon
    push Not at hcon
    have : ∑ c, ka c < 0 := Finset.sum_neg (fun c _ => hcon c) ⟨0, Finset.mem_univ _⟩
    omega
  obtain ⟨c1, hc1⟩ := hc1
  obtain ⟨c2, hc2⟩ := hc2
  have e1 := hdif a c1
  have e2 := hdif c2 a
  have e3 := hent a
  have e4 := hent c1
  have e5 := hent c2
  simp only [Pi.add_apply] at e1 e2
  unfold ellWt
  omega

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem lattice_theorem_single_rep_linf (h : InvariantDenominatorLinftyBound) (hTop : IsotypicSubmodulesSpanTop) (hRes : RestrictionIsRepresentation) (hHom : HomSpaceIsRepresentation) (hInv : InvariantProjectionExists)
    (hTh : IsotypicProjectorTraceFormula) (hB : LatticeAdaptedBasisExists) (hLat : HomLatticeDividedPowerStable)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) (n : ℕ) [NeZero n] (V : Type) [AddCommGroup V] [Module (KK O) V] [Module O V]
    [IsScalarTower O (KK O) V] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V) (hE : IsGLRep E)
    (M : Submodule O V) (hM : UZLattice E M) (hMQ : MQ (K := KK O) M = ⊤)
    (lam : Fin n → ℤ) (hdom : Dominant lam) (e : Module.End (KK O) V) (he : IsIsoProj E lam e) (x : V)
    (hx : x ∈ M) :
    ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M) + ellWt lam))) • e x ∈ M := by
  have : CharZero (KK O) := charZero_fraction_field_of_setting S hG.prime
  by_cases hv : ∃ v0, IsHWV E lam v0
  · obtain ⟨v0, hv0⟩ := hv
    have hL := cyclicSubmodule_isSubrepresentation E v0
    obtain ⟨d, b, hbM, hbc⟩ := hB O V M hM.2 hMQ (cyclicSubmodule E v0)
    have hEH : IsGLRep (homRepresentation (restrictRepresentation E _ hL) E) :=
      hHom n (KK O) _ V _ E (hRes n (KK O) V E hE _ hL) hE
    obtain ⟨P, hP⟩ := hInv n (KK O) _ _ hEH
    obtain ⟨hl1, hl2⟩ := hLat O n V E hE M hM hMQ _ hL
    have key : ∀ i, ((p : O) ^ (N0 n * deF p n (ellOf E (MQ M) + ellWt lam))) •
        P ((b.coord i).smulRight x) (b i) ∈ M := by
      intro i
      have hf : (b.coord i).smulRight x ∈ homLattice M (cyclicSubmodule E v0) := by
        intro y hy
        obtain ⟨o, ho⟩ := hbc y hy i
        rw [LinearMap.smulRight_apply, ho, algebraMap_smul]
        exact M.smul_mem _ hx
      have h1 := h p n' O S hG n _ _ hEH _ hl1 hl2 P hP _ hf
      have h2 := h1 (b i) (hbM i)
      rw [LinearMap.smul_apply] at h2
      refine pow_smul_mem_of_le' M _ ?_ h2
      refine Nat.mul_le_mul_left _ (log_bound_monotone p n ?_)
      rw [hl2, hMQ]
      exact linf_homRep_le_ell_add E hE lam hdom v0 hv0 hL
    rw [← hTh n (KK O) V E hE lam e he v0 hv0 hL P hP (Fin d) b x, Nat.cast_smul_eq_nsmul, smul_comm,
      Finset.smul_sum]
    exact M.smul_of_tower_mem _ (M.sum_mem fun i _ => key i)
  · have h0 : e x = 0 := by
      have hle : (⨆ mu, isoSub E mu) ≤ LinearMap.ker e := by
        refine iSup_le fun mu => ?_
        by_cases hmu : mu = lam
        · subst hmu
          refine Submodule.span_le.2 ?_
          rintro y ⟨u, _, v, hv', _⟩
          exact absurd ⟨v, hv'⟩ hv
        · intro y hy
          exact he.2 mu hmu y hy
      have : x ∈ (⨆ mu, isoSub E mu) := by rw [hTop n (KK O) V E hE]; trivial
      exact hle this
    rw [h0, smul_zero]; exact M.zero_mem

theorem isotypicProjectorTheoremField_of_linfty_bound (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (h : InvariantDenominatorLinftyBound) : IsotypicProjectorTheoremField D := by
  intro p n' O _ _ _ S hG n _ V _ _ _ _ _ E hE M hM hMQ Sw hSw e he x hx
  rw [Finset.smul_sum]
  refine M.sum_mem fun lam hlam => ?_
  have h1 := lattice_theorem_single_rep_linf h (isotypic_submodules_span_top D h2) restriction_is_representation hom_space_is_representation (invariant_projection_exists D h2) (isotypic_projector_trace_formula D h2)
    lattice_adapted_basis_exists hom_lattice_dividedPower_stable p n' O S hG n V E hE M hM hMQ lam (hSw lam hlam) (e lam) (he lam hlam) x hx
  refine pow_smul_mem_of_le' M _ ?_ h1
  exact Finset.le_sup (f := fun lam => N0 n * deF p n (ellOf E (MQ M) + ellWt lam)) hlam

end Formalism.MainNotions.G.GLWeightTheory
