module

public import Formalism.PeriodIntegrals.HermitianGenusExtension.SemilocalHermitianLattices.FiniteDimensionalOfOrtho
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTotalMassLeGenericMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermOverRelationUniqueness

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormal
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.MaxExists

private lemma isIntLat_of_isUnimodular {K V : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {h : V →ₗ⋆[K] V →ₗ[K] K} {M : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K M)
    (hU : _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M) : _root_.GlobalTheory.Mass.IsIntLat h M := by
  unfold _root_.GlobalTheory.Mass.IsIntLat
  refine ⟨hL, ?_⟩
  unfold _root_.Formalism.HermitianLatticesTheory.IsIntegralLat
  intro x hx y hy
  unfold _root_.Formalism.HermitianLatticesTheory.IsUnimodular at hU
  have hy' : y ∈ _root_.Formalism.HermitianLatticesTheory.dual h M := by rw [hU]; exact hy
  exact (_root_.Formalism.HermitianLatticesTheory.dualBasic_mem_dual h M y).1 hy' x hx

theorem _root_.GlobalTheory.Mass.MaxExists.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M → ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M → _root_.GlobalTheory.Mass.IsMaxLat h M ∧ _root_.GlobalTheory.Mass.badP h M = ∅ ∧ _root_.GlobalTheory.Mass.lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), _root_.Formalism.HermitianLatticesTheory.IsOrthoLattice h M n → Submodule.IsLattice K M ∧ _root_.Formalism.HermitianLatticesTheory.IsUnimodular h M ∧ Module.finrank K V = n) := by
  intro K V _ _ _ _ _ _ _ _ h hK hS hN
  have D := fun M hM => _root_.GlobalTheory.Mass.DiscOrder.main K V h hK hS hN M hM
  refine ⟨?_, ?_, ?_⟩
  · have key : ∀ n : ℕ, ∀ M : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h M →
        _root_.GlobalTheory.Mass.discN h M = n →
        ∃ M', _root_.GlobalTheory.Mass.IsMaxLat h M' ∧ M ≤ M' := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro M hM hn
        by_cases hmax : ∀ N : Submodule (𝓞 K) V, _root_.GlobalTheory.Mass.IsIntLat h N → M ≤ N → N = M
        · exact ⟨M, by unfold _root_.GlobalTheory.Mass.IsMaxLat; exact ⟨hM, hmax⟩, le_rfl⟩
        · push_neg at hmax
          obtain ⟨N, hNi, hMN, hne⟩ := hmax
          obtain ⟨hidx0, hdisc⟩ := (D M hM).2.2.1 N hNi hMN
          have hidx1 : _root_.GlobalTheory.Mass.idxN N M ≠ 1 := by
            intro h1
            exact hne (le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1) hMN)
          have hNpos : 0 < _root_.GlobalTheory.Mass.discN h N :=
            Nat.pos_of_ne_zero (D N hNi).1
          have hlt : _root_.GlobalTheory.Mass.discN h N < n := by
            rw [← hn, hdisc]
            have h2 : 2 ≤ _root_.GlobalTheory.Mass.idxN N M := by omega
            have h4 : 1 < _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
              Nat.one_lt_pow (by norm_num) (by omega)
            calc _root_.GlobalTheory.Mass.discN h N
                = _root_.GlobalTheory.Mass.discN h N * 1 := (mul_one _).symm
              _ < _root_.GlobalTheory.Mass.discN h N * _root_.GlobalTheory.Mass.idxN N M ^ 2 :=
                  Nat.mul_lt_mul_of_pos_left h4 hNpos
          obtain ⟨M', hM', hNM'⟩ := ih _ hlt N hNi rfl
          exact ⟨M', hM', hMN.trans hNM'⟩
    exact fun M hM => key _ M hM rfl
  · intro M hL hU
    have hI := isIntLat_of_isUnimodular hL hU
    have hD1 : _root_.GlobalTheory.Mass.discN h M = 1 := ((D M hI).2.1).2 hU
    have hbad : _root_.GlobalTheory.Mass.badP h M = ∅ := by
      unfold _root_.GlobalTheory.Mass.badP
      ext P
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hP
      refine (D M hI).2.2.2.2.1 P hP ?_
      rw [hD1, Nat.cast_one]
      exact fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
    refine ⟨?_, hbad, ?_⟩
    · unfold _root_.GlobalTheory.Mass.IsMaxLat
      refine ⟨hI, fun N hNi hMN => ?_⟩
      obtain ⟨_, hdisc⟩ := (D M hI).2.2.1 N hNi hMN
      rw [hD1] at hdisc
      have h1 : _root_.GlobalTheory.Mass.idxN N M ^ 2 = 1 :=
        Nat.eq_one_of_mul_eq_one_left hdisc.symm
      have h1' : _root_.GlobalTheory.Mass.idxN N M = 1 := by
        simpa using h1
      exact le_antisymm (_root_.GlobalTheory.Mass.DiscOrder.idxN_eq_one.1 h1') hMN
    · unfold _root_.GlobalTheory.Mass.lamMax
      rw [hbad]
      exact finprod_mem_empty
  · intro M n hO
    exact ⟨_root_.ReciprocityTheory.ChartRestriction.L3.isLattice_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.isUnimodular_of_ortho hO, _root_.ReciprocityTheory.ChartRestriction.L3.finrank_of_ortho hO⟩

end GlobalTheory.Mass.MaxExists
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_maximal_integralHermitianLattice_orthonormal_maximal : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → (∀ M : Submodule (𝓞 K) V, IsIntLat h M → ∃ M', IsMaxLat h M' ∧ M ≤ M') ∧ (∀ M : Submodule (𝓞 K) V, Submodule.IsFullLattice K M → IsUnimodular h M → IsMaxLat h M ∧ badP h M = ∅ ∧ lamMax h M = 1) ∧ (∀ (M : Submodule (𝓞 K) V) (n : ℕ), IsOrthoLattice h M n → Submodule.IsLattice K M ∧ IsUnimodular h M ∧ Module.finrank K V = n) := by
  first
  | exact @GlobalTheory.Mass.MaxExists.main
  | intro K V _ _ _ _ _ _ _ _ h hK hS hN
    have result := GlobalTheory.Mass.MaxExists.main K V h hK hS hN
    exact ⟨result.1, fun M hL hU => result.2.1 M hL.toIsLattice hU, result.2.2⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassPairingClassBounds
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem tsum_subtype_and_eq_ite {α : Type*} (S : Set α) (p q : α → Prop) (f : α → ℝ≥0∞)
    (h : ∀ t ∈ S, p t ↔ q t) :
    (∑' t : {t // t ∈ S ∧ p t}, f t.1) = ∑' t : S, (if q t.1 then f t.1 else 0) := by

  have hL : (∑' t : {t // t ∈ S ∧ p t}, f t.1) = ∑' t, ({t | t ∈ S ∧ p t} : Set α).indicator f t :=
    tsum_subtype {t | t ∈ S ∧ p t} f
  have hR : (∑' t : S, (if q t.1 then f t.1 else 0)) =
      ∑' t, S.indicator (fun t => if q t then f t else 0) t :=
    tsum_subtype S (fun t => if q t then f t else 0)
  rw [hL, hR]
  refine tsum_congr fun t => ?_
  by_cases hS : t ∈ S
  · have hpq := h t hS
    rw [Set.indicator_of_mem hS]
    by_cases hq : q t
    · rw [if_pos hq, Set.indicator_of_mem (show t ∈ {t | t ∈ S ∧ p t} from ⟨hS, hpq.2 hq⟩)]
    · rw [if_neg hq]
      exact Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ {t | t ∈ S ∧ p t}) =>
        absurd (hpq.1 hm.2) hq)
  · rw [Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ {t | t ∈ S ∧ p t}) =>
      absurd hm.1 hS), Set.indicator_apply_eq_zero.mpr (fun (hm : t ∈ S) => absurd hm hS)]

theorem mass_pairingClass_bounds : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), (∃ t0 : Term V M r, LocNG.IsTermOver P d0 t0) → ∀ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat t.f t.f' ∈ c1 → ∀ g : ℝ≥0∞, g = (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) → 0 < g ∧ g ≠ ⊤ ∧ (P.PrimeTo → LocNG.nn R d0 = g) ∧ LocNG.nn R d0 ≤ ENNReal.ofReal (8 * P.Hp ^ (9 * (r + 1) ^ 2 + 2 * (2 * r + 2))) * g := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hdim hrel R d0 hd0 d t hdt Y0 c1 hc1 ht g hg
  obtain ⟨t0, ht0⟩ := hd0

  let Cl : Term V M r → Prop := fun t' => ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, A i j ∈ M.L.O ∧ A' i j ∈ M.L.O ∧ ∃ c ∈ M.L.O, A' i j - A i j = algebraMap F E (LocNG.theta M) * c) ∧ (∀ i j, j < i → A i j = 0 ∧ A' i j = 0) ∧ (∀ i, A i i = 1 ∧ A' i i = 1) ∧ (∀ j, t'.f j = ∑ i, A i j • s (t.f i)) ∧ ∀ j, t'.f' j = ∑ i, A' i j • s (t.f' i)

  have hCl : ∀ (d' : LocNG.Datum P) (t' : Term V M r), LocNG.IsTermOver P d' t' →
      (H.Zhat t'.f t'.f' ∈ c1 ↔ Cl t') := fun d' t' h' =>
    GlobalTheory.T.term_over_relation_uniqueness M hM H r k P hdim hrel d d' t t' hdt h' Y0 c1 hc1 ht

  have hg' : g = ∑' d' : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d'.1) *
      ∑' t' : {t' // t' ∈ R.RT d'.1 ∧ ¬ LocNG.BBne (H := H) t' ∧ Cl t'},
        ENNReal.ofReal (LocNG.mu P t'.1) := by
    rw [hg]
    refine tsum_congr fun d' => ?_
    congr 1
    have e := tsum_subtype_and_eq_ite (R.RT d'.1) (fun t' => ¬ LocNG.BBne (H := H) t' ∧ Cl t')
      (fun t' => ¬ LocNG.BBne (H := H) t' ∧ H.Zhat t'.f t'.f' ∈ c1)
      (fun t' => ENNReal.ofReal (LocNG.mu P t'))
      (fun t' ht' => and_congr_right fun _ => (hCl d'.1 t' ((R.hRT d'.1).1 ht')).symm)
    convert e.symm
  obtain ⟨hne, hle, hprime, hpos⟩ :=
    GlobalTheory.T.hermitian_total_mass_le_generic_mass M hM H r k P hk hdim hrel R d0 d t hdt Cl (fun _ => Iff.rfl) g hg'
  exact ⟨pos_iff_ne_zero.mpr (hpos ⟨t0, ht0⟩), hne, hprime, hle⟩

end GlobalTheory
end
