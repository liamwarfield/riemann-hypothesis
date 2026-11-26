module

public import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib
public import Development.EtaleCohomology.TateTwists.ExistsEtaleKummerChernClassCochainOfDegreeValues

@[expose] public section

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCupCompatibleWithCoefficientMapsOfSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleCupCompatAlexanderWhitneyCocycleSpec : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k), (∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m), ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1) ∧ ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

theorem etale_cochain_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  unfold ev
  rw [Cochain.comp_v _ _ (add_zero n) (-(p : ℤ)) s s h (add_zero s), Cochain.ofHom_v]
  rfl

theorem etale_cocycle_comp_hom_evaluation_eq_map {R : Type} [CommRing R] {E : Spc} {I J : Cx R} {n : ℤ} (m : I ⟶ J)
    (α : Cocycle ((chains R).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx E p U) :
    ev (zcomp α (Cocycle.ofHom m) (add_zero n)).1 p s h U x =
      Sec.map (m.f s) (ev α.1 p s h U x) :=
  etale_cochain_comp_hom_evaluation_eq_map m α.1 p s h U x

theorem etale_cup_compatible_with_coefficient_maps_of_spec (hspec : EtaleCupCompatAlexanderWhitneyCocycleSpec) : EtaleCupProductNaturalInCoefficients := by
  intro R _ I J K I' J' K' μ ν f g u hc E n m k hk a b
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, hγ⟩ := (hspec R μ hk).1 α β
  rw [(hspec R μ hk).2 α β γ hγ, cpost_mk, cpost_mk, cpost_mk]
  symm
  apply (hspec R ν hk).2
  intro N w h U x
  rw [etale_cocycle_comp_hom_evaluation_eq_map, hγ N w h U x]
  simp only [Sec.map]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, Units.smul_def, map_zsmul, etale_cocycle_comp_hom_evaluation_eq_map, etale_cocycle_comp_hom_evaluation_eq_map]
  congr 1
  exact hc U _ _ w _ _ _

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsForPairing
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleAlexanderWhitneyCupCochainExistsForPairing : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def EtaleAlexanderWhitneyCupUniqueBiadditive : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ') ∧
    (∀ (α α' : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) (β β' : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) ∧
    (∀ (β : Cochain ((chains R).obj E) J m), μ.IsAW hk 0 β 0) ∧
    (∀ (α : Cochain ((chains R).obj E) I n), μ.IsAW hk α 0 0)

def EtaleAlexanderWhitneyCupLeibnizRule : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ → δ k k₁ γ = γ₁ + n.negOnePow • γ₂

theorem ev_add' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  unfold ev
  rw [Cochain.add_v, Preadditive.comp_add]
  rfl

theorem ev_zero' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  unfold ev
  rw [Cochain.zero_v, Limits.comp_zero]
  rfl

def EtaleAlexanderWhitneyCupCochainUnique : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ'

theorem awalg_of (hu : EtaleAlexanderWhitneyCupCochainUnique) : EtaleAlexanderWhitneyCupUniqueBiadditive := by
  intro R _ I J K μ E n m k hk
  refine ⟨hu R μ hk, ?_, ?_, ?_, ?_⟩
  · intro α α' β γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add (f := _), LinearMap.add_apply, smul_add]
  · intro α β β' γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add (f := _), smul_add]
  · intro β N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, LinearMap.zero_apply, smul_zero]
  · intro α N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, smul_zero]

theorem cup_spec_part1 (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
    (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 := by
  obtain ⟨γ, hγ⟩ := h1 R μ hk α.1 β.1
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m = k + 1 by omega) (δ n (n + 1) α.1) β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show n + (m + 1) = k + 1 by omega) α.1 (δ m (m + 1) β.1)
  have hd := h3 R μ hk rfl rfl _ _ α.1 β.1 γ γ₁ γ₂ hγ hγ₁ hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₁
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e1, e2, smul_zero, add_zero] at hd
  exact ⟨Cocycle.mk γ (k + 1) rfl hd, hγ⟩

def EtaleAlexanderWhitneyCupDescendsToCohomology : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
        CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

section Desc
variable (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
  {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)

noncomputable def chZ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    Cocycle ((chains R).obj E) K k :=
  Classical.choose (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_spec (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    μ.IsAW hk α.1 β.1 (chZ h1 h2 h3 μ E hk α β).1 :=
  Classical.choose_spec (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_eq (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) : chZ h1 h2 h3 μ E hk α β = γ :=
  Cocycle.ext ((h2 R μ hk).1 _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) h)

theorem chZ_add_left (α α' : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk (α + α') β = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α' β :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α' β))

theorem chZ_add_right (α : Cocycle ((chains R).obj E) I n) (β β' : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk α (β + β') = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α β' :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α β'))

theorem chZ_cob_left (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hα : α ∈ coboundaries _ _ n) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', η, hη⟩ := hα
  obtain ⟨γ, hγ⟩ := h1 R μ (show m' + m = m' + m from rfl) η β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show m' + (m + 1) = k by omega) η (δ m (m + 1) β.1)
  have hd := h3 R μ rfl hm' rfl (show n + m = k from hk) (show m' + (m + 1) = k by omega) η β.1 γ
    (chZ h1 h2 h3 μ E hk α β).1 γ₂ hγ (by rw [hη]; exact chZ_spec h1 h2 h3 μ E hk α β) hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e2, smul_zero, add_zero] at hd
  exact ⟨m' + m, by omega, γ, hd⟩

theorem chZ_cob_right (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hβ : β ∈ coboundaries _ _ m) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', θ, hθ⟩ := hβ
  obtain ⟨γ, hγ⟩ := h1 R μ (show n + m' = n + m' from rfl) α.1 θ
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m' = k by omega) (δ n (n + 1) α.1) θ
  have hd := h3 R μ rfl rfl hm' (show (n + 1) + m' = k by omega) (show n + m = k from hk) α.1 θ γ
    γ₁ (chZ h1 h2 h3 μ E hk α β).1 hγ hγ₁ (by rw [hθ]; exact chZ_spec h1 h2 h3 μ E hk α β)
  rw [Cocycle.δ_eq_zero] at hγ₁
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  rw [e1, zero_add] at hd
  refine ⟨n + m', by omega, n.negOnePow • γ, ?_⟩
  rw [δ_units_smul, hd, smul_smul, Int.units_mul_self, one_smul]

end Desc

theorem desc_of (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule) :
    EtaleAlexanderWhitneyCupDescendsToCohomology := by
  intro R _ I J K μ E n m k hk
  let G : Cocycle ((chains R).obj E) I n → (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    fun α => QuotientAddGroup.lift _
      (AddMonoidHom.mk' (fun β => CohomologyClass.mk (chZ h1 h2 h3 μ E hk α β))
        (fun β β' => by rw [chZ_add_right, CohomologyClass.mk_add]))
      (fun β hβ => by
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
        exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_right h1 h2 h3 μ E hk α β hβ))
  let F : Cocycle ((chains R).obj E) I n →+ (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    AddMonoidHom.mk' G (fun α α' => by
      refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
      show CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
      rw [chZ_add_left, CohomologyClass.mk_add])
  refine ⟨QuotientAddGroup.lift _ F (fun α hα => ?_), ?_⟩
  · rw [AddMonoidHom.mem_ker]
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
    show CohomologyClass.mk _ = 0
    exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_left h1 h2 h3 μ E hk α β hα)
  · intro α β γ hγ
    show CohomologyClass.mk _ = _
    rw [chZ_eq h1 h2 h3 μ E hk α β γ hγ]

theorem etale_cup_compat_spec_of_alexander_whitney_exists_unique_leibniz (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (hu : EtaleAlexanderWhitneyCupCochainUnique)
    (h3 : EtaleAlexanderWhitneyCupLeibnizRule) : EtaleCupCompatAlexanderWhitneyCocycleSpec := by
  have h2 := awalg_of hu
  have h4 := desc_of h1 h2 h3
  intro R _ I J K μ E n m k hk
  refine ⟨fun α β => cup_spec_part1 h1 h2 h3 R μ hk α β, ?_⟩
  intro α β γ hγ
  exact pick_spec (h4 R μ E hk) α β γ hγ
end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizOfSucc
section -- merged from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizEvalDegreeZero
section -- merged from Development.EtaleCohomology.TateTwists.EtaleCochainDifferentialEvaluationDegreeZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awleib_ev_smul {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (u : ℤˣ)
    (α : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (u • α) p s h U x = u • ev α p s h U x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [one_smul, one_smul]
  · rw [Units.neg_smul, Units.neg_smul, one_smul, one_smul]
    unfold ev
    rw [Cochain.neg_v, Preadditive.comp_neg]
    rfl

def EtaleSimplicialCochainEqOfEvaluationsAgree : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {K : Cx R} {k : ℤ} (γ γ' : Cochain ((chains R).obj E) K k),
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U), ev γ N w h U x = ev γ' N w h U x) →
    γ = γ'

def EtaleAlexanderWhitneyLeibnizZeroSimplexDegree : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ →
    ∀ (w : ℤ) (h : -((0 : ℕ) : ℤ) + k₁ = w) (U : Scheme.{0}) (x : Sx E 0 U),
      ev (δ k k₁ γ) 0 w h U x = ev γ₁ 0 w h U x + n.negOnePow • ev γ₂ 0 w h U x

def EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ →
    ∀ (P : ℕ) (w : ℤ) (h : -((P + 1 : ℕ) : ℤ) + k₁ = w) (U : Scheme.{0}) (x : Sx E (P + 1) U),
      ev (δ k k₁ γ) (P + 1) w h U x = ev γ₁ (P + 1) w h U x + n.negOnePow • ev γ₂ (P + 1) w h U x

theorem etale_zero_simplex_subface_zero_zero_eq_self {E : Spc} {U : Scheme.{0}} (x : Sx E 0 U) (h : 0 + 0 ≤ 0) : x.sub 0 0 h = x := by
  unfold Sx.sub
  have e : SimplexCategory.subinterval 0 0 h = 𝟙 _ := by
    ext i
    exact congrArg Fin.val (Subsingleton.elim (α := Fin 1) _ _)
  rw [e, op_id, E.map_id]
  rfl

theorem etale_alexander_whitney_cup_evaluation_degree_zero {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    {α : Cochain ((chains R).obj E) I n} {β : Cochain ((chains R).obj E) J m} {γ : Cochain ((chains R).obj E) K k}
    (ha : μ.IsAW hk α β γ) (s t w : ℤ) (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t)
    (hw : -((0 : ℕ) : ℤ) + k = w) (h : s + t = w) (U : Scheme.{0}) (x : Sx E 0 U) :
    ev γ 0 w hw U x = μ.mul U s t w h (ev α 0 s hs U x) (ev β 0 t ht U x) := by
  subst hs ht hw
  rw [ha 0 _ _ U x, Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
  rw [etale_zero_simplex_subface_zero_zero_eq_self]

theorem awleib_leib' {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0})
    (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s') (ht : t + 1 = t') (hw : w + 1 = w')
    (h1 : s' + t = w') (h2 : s + t' = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' h1 (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' h2 a (Sec.map (J.d t t') b) := by
  subst hs ht hw
  exact μ.leibniz U s t w h a b

def EtaleCochainDifferentialEvaluationDegreeZero : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n)
    (U : Scheme.{0}) (x : Sx E 0 U) (w w' : ℤ) (h : -((0 : ℕ) : ℤ) + n = w) (h' : -((0 : ℕ) : ℤ) + m = w'),
    ev (δ n m α) 0 w' h' U x = Sec.map (I.d w w') (ev α 0 w h U x)

theorem awleib_zero_of (hd : EtaleCochainDifferentialEvaluationDegreeZero) : EtaleAlexanderWhitneyLeibnizZeroSimplexDegree := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 w h U x
  rw [hd R (by omega) γ U x (-((0 : ℕ) : ℤ) + k) w rfl h,
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk ha (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + m) _ rfl rfl rfl (by omega),
    awleib_leib' μ U _ _ _ (-((0 : ℕ) : ℤ) + n₁) (-((0 : ℕ) : ℤ) + m₁) w _ (by omega) (by omega) (by omega)
      (by omega) (by omega),
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk₁ h1 (-((0 : ℕ) : ℤ) + n₁) (-((0 : ℕ) : ℤ) + m) w rfl rfl h (by omega),
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk₂ h2 (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + m₁) w rfl rfl h (by omega),
    hd R hn α U x _ _ rfl rfl, hd R hm β U x _ _ rfl rfl]
  simp

theorem etale_alexander_whitney_leibniz_of_ext_degree_zero_succ (h0 : EtaleSimplicialCochainEqOfEvaluationsAgree) (hd : EtaleCochainDifferentialEvaluationDegreeZero)
    (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) : EtaleAlexanderWhitneyCupLeibnizRule := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2
  apply h0 R
  intro N w h U x
  rw [ev_add', awleib_ev_smul]
  cases N with
  | zero => exact awleib_zero_of hd R μ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 w h U x
  | succ P => exact hs R μ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 P w h U x

end LateralTheory.EtaleFoundations
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_cup_alexanderWhitney_leibniz_eval_degree_zero : EtaleCochainDifferentialEvaluationDegreeZero := by
  intro R _ E I n m hm α U x w w' h h'
  subst h h'
  have hz : IsZero (((chains R).obj E).X (-((0 : ℕ) : ℤ) + 1)) :=
    HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => by
      have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
      omega)
  have hd0 : ((chains R).obj E).d (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) = 0 := hz.eq_of_tgt _ _
  unfold ev
  rw [δ_v n m hm α (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + m) rfl (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + 1)
    (by omega) rfl, hd0, zero_comp, smul_zero, add_zero, ← Category.assoc]
  rfl

theorem etale_cup_alexanderWhitney_leibniz_of_ext_and_succ (h0 : EtaleSimplicialCochainEqOfEvaluationsAgree) (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) :
    EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_alexander_whitney_leibniz_of_ext_degree_zero_succ h0 etale_cup_alexanderWhitney_leibniz_eval_degree_zero hs

end LateralTheory.EtaleFoundations
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awleib_ext_pf : EtaleSimplicialCochainEqOfEvaluationsAgree := by
  intro R _ E K k γ γ' H
  apply Cochain.ext
  intro p q hpq
  by_cases hp : ∃ N : ℕ, -(N : ℤ) = p
  · obtain ⟨N, rfl⟩ := hp
    rw [← cancel_epi (chainsXIso R E N).inv]
    apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _ (K.X q).property
    ext U : 2
    apply ModuleCat.free_hom_ext
    intro x
    exact H N q hpq U.unop x.down
  · have hz : IsZero (((chains R).obj E).X p) :=
      HomologicalComplex.isZero_extend_X _ _ _ (fun i hi => hp ⟨i, by
        have e : ComplexShape.embeddingDownNat.f i = -(i : ℤ) := rfl
        omega⟩)
    exact hz.eq_of_src _ _

theorem etale_cup_alexanderWhitney_leibniz_of_succ (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) : EtaleAlexanderWhitneyCupLeibnizRule :=
  etale_cup_alexanderWhitney_leibniz_of_ext_and_succ awleib_ext_pf hs

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyLeibnizSuccHolds
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem etale_cup_alexanderWhitney_leibniz_succ_holds : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 P w h U x
  subst hn hm
  obtain rfl : k₁ = k + 1 := by omega
  have e := LateralTheory.EtaleFoundations.etaleAlexanderWhitneyCup_leibniz_of_pairing R μ hk α β γ γ₁ γ₂ ha h1 h2
  rw [e, ev_add', awleib_ev_smul]

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsHolds
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awex_sub_res {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (x.res g).sub j l h = (x.sub j l h).res g := by
  unfold Sx.sub Sx.res
  exact ((E.map (SimplexCategory.subinterval j l h).op).naturality_apply g.op x)

theorem awex_freeGen_res {R : Type} [CommRing R] (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    (((free R).obj P).obj.map g.op).hom (freeGen R P U x) = freeGen R P V (P.map g.op x) := by
  unfold freeGen
  have e := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)) (ModuleCat.freeMk (ULift.up x))
  refine e.symm.trans ?_
  exact congrArg (fun y => ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).app (op V)).hom y)
    (ModuleCat.free_map_apply (R := ULift.{1} R) (uliftFunctor.{1}.map (P.map g.op)) (ULift.up x))

theorem awex_ev_res {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (ev α p s h U x) = ev α p s h V (x.res g) := by
  unfold ev Sec.res
  have e := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((((chainsXIso R E p).inv ≫ α.v _ _ h).hom).naturality g.op)) (freeGen R _ U x)
  refine e.symm.trans ?_
  exact congrArg (fun y => (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.app (op V)).hom y)
    (awex_freeGen_res (R := R) _ g x)

theorem awex_lift_single {S : Type*} [Semiring S] {X M : Type*} [AddCommMonoid M] [Module S M]
    (f : X → M) (x : X) : Finsupp.lift M S X f (Finsupp.single x 1) = f x := by
  simp

noncomputable def awexNat {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : (freeP R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ (I.X s).obj where
  app U := ModuleCat.ofHom (Finsupp.lift _ (ULift.{1} R) _
        (fun y : ULift.{1} (Sx E p (unop U)) => a p s h (unop U) y.down))
  naturality := by
        intro U V g
        refine ModuleCat.hom_ext (Finsupp.lhom_ext' fun y => LinearMap.ext_ring ?_)
        have e := ModuleCat.free_map_apply (R := ULift.{1} R)
          (uliftFunctor.{1}.map ((E.obj (op (SimplexCategory.mk p))).map g)) y
        change (Finsupp.lift _ (ULift.{1} R) _ _) (((freeP R).obj _).map g |>.hom (Finsupp.single y 1)) =
          ((I.X s).obj.map g).hom ((Finsupp.lift _ (ULift.{1} R) _ _) (Finsupp.single y 1))
        erw [e]
        refine (awex_lift_single (S := ULift.{1} R) _ _).trans ?_
        refine Eq.trans ?_ (congrArg ((I.X s).obj.map g).hom (awex_lift_single (S := ULift.{1} R) _ _).symm)
        exact (ha p s h (unop V) (unop U) g.unop y.down).symm

noncomputable def awexPhi {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) : (free R).obj (E.obj (op (SimplexCategory.mk p))) ⟶ I.X s :=
  ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ (I.X s)).symm (awexNat a ha p s h)

theorem awexPhi_freeGen {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ((awexPhi a ha p s h).hom.app (op U)).hom (freeGen R _ U x) = a p s h U x := by
  have e := toSheafify_sheafifyLift Scheme.etaleTopology (awexNat a ha p s h) (I.X s).property
  have e2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (congrArg (fun φ => φ.app (op U)) e))
    (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up.{1} x))
  refine e2.trans ?_
  exact awex_lift_single (S := ULift.{1} R) (fun y : ULift.{1} (Sx E p U) => a p s h U y.down) (ULift.up x)

def EtaleSimplicialCochainFromNaturalEvaluationsExists : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

theorem etale_alexander_whitney_cup_exists_of_cochain_from_evaluations (hmk : EtaleSimplicialCochainFromNaturalEvaluationsExists) : EtaleAlexanderWhitneyCupCochainExistsForPairing := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := hmk R (E := E) (I := K) (n := k)
    (fun N w h U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • μ.mul U (-((p : ℕ) : ℤ) + n)
      (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega))))
    (by
      intro N w h V U g x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Sec.res, map_sum, Units.smul_def, map_zsmul]
      refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [awex_sub_res, awex_sub_res, ← awex_ev_res, ← awex_ev_res]
      exact μ.nat g _ _ _ _ _ _)
  exact ⟨γ, fun N w h U x => hγ N w h U x⟩

noncomputable def awexCochain {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) :
    Cochain ((chains R).obj E) I n :=
  Cochain.mk fun x y hxy => if hx : x ≤ 0 then
    (((chains R).obj E).XIsoOfEq (show x = -(((-x).toNat : ℕ) : ℤ) by omega)).hom ≫
      (chainsXIso R E (-x).toNat).hom ≫ awexPhi a ha (-x).toNat y (by omega)
  else 0

theorem awex_key {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (q p : ℕ) (e : q = p) (he : -(p : ℤ) = -(q : ℤ)) (s : ℤ) (h : -(p : ℤ) + n = s) (hq : -(q : ℤ) + n = s) :
    (chainsXIso R E p).inv ≫ (((chains R).obj E).XIsoOfEq he).hom ≫ (chainsXIso R E q).hom ≫ awexPhi a ha q s hq =
      awexPhi a ha p s h := by
  subst e
  simp

theorem awex_ev {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U)
    (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (awexCochain a ha) p s h U x = a p s h U x := by
  unfold ev
  rw [awexCochain, Cochain.mk_v, dite_eq_left (by omega), awex_key a ha _ p (by omega)]
  exact awexPhi_freeGen a ha p s h U x

theorem etale_simplicial_cochain_from_natural_evaluations_exists_holds : EtaleSimplicialCochainFromNaturalEvaluationsExists := by
  intro R _ E I n a ha
  exact ⟨awexCochain a ha, awex_ev a ha⟩

theorem etale_alexander_whitney_cup_cochain_exists_holds : EtaleAlexanderWhitneyCupCochainExistsForPairing :=
  etale_alexander_whitney_cup_exists_of_cochain_from_evaluations etale_simplicial_cochain_from_natural_evaluations_exists_holds

end LateralTheory.EtaleFoundations
end

section -- merged from Development.EtaleCohomology.TateTwists.EtaleCupAlexanderWhitneyUniquenessHolds
section -- merged from Development.EtaleCohomology.TateTwists.FreeExt
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.AwExPf

variable {R : Type} [CommRing R]

theorem free_ext (P : PSh) (F : Shv R) (φ ψ : (free R).obj P ⟶ F)
    (h : ∀ U x, Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) : φ = ψ := by
  let φ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := φ
  let ψ' : (presheafToSheaf Scheme.etaleTopology _).obj ((freeP R).obj P) ⟶ F := ψ
  change φ' = ψ'
  apply ((sheafificationAdjunction Scheme.etaleTopology _).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine NatTrans.ext (funext fun U => ModuleCat.free_hom_ext fun x => ?_)
  exact h U.unop x.down

theorem ev_ext {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (h : ∀ p s h U x, ev α p s h U x = ev β p s h U x) : α = β := by
  refine Cochain.ext _ _ (fun i j hij => ?_)
  by_cases hi : 0 ≤ -i
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
    rw [← cancel_epi (chainsXIso R E p).inv]
    exact free_ext _ _ _ _ fun U x => h p j hij U x
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_extend_X
    intro i' hi'
    change -(i' : ℤ) = i at hi'
    omega

end LateralTheory.EtaleFoundations.AwExPf
end

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_uniqueness_holds : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupCochainUnique := by
  intro R _ I J K μ E n m k hk α β γ γ' h h'
  exact LateralTheory.EtaleFoundations.AwExPf.ev_ext _ _ fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm
end

namespace LateralTheory.Fin.EtaleCupProductNaturalInCoefficients
theorem etale_alexander_whitney_cup_exists_of_components : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupCochainExistsForPairing := by
  apply LateralTheory.EtaleFoundations.etale_alexander_whitney_cup_cochain_exists_holds
theorem etale_alexander_whitney_cup_unique_of_components : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupCochainUnique := by
  apply LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_uniqueness_holds
theorem etale_alexander_whitney_cup_leibniz_rule_succ_of_components : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree := by
  apply LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_leibniz_succ_holds
theorem etale_alexander_whitney_cup_leibniz_rule_of_components : LateralTheory.EtaleFoundations.EtaleAlexanderWhitneyCupLeibnizRule := by
  apply LateralTheory.EtaleFoundations.etale_cup_alexanderWhitney_leibniz_of_succ <;> first | exact etale_alexander_whitney_cup_leibniz_rule_succ_of_components
theorem etale_cup_product_compatibility_specification_of_components : LateralTheory.EtaleFoundations.EtaleCupCompatAlexanderWhitneyCocycleSpec := by
  apply LateralTheory.EtaleFoundations.etale_cup_compat_spec_of_alexander_whitney_exists_unique_leibniz <;> first | exact etale_alexander_whitney_cup_exists_of_components | exact etale_alexander_whitney_cup_unique_of_components | exact etale_alexander_whitney_cup_leibniz_rule_of_components
theorem etale_cup_product_compatible_with_cochains_of_components : LateralTheory.EtaleFoundations.EtaleCupProductNaturalInCoefficients := by
  apply LateralTheory.EtaleFoundations.etale_cup_compatible_with_coefficient_maps_of_spec <;> first | exact etale_cup_product_compatibility_specification_of_components
theorem intersectionNumber_baseChange : LateralTheory.EtaleFoundations.EtaleCupProductNaturalInCoefficients := etale_cup_product_compatible_with_cochains_of_components
end LateralTheory.Fin.EtaleCupProductNaturalInCoefficients
