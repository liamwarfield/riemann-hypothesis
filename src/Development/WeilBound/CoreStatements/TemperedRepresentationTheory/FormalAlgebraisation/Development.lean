module

public import PositivityTheory.PublishedTheorems.UnitKilling.UnitAnnihilation.UnitAnnihilators.ExistsUnitKillsOfIdempotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousIdealFiltrationSaturated
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalAlgebraisationSchemes
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GrothendieckExistenceClosed

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HomogeneousLiftAdicFiltration
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.Tower

variable {R : Type} [CommRing R] {N : ℕ}

theorem sub_tail_mem (I : Ideal R) (e : ℕ) (G : ℕ → MvPolynomial (Fin (N + 1)) R)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) (m k : ℕ) :
    G m - G (m + k) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : G (m + k) - G (m + k + 1) ∈ (I ^ (e + m + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
      Ideal.map_mono (Ideal.pow_le_pow_right (by omega)) (hd (m + k))
    have h3 : G m - G (m + (k + 1)) = (G m - G (m + k)) + (G (m + k) - G (m + k + 1)) := by
      rw [show m + (k + 1) = m + k + 1 from rfl]
      ring
    rw [h3]
    exact add_mem ih h2

theorem exists_limit_form (I : Ideal R) [IsPrecomplete I R] (n e : ℕ)
    (G : ℕ → MvPolynomial (Fin (N + 1)) R) (hom : ∀ i, (G i).IsHomogeneous n)
    (hd : ∀ i, G i - G (i + 1) ∈
      (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) :
    ∃ g : MvPolynomial (Fin (N + 1)) R, g.IsHomogeneous n ∧
      ∀ i, G i - g ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have htop : ∀ k, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hcoef : ∀ d i k, AddMonoidAlgebra.coeff (G i) d - AddMonoidAlgebra.coeff (G (i + k)) d ∈ I ^ (e + i + 1) := by
    intro d i k
    have h := (mem_map_C_iff.1 (sub_tail_mem I e G hd i k)) d
    rwa [coeff_sub] at h
  have hL : ∀ d, ∃ Ld : R, ∀ i, AddMonoidAlgebra.coeff (G i) d - Ld ∈ I ^ (e + i + 1) := by
    intro d
    obtain ⟨Ld, hLd⟩ := IsPrecomplete.prec' (I := I) (fun i => AddMonoidAlgebra.coeff (G i) d) (by
      intro m n hmn
      rw [SModEq.sub_mem, htop]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      exact Ideal.pow_le_pow_right (by omega) (hcoef d m k))
    refine ⟨Ld, fun i => ?_⟩
    have h1 := hcoef d i (e + 1)
    have h2 := hLd (i + (e + 1))
    rw [SModEq.sub_mem, htop] at h2
    have h3 : AddMonoidAlgebra.coeff (G i) d - Ld =
        (AddMonoidAlgebra.coeff (G i) d - AddMonoidAlgebra.coeff (G (i + (e + 1))) d) + (AddMonoidAlgebra.coeff (G (i + (e + 1))) d - Ld) := by ring
    rw [h3]
    exact add_mem h1 (Ideal.pow_le_pow_right (by omega) h2)
  choose Lf hLf using hL
  refine ⟨∑ d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n, monomial d (Lf d), ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ (fun d hd => isHomogeneous_monomial _ ?_)
    rw [Finset.mem_finsuppAntidiag] at hd
    rw [Finsupp.degree_eq_sum]
    exact hd.1
  · intro i
    rw [mem_map_C_iff]
    intro d
    rw [coeff_sub, coeff_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq']
    by_cases hdS : d ∈ (Finset.univ : Finset (Fin (N + 1))).finsuppAntidiag n
    · rw [if_pos hdS]
      exact hLf d i
    · rw [if_neg hdS, sub_zero]
      have h0 : AddMonoidAlgebra.coeff (G i) d = 0 := by
        by_contra hne
        apply hdS
        have hw := hom i hne
        rw [Finset.mem_finsuppAntidiag]
        refine ⟨?_, Finset.subset_univ _⟩
        rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
        exact hw
      rw [h0]
      exact zero_mem _

theorem exists_form_in_all (I : Ideal R) [IsPrecomplete I R]
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R))
    (hbase : ∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e)
    (hanti : ∀ e, L (e + 1) ≤ L e) (n₀ : ℕ)
    (hlift : ∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R))
    (e n : ℕ) (hn : n₀ ≤ n) (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ L e)
    (hgn : g.IsHomogeneous n) :
    ∃ g' : MvPolynomial (Fin (N + 1)) R, g'.IsHomogeneous n ∧ (∀ j, g' ∈ L j) ∧
      g - g' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  classical
  have hL : Antitone L := antitone_nat_of_succ_le hanti
  let lift' : ℕ → MvPolynomial (Fin (N + 1)) R → MvPolynomial (Fin (N + 1)) R := fun j f =>
    if h : ∃ f' ∈ L (j + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (j + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) then h.choose else f
  let s : ℕ → MvPolynomial (Fin (N + 1)) R := fun i =>
    Nat.rec (motive := fun _ => MvPolynomial (Fin (N + 1)) R) g (fun k f => lift' (e + k) f) i
  have hsS : ∀ i, s (i + 1) = lift' (e + i) (s i) := fun i => rfl
  have hstep : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n →
      s (i + 1) ∈ L (e + i + 1) ∧ (s (i + 1)).IsHomogeneous n ∧
        s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    rintro i ⟨h1, h2⟩
    have hex := hlift (e + i) n hn (s i) h1 h2
    rw [hsS]
    simp only [lift']
    rw [dite_eq_left hex]
    exact hex.choose_spec
  have hinv : ∀ i, s i ∈ L (e + i) ∧ (s i).IsHomogeneous n := by
    intro i
    induction i with
    | zero => exact ⟨hg, hgn⟩
    | succ i ih => exact ⟨(hstep i ih).1, (hstep i ih).2.1⟩
  have hd : ∀ i, s i - s (i + 1) ∈ (I ^ (e + i + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) :=
    fun i => (hstep i (hinv i)).2.2
  obtain ⟨g', hg'n, hg'⟩ := exists_limit_form I n e s (fun i => (hinv i).2) hd
  refine ⟨g', hg'n, fun j => ?_, hg' 0⟩
  have h1 : s j ∈ L j := hL (by omega : j ≤ e + j) (hinv j).1
  have h2 : s j - g' ∈ L j := hL (by omega : j ≤ e + j) (hbase (e + j) (hg' j))
  have h3 : g' = s j - (s j - g') := by ring
  rw [h3]
  exact sub_mem h1 h2


attribute [local instance] MvPolynomial.gradedAlgebra in
theorem exists_limit_ideal : ∀ (R : Type) [CommRing R] (I : Ideal R), IsAdicComplete I R → ∀ (N : ℕ)
    (L : ℕ → Ideal (MvPolynomial (Fin (N + 1)) R)),
    (∀ e, HomogIdeal (L e)) →
    (∀ e, (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ≤ L e) →
    (∀ e, L (e + 1) ≤ L e) →
    ∀ (n₀ : ℕ), (∀ e n, n₀ ≤ n → ∀ f ∈ L e, f.IsHomogeneous n →
      ∃ f' ∈ L (e + 1), f'.IsHomogeneous n ∧
        f - f' ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R)) →
    ∃ J : Ideal (MvPolynomial (Fin (N + 1)) R), HomogIdeal J ∧ ∀ e, J ≤ L e ∧
        ∀ f ∈ L e, ∀ k, ∃ m : ℕ, X k ^ m * f ∈
          J ⊔ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
  intro R _ I hI N L hhom hbase hanti n₀ hlift
  have : IsPrecomplete I R := hI.toIsPrecomplete
  classical
  let S : Set (MvPolynomial (Fin (N + 1)) R) := {g | ∃ n, n₀ ≤ n ∧ g.IsHomogeneous n ∧ ∀ j, g ∈ L j}
  refine ⟨Ideal.span S, ?_, fun e => ⟨?_, ?_⟩⟩
  · intro d f hf
    have hH : (Ideal.span S).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) R) :=
      Ideal.homogeneous_span _ _ (fun x hx => by
        obtain ⟨n, _, hn, _⟩ := hx
        exact ⟨n, (mem_homogeneousSubmodule n x).2 hn⟩)
    have h := (Ideal.IsHomogeneous.mem_iff _ hH).1 hf d
    have e1 : (DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) f d :
        MvPolynomial (Fin (N + 1)) R) = homogeneousComponent d f := decomposition.decompose'_apply f d
    rwa [e1] at h
  · rw [Ideal.span_le]
    rintro g ⟨n, _, _, hall⟩
    exact hall e
  · intro f hf k
    refine ⟨n₀, ?_⟩
    rw [← sum_homogeneousComponent f, Finset.mul_sum]
    refine Submodule.sum_mem _ fun d _ => ?_
    have hmem : X k ^ n₀ * homogeneousComponent d f ∈ L e := Ideal.mul_mem_left _ _ (hhom e d f hf)
    have hh : (X k ^ n₀ * homogeneousComponent d f).IsHomogeneous (n₀ + d) :=
      (isHomogeneous_X_pow k n₀).mul (homogeneousComponent_isHomogeneous d f)
    obtain ⟨g', hg'n, hall, hdiff⟩ :=
      exists_form_in_all I L hbase hanti n₀ hlift e (n₀ + d) (Nat.le_add_right _ _) _ hmem hh
    have h3 : X k ^ n₀ * homogeneousComponent d f = g' + (X k ^ n₀ * homogeneousComponent d f - g') := by
      ring
    rw [h3]
    exact add_mem (Ideal.mem_sup_left (Ideal.subset_span ⟨n₀ + d, Nat.le_add_right _ _, hg'n, hall⟩))
      (Ideal.mem_sup_right hdiff)

end GlobalTheory.CompanionTheory.GE.Tower
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismUniqueness
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismUniqueness
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.FormalUniq

theorem eq_of_comp_thickenings_eq :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
    ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  intro R _ _ I hI X Z hX hZ Y b hpb g g' hb
  have hw : g.left ≫ Z.hom = g'.left ≫ Z.hom := by rw [Over.w g, Over.w g']
  obtain ⟨L, hL1, hL2⟩ : ∃ L : X.left ⟶ pullback Z.hom Z.hom,
      L ≫ pullback.fst _ _ = g.left ∧ L ≫ pullback.snd _ _ = g'.left :=
    ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hfac : ∀ e : ℕ, ∃ h, h ≫ pullback.snd (pullback.diagonal Z.hom) L =
      pullback.fst X.hom (thick R I e) := by
    intro e
    have hfe : pullback.fst X.hom (thick R I e) ≫ g.left =
        pullback.fst X.hom (thick R I e) ≫ g'.left := by
      rw [← (hpb e).isoPullback_inv_fst, Category.assoc, Category.assoc, hb e]
    refine ⟨pullback.lift (pullback.fst X.hom (thick R I e) ≫ g.left)
      (pullback.fst X.hom (thick R I e)) ?_, pullback.lift_snd _ _ _⟩
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, hL1]
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id, hL2, hfe]
  haveI : IsIso (pullback.snd (pullback.diagonal Z.hom) L) :=
    GlobalTheory.CompanionTheory.FormalClosed.isIso_of_isClosedImmersion_of_thickenings R I hI X hX _ _ inferInstance hfac
  have hc := pullback.condition (f := pullback.diagonal Z.hom) (g := L)
  have e1 := congrArg (· ≫ pullback.fst Z.hom Z.hom) hc
  have e2 := congrArg (· ≫ pullback.snd Z.hom Z.hom) hc
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    hL1, hL2] at e1 e2
  exact Over.OverMorphism.ext
    ((cancel_epi (pullback.snd (pullback.diagonal Z.hom) L)).mp (e1.symm.trans e2))

end GlobalTheory.CompanionTheory.FormalUniq
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismUniquenessStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_morphism_uniqueness : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
  ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom → IsSeparated Z.hom →
  ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left),
    (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) →
  ∀ g g' : X ⟶ Z, (∀ e, b e ≫ g.left = b e ≫ g'.left) → g = g' := by
  first | exact @GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq | exact GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq | (intros; apply GlobalTheory.CompanionTheory.FormalUniq.eq_of_comp_thickenings_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismExistence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismExistence
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.MorphismAlgebraisation

lemma isPullback_of_sections {C : Type*} [Category C] {A A' B B' : C} {p : A ⟶ B} {q : A' ⟶ B'}
    {rA : A ⟶ A'} {rB : B ⟶ B'} {sA : A' ⟶ A} {sB : B' ⟶ B} (h : IsPullback p rA rB q)
    (hA : sA ≫ rA = 𝟙 _) (hB : sB ≫ rB = 𝟙 _) (hc : sA ≫ p = q ≫ sB) :
    IsPullback q sA sB p :=
  IsPullback.of_bot (by rw [hA, hB]; exact IsPullback.id_vert q) hc.symm h

section Graph

variable {S Se X Z Y : Scheme.{0}} (hX : X ⟶ S) (hZ : Z ⟶ S) (t : Se ⟶ S) {b : Y ⟶ X} {y : Y ⟶ Se}

def retr (h : IsPullback b y hX t) : pullback (pullback.fst hX hZ ≫ hX) t ⟶ Y :=
  h.lift (pullback.fst _ t ≫ pullback.fst hX hZ) (pullback.snd _ t)
    (by simp only [Category.assoc]; exact pullback.condition)

lemma retr_fst (h : IsPullback b y hX t) :
    retr hX hZ t h ≫ b = pullback.fst _ t ≫ pullback.fst hX hZ := h.lift_fst _ _ _

lemma retr_snd (h : IsPullback b y hX t) : retr hX hZ t h ≫ y = pullback.snd _ t :=
  h.lift_snd _ _ _

lemma isPullback_retr (h : IsPullback b y hX t) :
    IsPullback (pullback.fst (pullback.fst hX hZ ≫ hX) t) (retr hX hZ t h)
      (pullback.fst hX hZ) b :=
  IsPullback.of_bot (by rw [retr_snd]; exact IsPullback.of_hasPullback _ _)
    (retr_fst hX hZ t h).symm h

def graph (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    Y ⟶ pullback (pullback.fst hX hZ ≫ hX) t :=
  pullback.lift (pullback.lift b f (by rw [hf, h.w])) y (by rw [pullback.lift_fst_assoc, h.w])

@[reassoc (attr := simp)]
lemma graph_fst_fst (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.fst _ t ≫ pullback.fst hX hZ = b := by
  rw [graph, pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma graph_fst_snd (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.fst _ t ≫ pullback.snd hX hZ = f := by
  rw [graph, pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc (attr := simp)]
lemma graph_snd (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ pullback.snd _ t = y := by
  rw [graph, pullback.lift_snd]

lemma graph_retr (h : IsPullback b y hX t) (f : Y ⟶ Z) (hf : f ≫ hZ = y ≫ t) :
    graph hX hZ t h f hf ≫ retr hX hZ t h = 𝟙 Y := by
  apply h.hom_ext
  · simp [retr_fst]
  · simp [retr_snd]

lemma isClosedImmersion_graph [IsSeparated hZ] (h : IsPullback b y hX t) (f : Y ⟶ Z)
    (hf : f ≫ hZ = y ≫ t) : IsClosedImmersion (graph hX hZ t h f hf) := by
  have : IsSeparated (retr hX hZ t h) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_retr hX hZ t h) inferInstance
  have : IsClosedImmersion (graph hX hZ t h f hf ≫ retr hX hZ t h) := by
    rw [graph_retr]; infer_instance
  exact IsClosedImmersion.of_comp _ (retr hX hZ t h)

lemma isPullback_graph [IsSeparated hZ] {Se' Y' : Scheme.{0}} (t' : Se' ⟶ S) {b' : Y' ⟶ X} {y' : Y' ⟶ Se'}
    (τ : Se ⟶ Se') (hτ : τ ≫ t' = t) (h : IsPullback b y hX t) (h' : IsPullback b' y' hX t')
    (β : Y ⟶ Y') (hβ : β ≫ b' = b) (hy : β ≫ y' = y ≫ τ) (f : Y ⟶ Z) (f' : Y' ⟶ Z)
    (hf : f ≫ hZ = y ≫ t) (hf' : f' ≫ hZ = y' ≫ t') (hff : β ≫ f' = f) :
    IsPullback β (graph hX hZ t h f hf) (graph hX hZ t' h' f' hf')
      (pullback.map (pullback.fst hX hZ ≫ hX) t (pullback.fst hX hZ ≫ hX) t' (𝟙 _) τ (𝟙 _)
        (by simp) (by simp [hτ])) := by
  set m := pullback.map (pullback.fst hX hZ ≫ hX) t (pullback.fst hX hZ ≫ hX) t' (𝟙 _) τ (𝟙 _)
        (by simp) (by simp [hτ]) with hm
  have m_fst : m ≫ pullback.fst _ t' = pullback.fst _ t := by
    rw [hm, pullback.map, pullback.lift_fst, Category.comp_id]
  have m_snd : m ≫ pullback.snd _ t' = pullback.snd _ t ≫ τ := by
    rw [hm, pullback.map, pullback.lift_snd]
  have sq : m ≫ retr hX hZ t' h' = retr hX hZ t h ≫ β := by
    apply h'.hom_ext
    · rw [Category.assoc, Category.assoc, hβ, retr_fst, retr_fst, reassoc_of% m_fst]
    · rw [Category.assoc, Category.assoc, hy, retr_snd, m_snd, reassoc_of% (retr_snd hX hZ t h)]
  have h0 : IsPullback m (retr hX hZ t h) (retr hX hZ t' h') β :=
    IsPullback.of_right (h₁₂ := pullback.fst _ t') (h₂₂ := b') (v₁₃ := pullback.fst hX hZ)
      (by rw [m_fst, hβ]; exact isPullback_retr hX hZ t h) sq (isPullback_retr hX hZ t' h')
  refine isPullback_of_sections h0 (graph_retr hX hZ t h f hf) (graph_retr hX hZ t' h' f' hf') ?_
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, m_fst, graph_fst_fst, graph_fst_fst_assoc, hβ]
    · simp only [Category.assoc, m_fst, graph_fst_snd, graph_fst_snd_assoc, hff]
  · simp only [Category.assoc, m_snd, graph_snd, graph_snd_assoc, hy]

end Graph

theorem exists_hom_of_thickenings : GEClosed → IsoOfThick →
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      IsSeparated Z.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) →
    ∀ f : ∀ e, (Y e).left ⟶ Z.left,
      (∀ e, f e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ f (e + 1) = f e) →
      ∃ g : X ⟶ Z, ∀ e, b e ≫ g.left = f e := by
  intro hGE hIso R _ _ I hI X Z hXp hZs hZf hZq Y β b hb hβ f hf hfβ
  let P : Over (Spec (CommRingCat.of R)) := Over.mk (pullback.fst X.hom Z.hom ≫ X.hom)
  have hPs : IsSeparated P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hPf : LocallyOfFiniteType P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hPq : QuasiCompact P.hom := by dsimp only [P, Over.mk_hom]; infer_instance
  have hth : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hy : ∀ e, β e ≫ (Y (e + 1)).hom = (Y e).hom ≫ thickTrans R I e := fun e => by
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, Category.assoc, thickTrans_comp,
      ← (hb (e + 1)).w, ← (hb e).w, ← Category.assoc, hβ]
  let i : ∀ e, (Y e).left ⟶ (thickObj R I e P).left := fun e =>
    graph X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hi : ∀ e, IsClosedImmersion (i e) := fun e =>
    isClosedImmersion_graph X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hiβ : ∀ e, IsPullback (β e) (i e) (i (e + 1)) (thickMap R I e P) := fun e =>
    isPullback_graph X.hom Z.hom (thick R I e) (thick R I (e + 1)) (thickTrans R I e)
      (thickTrans_comp R I e) (hb e) (hb (e + 1)) (β e) (hβ e) (hy e) (f e) (f (e + 1)) (hf e)
      (hf (e + 1)) (hfβ e)
  have hisnd : ∀ e, i e ≫ pullback.snd P.hom (thick R I e) = (Y e).hom := fun e =>
    graph_snd X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hi0 : IsProper (i 0 ≫ (thickObj R I 0 P).hom) := by
    have h1 : i 0 ≫ (thickObj R I 0 P).hom = (Y 0).hom := hisnd 0
    rw [h1]
    exact MorphismProperty.of_isPullback (P := @IsProper) (hb 0) hXp
  obtain ⟨C', j, b', hj, hjp, hpb, hb'⟩ :=
    hGE R I hI P hPs hPf hPq (fun e => (Y e).left) i β hi hiβ hi0
  let Co : Over (Spec (CommRingCat.of R)) := Over.mk (j ≫ P.hom)
  let p : Co ⟶ X := Over.homMk (j ≫ pullback.fst X.hom Z.hom) (by simp [Co, P])
  have hpl : p.left = j ≫ pullback.fst X.hom Z.hom := rfl
  have hpp : IsProper p.left := by
    have h1 : IsProper (p.left ≫ X.hom) := by
      have h2 : p.left ≫ X.hom = j ≫ P.hom := by simp [hpl, P]
      rw [h2]; exact hjp
    exact IsProper.of_comp _ X.hom
  have hC : ∀ e, IsPullback (b' e) (Y e).hom Co.hom (thick R I e) := fun e => by
    have h1 := (hpb e).paste_vert (IsPullback.of_hasPullback P.hom (thick R I e))
    rw [hisnd e] at h1
    exact h1
  have hbe : ∀ e, b' e ≫ p.left = b e := fun e => by
    have h1 := (hpb e).w
    rw [hpl, reassoc_of% h1]
    exact graph_fst_fst X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
  have hiso : ∀ e, IsIso ((Over.pullback (thick R I e)).map p).left := fun e => by
    have key : (hC e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map p).left =
        (hb e).isoPullback.hom := by
      have m1 : ((Over.pullback (thick R I e)).map p).left ≫ pullback.fst X.hom (thick R I e) =
          pullback.fst Co.hom (thick R I e) ≫ p.left := pullback.lift_fst _ _ _
      have m2 : ((Over.pullback (thick R I e)).map p).left ≫ pullback.snd X.hom (thick R I e) =
          pullback.snd Co.hom (thick R I e) := pullback.lift_snd _ _ _
      apply pullback.hom_ext
      · rw [Category.assoc, m1, IsPullback.isoPullback_hom_fst_assoc, hbe,
          IsPullback.isoPullback_hom_fst]
      · rw [Category.assoc, m2, IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd]
    have h1 : IsIso ((hC e).isoPullback.hom ≫ ((Over.pullback (thick R I e)).map p).left) := by
      rw [key]; infer_instance
    exact IsIso.of_isIso_comp_left (hC e).isoPullback.hom _
  have hp : IsIso p := hIso R I hI X Co p hXp hpp hiso
  have hl : IsIso p.left := inferInstanceAs (IsIso ((Over.forget _).map p))
  have hz : j ≫ pullback.snd X.hom Z.hom ≫ Z.hom = p.left ≫ X.hom := by
    rw [hpl, Category.assoc, pullback.condition]
  refine ⟨Over.homMk (inv p.left ≫ j ≫ pullback.snd X.hom Z.hom) ?_, fun e => ?_⟩
  · simp [hz]
  · have h1 := (hpb e).w
    have h2 : b' e ≫ j ≫ pullback.snd X.hom Z.hom = f e := by
      rw [reassoc_of% h1]
      exact graph_fst_snd X.hom Z.hom (thick R I e) (hb e) (f e) (hf e)
    simp only [Over.homMk_left]
    rw [← hbe e, Category.assoc, IsIso.hom_inv_id_assoc, h2]

end GlobalTheory.CompanionTheory.MorphismAlgebraisation
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalMorphismExistenceStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_morphism_existence : GEClosed → IsoOfThick →
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R →
    ∀ (X Z : Over (Spec (CommRingCat.of R))), IsProper X.hom →
      IsSeparated Z.hom → LocallyOfFiniteType Z.hom → QuasiCompact Z.hom →
    ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
      (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (b : ∀ e, (Y e).left ⟶ X.left),
      (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → (∀ e, β e ≫ b (e + 1) = b e) →
    ∀ f : ∀ e, (Y e).left ⟶ Z.left,
      (∀ e, f e ≫ Z.hom = (Y e).hom ≫ thick R I e) → (∀ e, β e ≫ f (e + 1) = f e) →
      ∃ g : X ⟶ Z, ∀ e, b e ≫ g.left = f e := by
  first | exact @GlobalTheory.CompanionTheory.MorphismAlgebraisation.exists_hom_of_thickenings | exact GlobalTheory.CompanionTheory.MorphismAlgebraisation.exists_hom_of_thickenings | (intros; apply GlobalTheory.CompanionTheory.MorphismAlgebraisation.exists_hom_of_thickenings <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickenings
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickenings
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

namespace GlobalTheory.CompanionTheory.Formal.IsoThick

theorem exists_unit_kills {A B : Type} [CommRing A] [CommRing B] [IsNoetherianRing A] (φ : A →+* B)
    (hφ : φ.Finite) (J : Ideal A) (hsurj : ∀ b, ∃ a, b - φ a ∈ J.map φ)
    (hinj : ∀ a, φ a = 0 → ∀ n : ℕ, a ∈ J ^ n) :
    ∃ s : A, s - 1 ∈ J ∧ (∀ k, φ k = 0 → s * k = 0) ∧ ∀ b, ∃ a, φ s * b = φ a := by
  first | exact @KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills | exact KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills | (intros; apply KrullIntersectionUnits.KrullIntersectionLemmas.GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills <;> assumption)

theorem bijective_of_away {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (ρA : A →+* A') (ρB : B →+* B') (ψ : A' →+* B')
    (hc : ∀ a, ψ (ρA a) = ρB (φ a)) (s : A)
    (hA : @IsLocalization.Away _ _ s A' _ ρA.toAlgebra)
    (hB : @IsLocalization.Away _ _ (φ s) B' _ ρB.toAlgebra)
    (hker : ∀ k, φ k = 0 → s * k = 0) (hcok : ∀ b, ∃ a, φ s * b = φ a) :
    Function.Bijective ψ := by
  letI := ρA.toAlgebra
  letI := ρB.toAlgebra
  have eA : ∀ a, algebraMap A A' a = ρA a := fun _ => rfl
  have eB : ∀ a, algebraMap B B' a = ρB a := fun _ => rfl
  have uA : IsUnit (ρA s) := IsLocalization.Away.algebraMap_isUnit (S := A') s
  have uB : IsUnit (ρB (φ s)) := IsLocalization.Away.algebraMap_isUnit (S := B') (φ s)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (S := A') s x
    rw [eA, eA] at h
    have h1 : ρB (φ a) = 0 := by
      rw [← hc, ← h, map_mul, hx, zero_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (φ s)) B' (φ a)).1 h1
    have h2 : φ (s ^ m * a) = 0 := by rw [map_mul, map_pow]; exact hm
    have h3 := hker _ h2
    have h4 : ρA s * (ρA s ^ m * ρA a) = 0 := by
      have := congrArg ρA h3
      simpa [map_mul, map_pow] using this
    have h5 : ρA a = 0 := by
      have := (uA.mul_right_eq_zero).1 h4
      exact ((uA.pow m).mul_right_eq_zero).1 this
    rw [h5] at h
    exact ((uA.pow n).mul_left_eq_zero).1 h
  · intro y
    obtain ⟨n, b, h⟩ := IsLocalization.Away.surj (S := B') (φ s) y
    rw [eB, eB] at h
    obtain ⟨a, ha⟩ := hcok b
    obtain ⟨x, hx⟩ : ∃ x, x * ρA s ^ (n + 1) = ρA a := by
      refine ⟨ρA a * ↑((uA.pow (n + 1)).unit⁻¹), ?_⟩
      rw [mul_assoc]
      have : (↑((uA.pow (n + 1)).unit⁻¹) : A') * ρA s ^ (n + 1) = 1 :=
        (uA.pow (n + 1)).val_inv_mul
      rw [this, mul_one]
    refine ⟨x, ?_⟩
    have h1 : ψ x * ρB (φ s) ^ (n + 1) = y * ρB (φ s) ^ (n + 1) := by
      have := congrArg ψ hx
      rw [map_mul, map_pow, hc, hc, ← ha, map_mul, ← h] at this
      rw [this]; ring
    exact (uB.pow (n + 1)).mul_right_cancel h1

open TensorProduct in
theorem tmul_one_eq_zero_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (m : M) : m ⊗ₜ[R] (1 : R ⧸ K) = 0 ↔ m ∈ (K • ⊤ : Submodule R M) := by
  have h : m ⊗ₜ[R] (1 : R ⧸ K) = 0 ↔ (TensorProduct.tensorQuotEquivQuotSMul M K).symm
      (Submodule.Quotient.mk m) = 0 := by rw [TensorProduct.tensorQuotEquivQuotSMul_symm_mk]
  rw [h, LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

open TensorProduct in
theorem exists_tmul_one {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (K : Ideal R)
    (y : M ⊗[R] (R ⧸ K)) : ∃ m : M, y = m ⊗ₜ[R] (1 : R ⧸ K) := by
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (TensorProduct.tensorQuotEquivQuotSMul M K y)
  refine ⟨m, ?_⟩
  rw [← TensorProduct.tensorQuotEquivQuotSMul_symm_mk, hm, LinearEquiv.symm_apply_apply]

open TensorProduct in
theorem facts_of_bijective {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (K : Ideal R)
    (h : Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id R (R ⧸ K)))) :
    (∀ a, φ a = 0 → a ∈ K.map (algebraMap R A)) ∧
      ∀ b, ∃ a, b - φ a ∈ K.map (algebraMap R B) := by
  constructor
  · intro a ha
    have h1 : a ⊗ₜ[R] (1 : R ⧸ K) = 0 := by
      apply h.1
      rw [map_zero]
      simp [ha]
    have h2 := (tmul_one_eq_zero_iff K a).1 h1
    rw [Ideal.smul_top_eq_map] at h2
    exact h2
  · intro b
    obtain ⟨y, hy⟩ := h.2 (b ⊗ₜ[R] (1 : R ⧸ K))
    obtain ⟨a, rfl⟩ := exists_tmul_one K y
    refine ⟨a, ?_⟩
    have h1 : (b - φ a) ⊗ₜ[R] (1 : R ⧸ K) = 0 := by
      rw [TensorProduct.sub_tmul, ← hy]
      simp
    have h2 := (tmul_one_eq_zero_iff K _).1 h1
    rw [Ideal.smul_top_eq_map] at h2
    exact h2

open TensorProduct in
theorem bijective_of_isIso_pullback {R A B T : Type} [CommRing R] [CommRing A] [CommRing B]
    [CommRing T] [Algebra R A] [Algebra R B] [Algebra R T] (φ : A →ₐ[R] B)
    (m : pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom (algebraMap R T))))
    (hm1 : m ≫ pullback.fst _ _ = pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom))
    (hm2 : m ≫ pullback.snd _ _ = pullback.snd _ _) (h : IsIso m) :
    Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id R T)) := by
  have e1 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] T)) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[R] T)) ≫
        Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have e2 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) :
        T →+* A ⊗[R] T)) =
      Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : T →ₐ[R] B ⊗[R] T) :
        T →+* B ⊗[R] T)) := by
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp
  have key : m = (pullbackSpecIso R B T).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) ≫
        (pullbackSpecIso R A T).inv := by
    apply pullback.hom_ext
    · rw [hm1, Category.assoc, Category.assoc, pullbackSpecIso_inv_fst, e1, ← Category.assoc,
        pullbackSpecIso_hom_fst]
    · rw [hm2, Category.assoc, Category.assoc, pullbackSpecIso_inv_snd, e2, pullbackSpecIso_hom_snd]
  have h2 : IsIso (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom)) := by
    have : Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id R T)).toRingHom) =
        (pullbackSpecIso R B T).inv ≫ m ≫ (pullbackSpecIso R A T).hom := by
      rw [key]; simp
    rw [this]
    infer_instance
  rw [isIso_SpecMap_iff] at h2
  exact h2

theorem toSpecΓ_comp {R : Type} [CommRing R] {X : Scheme.{0}} (h : X ⟶ Spec (CommRingCat.of R)) :
    X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ h.appTop) = h := by
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality, Iso.hom_inv_id_assoc]

theorem ring_case {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsNoetherianRing A] (φ : A →ₐ[R] B) (hφ : φ.toRingHom.Finite) (I : Ideal R)
    (hf : ∀ e : ℕ, Function.Bijective
      (Algebra.TensorProduct.map φ (AlgHom.id R (R ⧸ I ^ (e + 1))))) :
    ∃ s : A, s - 1 ∈ I.map (algebraMap R A) ∧ (∀ k, φ k = 0 → s * k = 0) ∧
      ∀ b, ∃ a, φ s * b = φ a := by
  refine exists_unit_kills φ.toRingHom hφ (I.map (algebraMap R A)) ?_ ?_
  · intro b
    obtain ⟨a, ha⟩ := (facts_of_bijective φ _ (hf 0)).2 b
    refine ⟨a, ?_⟩
    rw [Ideal.map_map]
    have : φ.toRingHom.comp (algebraMap R A) = algebraMap R B := φ.comp_algebraMap
    rw [this]
    simpa using ha
  · intro a ha n
    have h1 := (facts_of_bijective φ _ (hf n)).1 a ha
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_le_pow_right (Nat.le_succ n) h1

theorem over_pullback_fst {S T : Scheme.{0}} (t : T ⟶ S) {P Q : Over S} (g : P ⟶ Q) :
    ((Over.pullback t).map g).left ≫ pullback.fst Q.hom t = pullback.fst P.hom t ≫ g.left := by
  simp

theorem over_pullback_snd {S T : Scheme.{0}} (t : T ⟶ S) {P Q : Over S} (g : P ⟶ Q) :
    ((Over.pullback t).map g).left ≫ pullback.snd Q.hom t = pullback.snd P.hom t := by
  simp

theorem isIso_pullback_conj {S T : Scheme.{0}} (t : T ⟶ S) {P Q P' Q' : Over S} (g : P ⟶ Q)
    (eP : P ≅ P') (eQ : Q ≅ Q') (h : IsIso ((Over.pullback t).map g).left) :
    IsIso ((Over.pullback t).map (eP.inv ≫ g ≫ eQ.hom)).left := by
  haveI : IsIso ((Over.forget _).map ((Over.pullback t).map g)) := h
  haveI : IsIso ((Over.pullback t).map g) := isIso_of_reflects_iso _ (Over.forget _)
  haveI : IsIso ((Over.pullback t).map (eP.inv ≫ g ≫ eQ.hom)) := by
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  exact inferInstanceAs (IsIso ((Over.forget T).map ((Over.pullback t).map (eP.inv ≫ g ≫ eQ.hom))))

theorem affine_case {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (U V : Over (Spec (CommRingCat.of R))) (g : V ⟶ U) [IsAffine U.left] [IsAffine V.left]
    [IsProper g.left] [LocallyOfFiniteType U.hom]
    (h : ∀ e, IsIso ((Over.pullback (thick R I e)).map g).left) (x : U.left)
    (hx : I ≤ (U.hom x).asIdeal) :
    ∃ s : Γ(U.left, ⊤), x ∈ U.left.basicOpen s ∧ IsIso (g.left ∣_ U.left.basicOpen s) := by
  let aU : R →+* Γ(U.left, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ U.hom.appTop).hom
  let aV : R →+* Γ(V.left, ⊤) := ((Scheme.ΓSpecIso (.of R)).inv ≫ V.hom.appTop).hom
  letI : Algebra R Γ(U.left, ⊤) := aU.toAlgebra
  letI : Algebra R Γ(V.left, ⊤) := aV.toAlgebra
  have hcomm : ((Scheme.ΓSpecIso (.of R)).inv ≫ U.hom.appTop) ≫ g.left.appTop =
      (Scheme.ΓSpecIso (.of R)).inv ≫ V.hom.appTop := by
    rw [← Over.w g, Scheme.Hom.comp_appTop, Category.assoc]
  let φ : Γ(U.left, ⊤) →ₐ[R] Γ(V.left, ⊤) :=
    { g.left.appTop.hom with
      commutes' := fun r => congrArg (fun f => f.hom r) hcomm }
  have wU : U.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(U.left, ⊤))) = U.hom :=
    toSpecΓ_comp U.hom
  have wV : V.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(V.left, ⊤))) = V.hom :=
    toSpecΓ_comp V.hom
  let eU : U ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Γ(U.left, ⊤)))) :=
    Over.isoMk U.left.isoSpec (by simpa [Scheme.isoSpec_hom] using wU)
  let eV : V ≅ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R Γ(V.left, ⊤)))) :=
    Over.isoMk V.left.isoSpec (by simpa [Scheme.isoSpec_hom] using wV)
  have hg' : (eV.inv ≫ g ≫ eU.hom).left = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    change V.left.isoSpec.inv ≫ g.left ≫ U.left.isoSpec.hom = _
    rw [Iso.inv_comp_eq, Scheme.isoSpec_hom, Scheme.isoSpec_hom, Scheme.toSpecΓ_naturality]
    rfl
  have hbij : ∀ e : ℕ, Function.Bijective
      (Algebra.TensorProduct.map φ (AlgHom.id R (R ⧸ I ^ (e + 1)))) := by
    intro e
    refine bijective_of_isIso_pullback (T := R ⧸ I ^ (e + 1)) φ
      ((Over.pullback (thick R I e)).map (eV.inv ≫ g ≫ eU.hom)).left ?_ ?_
      (isIso_pullback_conj _ g eV eU (h e))
    · rw [← hg']
      exact over_pullback_fst (thick R I e) (eV.inv ≫ g ≫ eU.hom)
    · exact over_pullback_snd (thick R I e) (eV.inv ≫ g ≫ eU.hom)
  haveI : IsFinite g.left := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  have hfin : φ.toRingHom.Finite := IsFinite.finite_app g.left ⊤ (isAffineOpen_top _)
  haveI : IsLocallyNoetherian U.left := LocallyOfFiniteType.isLocallyNoetherian U.hom
  haveI : IsNoetherianRing Γ(U.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨s, hs1, hker, hcok⟩ := ring_case φ hfin I hbij
  refine ⟨s, ?_, ?_⟩
  · have hq : (U.hom x).asIdeal = (U.left.toSpecΓ x).asIdeal.comap aU := by
      conv_lhs => rw [← wU]
      rfl
    have hJ : I.map (algebraMap R Γ(U.left, ⊤)) ≤ (U.left.toSpecΓ x).asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      exact hx.trans hq.le
    have hs : s ∉ (U.left.toSpecΓ x).asIdeal := fun hs =>
      (U.left.toSpecΓ x).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
        have := Ideal.sub_mem _ hs (hJ hs1)
        simpa using this))
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact hs
  · have hD : IsAffineOpen (U.left.basicOpen s) := (isAffineOpen_top _).basicOpen s
    rw [isIso_morphismRestrict_iff_isIso_app g.left hD, ConcreteCategory.isIso_iff_bijective]
    have e : g.left ⁻¹ᵁ U.left.basicOpen s = V.left.basicOpen (φ s) :=
      Scheme.preimage_basicOpen_top g.left s
    refine bijective_of_away g.left.appTop.hom
      (U.left.presheaf.map (homOfLE le_top).op).hom (V.left.presheaf.map (homOfLE le_top).op).hom
      _ ?_ s ?_ ?_ hker hcok
    · intro a
      have := g.left.naturality (homOfLE (le_top : U.left.basicOpen s ≤ ⊤)).op
      exact congrArg (fun f => f.hom a) this
    · exact (isAffineOpen_top _).isLocalization_of_eq_basicOpen s _ rfl
    · exact (isAffineOpen_top _).isLocalization_of_eq_basicOpen (φ s) _ e

theorem fibre_subsingleton {R : Type} [CommRing R] (I : Ideal R)
    (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X)
    (hiso : IsIso ((Over.pullback (thick R I 0)).map p).left) (c₁ c₂ : C.left)
    (h12 : p.left c₁ = p.left c₂) (hI : I ≤ (X.hom (p.left c₁)).asIdeal) : c₁ = c₂ := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk (I ^ (0 + 1))) := Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion (thick R I 0) := IsClosedImmersion.spec_of_surjective _ hsurj
  obtain ⟨y, hy⟩ : ∃ y, thick R I 0 y = X.hom (p.left c₁) := by
    have : X.hom (p.left c₁) ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
      rw [_root_.range_comap_of_surjective _ _ hsurj, Ideal.mk_ker]
      exact (PrimeSpectrum.mem_zeroLocus _ _).2 (by simpa using hI)
    exact this
  have hC : ∀ c, C.hom c = X.hom (p.left c) := fun c => by
    rw [← Over.w p]; rfl
  obtain ⟨z₁, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.hom) (g := thick R I 0)
    c₁ y (by rw [hC, hy])
  obtain ⟨z₂, hz₂, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := C.hom) (g := thick R I 0)
    c₂ y (by rw [hC, hy, h12])
  let P0 := ((Over.pullback (thick R I 0)).map p).left
  have hfst : ∀ z, pullback.fst X.hom (thick R I 0) (P0 z) =
      p.left (pullback.fst C.hom (thick R I 0) z) := fun z => by
    have := over_pullback_fst (thick R I 0) p
    exact congrArg (fun f => f z) this
  have hinj1 : Function.Injective (pullback.fst X.hom (thick R I 0)) :=
    (pullback.fst X.hom (thick R I 0)).isEmbedding.injective
  have hinj2 : Function.Injective P0 := P0.isEmbedding.injective
  have : z₁ = z₂ := hinj2 (hinj1 (by rw [hfst, hfst, hz₁, hz₂, h12]))
  rw [← hz₁, ← hz₂, this]

theorem isIso_restrict_thick {S T : Scheme.{0}} (t : T ⟶ S) (X C : Over S) (p : C ⟶ X)
    (W : X.left.Opens) (g : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ Over.mk (W.ι ≫ X.hom))
    (hg : g.left = p.left ∣_ W) (h : IsIso ((Over.pullback t).map p).left) :
    IsIso ((Over.pullback t).map g).left := by
  let a : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ C := Over.homMk (p.left ⁻¹ᵁ W).ι rfl
  let b : Over.mk (W.ι ≫ X.hom) ⟶ X := Over.homMk W.ι rfl
  have hcomm : a ≫ p = g ≫ b := by
    ext1
    change (p.left ⁻¹ᵁ W).ι ≫ p.left = g.left ≫ W.ι
    rw [hg, morphismRestrict_ι]
  have hsq : IsPullback a g p b :=
    IsPullback.of_map (Over.forget S) hcomm (by
      have h1 := (isPullback_morphismRestrict p.left W).flip
      rw [← hg] at h1
      exact h1)
  have hsq' := hsq.map (Over.pullback t)
  haveI : IsIso ((Over.forget T).map ((Over.pullback t).map p)) := h
  haveI : IsIso ((Over.pullback t).map p) := isIso_of_reflects_iso _ (Over.forget _)
  haveI : IsIso ((Over.pullback t).map g) := hsq'.isIso_snd_of_isIso
  exact inferInstanceAs (IsIso ((Over.forget T).map ((Over.pullback t).map g)))

theorem exists_nbhd {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X) [IsProper X.hom] [IsProper p.left]
    (h : ∀ e, IsIso ((Over.pullback (thick R I e)).map p).left) (x : X.left)
    (hx : I ≤ (X.hom x).asIdeal) : ∃ W : X.left.Opens, x ∈ W ∧ IsIso (p.left ∣_ W) := by
  obtain ⟨V', hV', hsub⟩ : ∃ V' : C.left.Opens, IsAffineOpen V' ∧ ∀ c, p.left c = x → c ∈ V' := by
    by_cases hc : ∃ c, p.left c = x
    · obtain ⟨c, rfl⟩ := hc
      obtain ⟨V', hV', hcV, -⟩ := exists_isAffineOpen_mem_and_subset (X := C.left) (x := c) (U := ⊤) trivial
      refine ⟨V', hV', fun c' hc' => ?_⟩
      rwa [fibre_subsingleton I X C p (h 0) c' c hc' (by rw [hc']; exact hx)]
    · exact ⟨⊥, isAffineOpen_bot _, fun c hc' => (hc ⟨c, hc'⟩).elim⟩
  have hcl : IsClosed (p.left '' (V' : Set C.left)ᶜ) :=
    p.left.isClosedMap _ V'.isOpen.isClosed_compl
  have hxO : x ∈ (p.left '' (V' : Set C.left)ᶜ)ᶜ := by
    rintro ⟨c, hc, rfl⟩
    exact hc (hsub c rfl)
  let O : X.left.Opens := ⟨_, hcl.isOpen_compl⟩
  obtain ⟨W, hW, hxW, hWO⟩ := exists_isAffineOpen_mem_and_subset (X := X.left) (x := x) (U := O) hxO
  have hle : p.left ⁻¹ᵁ W ≤ V' := by
    intro c hc
    by_contra hcV
    exact hWO hc ⟨c, hcV, rfl⟩
  haveI : IsAffine V'.toScheme := hV'
  haveI : IsAffineHom ((V'.ι ≫ p.left) ≫ X.hom) := isAffineHom_of_isAffine _
  haveI : IsAffineHom (V'.ι ≫ p.left) := IsAffineHom.of_comp _ X.hom
  have hWa : IsAffineOpen (p.left ⁻¹ᵁ W) := by
    have h1 := (hW.preimage (V'.ι ≫ p.left)).image_of_isOpenImmersion V'.ι
    have h2 : V'.ι ''ᵁ ((V'.ι ≫ p.left) ⁻¹ᵁ W) = p.left ⁻¹ᵁ W := by
      change V'.ι ''ᵁ (V'.ι ⁻¹ᵁ (p.left ⁻¹ᵁ W)) = p.left ⁻¹ᵁ W
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.2 hle
    rwa [h2] at h1
  haveI : IsAffine W.toScheme := hW
  haveI : IsAffine (p.left ⁻¹ᵁ W).toScheme := hWa
  let g : Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom) ⟶ Over.mk (W.ι ≫ X.hom) :=
    Over.homMk (p.left ∣_ W) (by
      change (p.left ∣_ W) ≫ W.ι ≫ X.hom = (p.left ⁻¹ᵁ W).ι ≫ C.hom
      rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w p])
  haveI : IsProper g.left := inferInstanceAs (IsProper (p.left ∣_ W))
  haveI : LocallyOfFiniteType (Over.mk (W.ι ≫ X.hom)).hom :=
    inferInstanceAs (LocallyOfFiniteType (W.ι ≫ X.hom))
  haveI : IsAffine (Over.mk (W.ι ≫ X.hom)).left := inferInstanceAs (IsAffine W.toScheme)
  haveI : IsAffine (Over.mk ((p.left ⁻¹ᵁ W).ι ≫ C.hom)).left :=
    inferInstanceAs (IsAffine (p.left ⁻¹ᵁ W).toScheme)
  obtain ⟨s, hs, hiso⟩ := affine_case I _ _ g
    (fun e => isIso_restrict_thick (thick R I e) X C p W g rfl (h e))
    (⟨x, hxW⟩ : W.toScheme) hx
  refine ⟨W.ι ''ᵁ (W.toScheme.basicOpen s), ⟨_, hs, rfl⟩, ?_⟩
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict p.left W _)).1 hiso

theorem isoOfThick : IsoOfThick := by
  intro R _ _ I hI X C p hX hp hiso
  haveI := hI
  let Ω : X.left.Opens := ⨆ W : {W : X.left.Opens // IsIso (p.left ∣_ W)}, W.1
  have hΩ : Ω = ⊤ := by
    by_contra hne
    obtain ⟨x₀, hx₀⟩ : ∃ x, x ∉ Ω := by
      by_contra hall
      push_neg at hall
      exact hne (eq_top_iff.2 fun x _ => hall x)
    have hT : IsClosed (X.hom '' (Ω : Set X.left)ᶜ) :=
      X.hom.isClosedMap _ Ω.isOpen.isClosed_compl
    obtain ⟨m, hmT, hm⟩ : ∃ m : PrimeSpectrum R,
        m ∈ (X.hom '' (Ω : Set X.left)ᶜ : Set (PrimeSpectrum R)) ∧ m.asIdeal.IsMaximal := by
      obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hT
      have hy : X.hom x₀ ∈ PrimeSpectrum.zeroLocus (J : Set R) := by
        rw [← hJ]; exact ⟨x₀, hx₀, rfl⟩
      have hJtop : J ≠ ⊤ := fun h => (X.hom x₀).isPrime.ne_top
        (top_le_iff.mp (h ▸ (PrimeSpectrum.mem_zeroLocus _ _).1 hy))
      obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hJtop
      refine ⟨⟨M, hM.isPrime⟩, ?_, hM⟩
      exact (Set.ext_iff.1 hJ _).2 hJM
    obtain ⟨x, hxZ, rfl⟩ := hmT
    have hIx : I ≤ (X.hom x).asIdeal :=
      (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)
    obtain ⟨W, hxW, hW⟩ := exists_nbhd I X C p hiso x hIx
    exact hxZ (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW⟩, hxW⟩)
  have hf : IsIso p.left :=
    IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
      (fun W : {W : X.left.Opens // IsIso (p.left ∣_ W)} => W.1) hΩ (fun W => W.2)
  haveI : IsIso ((Over.forget _).map p) := hf
  exact isIso_of_reflects_iso p (Over.forget _)

end GlobalTheory.CompanionTheory.Formal.IsoThick
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsoOfThickeningsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iso_of_thickenings : IsoOfThick := by
  first | exact @GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | exact GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick | (intros; apply GlobalTheory.CompanionTheory.Formal.IsoThick.isoOfThick <;> assumption)
end
end

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening

theorem _root_.GlobalTheory.T.grothendieck_existence_closed_proj : GEClosedProj := by
  intro R _ _ I hI N P Cs i β hi hβ
  obtain ⟨hbase, hsat, hanti, hcompat⟩ := GlobalTheory.CompanionTheory.GE.Family.vanIdeal_family R I N Cs i β hi hβ
  obtain ⟨n₀, hlift⟩ := GlobalTheory.CompanionTheory.GE.Lift.uniform_lift R I N
    (fun e => GlobalTheory.CompanionTheory.GE.vanIdeal (i e ≫ GlobalTheory.CompanionTheory.GE.thickι R I N e))
    (fun e => GlobalTheory.CompanionTheory.GE.vanIdeal_homog _) hbase hsat hcompat
  obtain ⟨J, hJ, h⟩ := GlobalTheory.CompanionTheory.GE.Tower.exists_limit_ideal R I hI N
    (fun e => GlobalTheory.CompanionTheory.GE.vanIdeal (i e ≫ GlobalTheory.CompanionTheory.GE.thickι R I N e))
    (fun e => GlobalTheory.CompanionTheory.GE.vanIdeal_homog _) hbase hanti n₀ hlift
  exact GlobalTheory.CompanionTheory.GE.exists_closed_of_homogIdeal R I N Cs i β hi hβ J hJ (fun e => (h e).1) (fun e => (h e).2)

namespace PositivityTheory.FormalThickening

theorem formalAlgebraisation : GlobalTheory.Published.FormalAlgebraisation := by
  refine ⟨?_, GlobalTheory.T.formal_algebraisation_schemes GlobalTheory.T.grothendieck_existence_closed_proj⟩
  intro R _ _ I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  obtain ⟨g, hg⟩ := GlobalTheory.T.formal_morphism_existence GlobalTheory.T.grothendieck_existence_closed GlobalTheory.T.iso_of_thickenings R I hI X Z hX hZs hZl hZq Y β b hb hβ f hf hfβ
  refine ⟨g, hg, fun g' hg' => ?_⟩
  exact GlobalTheory.T.formal_morphism_uniqueness R I hI X Z hX hZs Y b hb g' g (fun e => (hg' e).trans (hg e).symm)

end PositivityTheory.FormalThickening
