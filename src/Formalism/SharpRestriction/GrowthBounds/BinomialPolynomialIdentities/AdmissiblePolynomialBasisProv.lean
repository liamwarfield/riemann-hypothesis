module

public import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.IndexOffRange

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.PeBnOfLt
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem iv_inj (N n : ℕ) : Function.Injective (iv N n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [iv, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

theorem pe_Bn_of_lt {N : ℕ} (B : Fin N → ℕ) {i : ℕ} (h : i < N) : Bn B i = B ⟨i, h⟩ := by simp [Bn, h]

theorem expSet_eq (n N : ℕ) (B : Fin N → ℕ) :
    (fun m : Fin N × Fin n →₀ ℕ => m.mapDomain (iv N n)) '' {m | ∀ i, multideg m i = B i} =
      {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then Bn B i else 0} := by
  ext e
  constructor
  · rintro ⟨m, hm, rfl⟩ i
    by_cases h : i < N
    · rw [if_pos h, pe_Bn_of_lt B h, ← hm ⟨i, h⟩]
      unfold multideg
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ((i, a) : ℕ × Fin n) = iv N n (⟨i, h⟩, a) := rfl
      rw [this, Finsupp.mapDomain_apply_of_injective (iv_inj N n)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun a _ => ?_
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨⟨x, y⟩, hxy⟩
      simp only [iv, Prod.mk.injEq] at hxy
      exact h (hxy.1 ▸ x.2)
  · intro he
    have hsupp : (↑e.support : Set (ℕ × Fin n)) ⊆ Set.range (iv N n) := by
      rintro ⟨i, a⟩ hia
      by_cases h : i < N
      · exact ⟨(⟨i, h⟩, a), rfl⟩
      · exfalso
        have h0 := he i
        rw [if_neg h] at h0
        have := (Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a)
        simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hia
        exact hia this
    refine ⟨e.comapDomain (iv N n) (iv_inj N n).injOn, ?_, Finsupp.mapDomain_comapDomain _ (iv_inj N n) e hsupp⟩
    intro i
    have h0 := he i.val
    rw [if_pos i.2, pe_Bn_of_lt B i.2] at h0
    rw [← h0]
    unfold multideg
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.comapDomain_apply]
    rfl

theorem restPol : RestPol := by
  intro R _ n N B
  rw [(Formalism.InvariantFactorPaths.GelfandTsetlinBases.polynomial_b_rank n N (Bn B)).2.2 R, ← expSet_eq, Pol, MvPolynomial.restrictSupport_eq_span,
    Submodule.map_span, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro m _
  simp [rename_monomial]

end Formalism.MainNotions.G.ColumnFamilies
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.ExtendByZeroRestrictOfVanish
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem ext_last {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ext mu N = pEnd mu := by
  unfold ext pEnd
  rw [dite_eq_left (Nat.lt_succ_self N)]
  rfl

theorem ext_apply_of_lt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {i : ℕ} (h : i < N + 1) : ext mu i = mu ⟨i, h⟩ := by
  unfold ext
  rw [dite_eq_left h]

theorem ext_val {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (i : Fin (N + 1)) : ext mu i.val = mu i := by
  exact ext_apply_of_lt mu i.2

theorem ext_of_gt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {i : ℕ} (h : N < i) : ext mu i = 0 := by
  unfold ext
  rw [dite_eq_right (by omega)]

theorem restrict_extendByZero {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : res N (ext mu) = mu := by
  funext i
  exact ext_val mu i

theorem extendByZero_restrict_of_vanish {N n : ℕ} (μ : ℕ → Fin n → ℤ) (h : ∀ i, N < i → μ i = 0) : ext (res N μ) = μ := by
  funext i
  by_cases hi : i < N + 1
  · rw [ext_apply_of_lt _ hi]
    rfl
  · rw [ext_of_gt _ (by omega), h i (by omega)]

theorem ext_inj {N n : ℕ} {mu mu' : Fin (N + 1) → Fin n → ℤ} (h : ext mu = ext mu') : mu = mu' := by
  have h' := congrArg (res N) h
  rwa [restrict_extendByZero, restrict_extendByZero] at h'

theorem PPath_ext' {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {P Q : PPath n N LL B} (h : P.mu = Q.mu) :
    P = Q := by
  obtain ⟨mu, z, d, s⟩ := P
  obtain ⟨mu', z', d', s'⟩ := Q
  cases h
  rfl

abbrev WIdx (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :=
  {x : PPath n N LL B × (ℤ → Finset (Fin n)) // IsSt x.1.mu x.2}

def f17 (hT : RestPathTo) (hS : RestStd) {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (x : WIdx n N LL B) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) :=
  Subtype.mk (ext x.1.1.mu, x.1.2)
    ⟨hT n N LL B x.1.1, fun _ hi => ext_of_gt _ hi, by
      show Formalism.InvariantFactorPaths.GelfandTsetlinBases.IsStd (ext x.1.1.mu N) x.1.2
      rw [ext_last]; exact (hS n N x.1.1.mu x.1.2).1 x.2⟩

theorem pathWordMap_fst_eq (hT : RestPathTo) (hS : RestStd) {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ}
    (x : WIdx n N LL B) : (f17 hT hS x).1 = (ext x.1.1.mu, x.1.2) := rfl

theorem pathWordMap_bijective (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) {n N : ℕ} {LL : Letters (Fin N)}
    {B : Fin N → ℕ} : Function.Bijective (f17 hT hS (n := n) (N := N) (LL := LL) (B := B)) := by
  constructor
  · rintro ⟨⟨P, I⟩, hPI⟩ ⟨⟨Q, J⟩, hQJ⟩ h
    have h1 := congrArg (fun y => y.1.1) h
    have h2 := congrArg (fun y => y.1.2) h
    simp only [pathWordMap_fst_eq] at h1 h2
    have hPQ : P = Q := PPath_ext' (ext_inj h1)
    subst hPQ
    subst h2
    rfl
  · rintro ⟨⟨μ, I⟩, hpath, hzero, hstd⟩
    obtain ⟨P, hP⟩ := hF n N LL B μ hpath
    have hend : pEnd P.mu = μ N := by
      rw [← ext_last, hP, extendByZero_restrict_of_vanish μ hzero]
    have hst : IsSt P.mu I := (hS n N P.mu I).2 (by rw [hend]; exact hstd)
    refine ⟨⟨(P, I), hst⟩, ?_⟩
    apply Subtype.ext
    show (ext P.mu, I) = (μ, I)
    rw [hP, extendByZero_restrict_of_vanish μ hzero]

def e17 (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) (n N : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) :
    WIdx n N LL B ≃ Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) :=
  Equiv.ofBijective (f17 hT hS) (pathWordMap_bijective hT hF hS)

theorem rename_Psi (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) (hP : RestPsi) (R : Type) [CommRing R]
    {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (x : WIdx n N LL B) :
    rename (iv N n) (Psi R x.1.1.mu x.1.2) =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiFam R n N (isV LL) (Bn B) (e17 hT hF hS n N LL B x) := by
  rw [hP R n N LL B x.1.1 x.1.2 ((hS n N x.1.1.mu x.1.2).1 x.2).1]
  rfl

theorem word_basis_of_path_restrictions (D : Formalism.BasicNotions.D7) (hT : RestPathTo) (hF : RestPathFrom) (hS : RestStd) (hP : RestPsi)
    (hPol : RestPol) : Formalism.MainNotions.CovariantDegrees.PathBasisOverRing D := by
  intro R _ N n _ LL B
  have hρ : Function.Injective
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap :=
    rename_injective _ (iv_inj N n)
  obtain ⟨hli, hsp⟩ := Formalism.InvariantFactorPaths.GelfandTsetlinBases.Top.psiPath_basis n N (isV LL) (Bn B) R
  have hfam : ⇑(rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap ∘
      (fun x : WIdx n N LL B => Psi R x.1.1.mu x.1.2) =
      (fun y : Formalism.InvariantFactorPaths.GelfandTsetlinBases.PathIdx n N (isV LL) (Bn B) => Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath R (isV LL) y.1.1 N y.1.2) ∘
        (e17 hT hF hS n N LL B) := by
    funext x
    exact rename_Psi hT hF hS hP R x
  have hS' : {G | ∃ P : PPath n N LL B, ∃ I : ℤ → Finset (Fin n), IsSt P.mu I ∧ G = Psi R P.mu I} =
      Set.range (fun x : WIdx n N LL B => Psi R x.1.1.mu x.1.2) := by
    ext G
    constructor
    · rintro ⟨P, I, h, rfl⟩
      exact ⟨⟨(P, I), h⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1.1, x.1.2, x.2, rfl⟩
  refine ⟨?_, ?_⟩
  · apply LinearIndependent.of_comp
      (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] MvPolynomial (ℕ × Fin n) R).toLinearMap
    rw [hfam]
    exact hli.comp _ (e17 hT hF hS n N LL B).injective
  · apply Submodule.map_injective_of_injective hρ
    rw [hPol R n N B, Submodule.map_span, hS', ← Set.range_comp, hfam,
      (e17 hT hF hS n N LL B).surjective.range_comp, hsp]

end Formalism.MainNotions.G.ColumnFamilies
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.KcolEqPathWord
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.LemmaBAlt

theorem wedgeR_eq_wedgeF {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) :
    wedgeR x K = Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF K x := by
  funext J
  unfold wedgeR Formalism.InvariantFactorPaths.GelfandTsetlinBases.wedgeF Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

theorem contrR_eq_contrF {n : ℕ} {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) :
    contrR x K = Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF K x := by
  funext J
  unfold contrR Formalism.InvariantFactorPaths.GelfandTsetlinBases.contrF Formalism.InvariantFactorPaths.GelfandTsetlinBases.sg
  rw [Finset.compl_eq_univ_sdiff]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

theorem colHeight_eq {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : Formalism.InvariantFactorPaths.GelfandTsetlinBases.colHeight mu c = colH mu c := rfl

theorem ext_apply {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (j : ℕ) (h : j < N + 1) : ext mu j = mu ⟨j, h⟩ := by
  unfold ext; rw [dite_eq_left h]

theorem colH_step {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} (P : PPath n N LL B) (c : ℤ) (j : ℕ) (h : j < N) :
    if LL.vec ⟨j, h⟩ then colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c
    else colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c := by
  have hs := P.step ⟨j, h⟩
  have e1 : (Fin.castSucc (⟨j, h⟩ : Fin N)) = ⟨j, by omega⟩ := rfl
  have e2 : (Fin.succ (⟨j, h⟩ : Fin N)) = ⟨j + 1, by omega⟩ := rfl
  rw [e1, e2] at hs
  split_ifs with hv
  · rw [if_pos hv] at hs
    exact column_height_mono hs.1 c
  · rw [if_neg hv] at hs
    exact column_height_mono hs.1 c

theorem Kcol_eq_pathWord (R : Type*) [CommRing R] {n N : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ}
    (P : PPath n N LL B) (c : ℤ) (j : ℕ) (hj : j ≤ N) (J : Finset (Fin n)) :
    rename (iv N n) (Kcol R P.mu c j J) =
      Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c
        (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j J := by
  induction j generalizing J with
  | zero =>
    simp only [Kcol, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    exact map_exterior_one (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom J
  | succ j ih =>
    have h : j < N := hj
    have ih' := ih (by omega)
    simp only [Kcol, Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    rw [dite_eq_left h]
    have hm := map_column_operator (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom c
      (colH (P.mu ⟨j, by omega⟩) c) (colH (P.mu ⟨j + 1, by omega⟩) c) (letVec R ⟨j, h⟩) (Kcol R P.mu c j) J
    have h1 : (fun m => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom
        (letVec R (⟨j, h⟩ : Fin N) m)) = fun a => (X (j, a) : MvPolynomial (ℕ × Fin n) R) := by
      funext m; simp [letVec, iv]
    have h2 : (fun J => (rename (iv N n) : MvPolynomial (Fin N × Fin n) R →ₐ[R] _).toRingHom
        (Kcol R P.mu c j J)) = Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c
        (fun i a => (X (i, a) : MvPolynomial (ℕ × Fin n) R)) j := funext ih'
    rw [h1, h2] at hm
    have hm' : rename (iv N n) (colStep c (colH (P.mu ⟨j, by omega⟩) c) (colH (P.mu ⟨j + 1, by omega⟩) c)
        (letVec R ⟨j, h⟩) (Kcol R P.mu c j) J) = _ := hm
    rw [hm', colHeight_eq, colHeight_eq, ext_apply P.mu j (by omega), ext_apply P.mu (j + 1) (by omega)]
    have hst := colH_step P c j h
    have hV : isV LL j = LL.vec ⟨j, h⟩ := by unfold isV; rw [dite_eq_left h]
    rw [hV]
    unfold colStep Formalism.InvariantFactorPaths.GelfandTsetlinBases.stepF
    by_cases hv : LL.vec ⟨j, h⟩ = true
    · rw [if_pos hv] at hst
      rw [hv]
      by_cases he : colH (P.mu ⟨j + 1, by omega⟩) c = colH (P.mu ⟨j, by omega⟩) c
      · rw [if_pos he, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg he, if_pos (by omega)]
        by_cases hc : 1 ≤ c
        · simp [hc, wedgeR_eq_wedgeF]
        · simp [hc, contrR_eq_contrF]
    · rw [if_neg hv] at hst
      have hv' : LL.vec ⟨j, h⟩ = false := by simpa using hv
      rw [hv']
      by_cases he : colH (P.mu ⟨j + 1, by omega⟩) c = colH (P.mu ⟨j, by omega⟩) c
      · rw [if_pos he, if_neg (by omega), if_neg (by omega)]
      · rw [if_neg he, if_neg (by omega), if_pos (by omega)]
        by_cases hc : 1 ≤ c
        · simp [hc, contrR_eq_contrF]
        · simp [hc, wedgeR_eq_wedgeF]

theorem colH_off {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {c : ℤ} (hc : c ∉ colRange mu) (i : Fin (N + 1)) :
    colH (mu i) c = if 1 ≤ c then 0 else n := by
  have hT : ∀ m, |mu i m| ≤ ∑ i, ∑ m, |mu i m| := fun m => abs_entry_le_total mu i m
  have hT0 : (0 : ℤ) ≤ ∑ i, ∑ m, |mu i m| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  simp only [colRange, Finset.mem_Icc, not_and_or, not_le] at hc
  unfold colH
  rcases hc with hc | hc
  · rw [if_neg (by omega)]
    rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
    intro m _
    have := abs_le.mp (hT m)
    omega
  · rw [if_pos (by omega)]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _
    have := abs_le.mp (hT m)
    omega

theorem pathWord_off (R : Type*) [CommRing R] {n N : ℕ} (isVec : ℕ → Bool) (mu : Fin (N + 1) → Fin n → ℤ) {c : ℤ}
    (hc : c ∉ colRange mu) (Xr : ℕ → Fin n → R) (j : ℕ) (hj : j ≤ N) :
    Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord isVec (ext mu) c Xr j = Formalism.InvariantFactorPaths.GelfandTsetlinBases.oneF := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord]
    rw [colHeight_eq, colHeight_eq, ext_apply mu j (by omega), ext_apply mu (j + 1) (by omega),
      colH_off mu hc, colH_off mu hc, if_pos rfl]
    exact ih (by omega)

theorem restPsi : RestPsi := by
  intro R _ n N LL B P I hI
  unfold Psi Formalism.InvariantFactorPaths.GelfandTsetlinBases.psiPath
  rw [map_prod]
  rw [finprod_eq_prod_of_mulSupport_subset (s := colRange P.mu)]
  · exact Finset.prod_congr rfl fun c _ => Kcol_eq_pathWord R P c N le_rfl (I c)
  · intro c hc
    by_contra hcn
    apply hc
    have hcn' : c ∉ colRange P.mu := hcn
    show Formalism.InvariantFactorPaths.GelfandTsetlinBases.pathWord (isV LL) (ext P.mu) c _ N (I c) = 1
    rw [pathWord_off _ _ _ hcn' _ N le_rfl]
    have hcard := hI c
    rw [colHeight_eq] at hcard
    have h0 : colH (pEnd P.mu) c = if 1 ≤ c then 0 else n := colH_off P.mu hcn' (Fin.last N)
    have : (I c).card = 0 := by
      rw [hcard, h0]
      split_ifs <;> simp
    rw [Finset.card_eq_zero] at this
    rw [this]
    simp [Formalism.InvariantFactorPaths.GelfandTsetlinBases.oneF]

end Formalism.MainNotions.G.ColumnFamilies
end
end

namespace Formalism.MainNotions.G.ColumnFamilies

theorem admissible_standardPath_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PathBasisOverRing D :=
  word_basis_of_path_restrictions D restPathTo restPathFrom restStd restPsi restPol

theorem admissible_polynomial_basis (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.PathColumnBasis D := Formalism.MainNotions.CovariantDegrees.path_basis_of_field_basis D (admissible_standardPath_basis D)

end Formalism.MainNotions.G.ColumnFamilies
