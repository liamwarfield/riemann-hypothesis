module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

namespace UpperTheory.V.AlgebraTools

section Gen

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

def FinOrb (K K' : Subgroup G) (x : G) : Prop := (MulAction.orbit K (x : G ⧸ K')).Finite

def HeckePair (I : Subgroup G) : Prop := ∀ x : G, FinOrb I I x


open scoped Classical in
open Classical in
def hk2 (ρ : Representation A G M) (K K' : Subgroup G) (x : G) : fixd ρ K' →ₗ[A] fixd ρ K :=
  if h : ∀ v ∈ fixd ρ K', dc ρ K K' x v ∈ fixd ρ K then (dc ρ K K' x).restrict h else 0

def hk (ρ : Representation A G M) (I : Subgroup G) (x : G) : Module.End A (fixd ρ I) := hk2 ρ I I x

theorem fixd_anti (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) : fixd ρ K ≤ fixd ρ I :=
  fun _ hv u hu => hv u (h hu)

def inc (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) : fixd ρ K →ₗ[A] fixd ρ I :=
  Submodule.inclusion (fixd_anti ρ h)

def trc (ρ : Representation A G M) (K I : Subgroup G) : fixd ρ I →ₗ[A] fixd ρ K := hk2 ρ K I 1


variable (A)

abbrev permRep (I : Subgroup G) : Representation A G (MonoidAlgebra A (G ⧸ I)) := Representation.ofMulAction A G (G ⧸ I)

def HkAlg (I : Subgroup G) : Subalgebra A (Module.End A (fixd (permRep A I) I)) :=
  Algebra.adjoin A (Set.range (hk (permRep A I) I))

def hT (I : Subgroup G) (x : G) : HkAlg A I := ⟨hk (permRep A I) I x, Algebra.subset_adjoin ⟨x, rfl⟩⟩

structure LeviFact (I : Subgroup G) where
  Uf : Subgroup G
  Mf : Subgroup G
  Lf : Subgroup G
  M_U : ∀ m ∈ Mf, ∀ u ∈ Uf, m * u * m⁻¹ ∈ Uf
  M_L : ∀ m ∈ Mf, ∀ l ∈ Lf, m * l * m⁻¹ ∈ Lf
  uniq : ∀ u ∈ Uf, ∀ m ∈ Mf, ∀ l ∈ Lf, u * m * l = 1 → u = 1 ∧ m = 1
  fact : ∀ g ∈ I, ∃ u ∈ Uf ⊓ I, ∃ m ∈ Mf ⊓ I, ∃ l ∈ Lf ⊓ I, g = u * m * l

def LeviFact.Pos {I : Subgroup G} (F : LeviFact I) (m : G) : Prop :=
  m ∈ F.Mf ∧ (∀ u ∈ F.Uf ⊓ I, m * u * m⁻¹ ∈ I) ∧ ∀ l ∈ F.Lf ⊓ I, m⁻¹ * l * m ∈ I

def LeviFact.NormJ {I : Subgroup G} (F : LeviFact I) (m : G) : Prop :=
  ∀ j ∈ F.Mf ⊓ I, m * j * m⁻¹ ∈ I ∧ m⁻¹ * j * m ∈ I

end Gen

section Perm

variable {n : ℕ}

def invLen (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).card

def pm (R : Type) [CommRing R] (n : ℕ) : Equiv.Perm (Fin n) →* GL (Fin n) R :=
  (Matrix.permMatrixHom (n := Fin n) (R := R)).toHomUnits

theorem pm_apply (R : Type) [CommRing R] (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (pm R n w : Matrix (Fin n) (Fin n) R) i j = if i = w j then 1 else 0 := by
  simp only [pm, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  exact propext Equiv.Perm.inv_eq_iff_eq

end Perm

section GeneralLinearIntegers

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

def unitsC (C : Subgroup 𝓀[k]ˣ) : Subgroup kˣ :=
  (C.comap (Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom)).map (Units.map (algebraMap 𝒪[k] k).toMonoidHom)

def torC (C : Subgroup 𝓀[k]ˣ) : Subgroup (Fin n → kˣ) := Subgroup.pi Set.univ fun _ => unitsC k C

def unipO : Subgroup (GL (Fin n) k) := unipB k (Fin n) ⊓ KO k (Fin n)

def iwC (C : Subgroup 𝓀[k]ˣ) : Subgroup (GL (Fin n) k) :=
  KOne k (Fin n) ⊔ unipO k n ⊔ (torC k n C).map (diagT k (Fin n))

variable {k n}

def IsUnif (x : kˣ) : Prop := ∃ p : 𝒪[k], Irreducible p ∧ algebraMap 𝒪[k] k p = x

def Dom (t : Fin n → kˣ) : Prop := ∀ i j, i ≤ j → valuation k (t i : k) ≤ valuation k (t j : k)

theorem dom_one : Dom (1 : Fin n → kˣ) := fun _ _ _ => le_rfl

def pw (x : kˣ) (a : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => x ^ a i

def fund (n m : ℕ) : Fin n → ℤ := fun i => if (i : ℕ) < m then 1 else 0

theorem exists_isUnif : ∃ x : kˣ, IsUnif x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have : algebraMap 𝒪[k] k p ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  exact ⟨Units.mk0 _ this, p, hp, rfl⟩

end GeneralLinearIntegers

end UpperTheory.V.AlgebraTools
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplEx
open IsLocalRing UpperTheory.V.AlgebraTools

private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  simpa [smul_eq_mul, Ideal.mul_top] using h

private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, ← ha, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply]
  simp

theorem UpperTheory.V.AlgebraTools.isCplAt_cplAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime], IsCplAt R p (CplAt R p) := by
  intro R _ _ p _
  let L := Localization.AtPrime p
  have hRB : ∀ r : R, algebraMap R (CplAt R p) r =
      algebraMap L (CplAt R p) (algebraMap R L r) := fun r =>
    IsScalarTower.algebraMap_apply R L (CplAt R p) r
  refine ⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion L (maximalIdeal L), inferInstance, ?_, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq R L (CplAt R p), ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal
  · intro n b
    obtain ⟨a', ha'⟩ := dense_loc L n b
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
    refine ⟨r, s, s.2, ?_⟩
    have e : algebraMap R (CplAt R p) s * b - algebraMap R (CplAt R p) r =
        algebraMap R (CplAt R p) s *
          (b - algebraMap L (CplAt R p) (IsLocalization.mk' L r s)) := by
      rw [mul_sub, hRB, hRB, ← map_mul, mul_comm (algebraMap R L s), IsLocalization.mk'_spec]
    rw [e]
    exact Ideal.mul_mem_left _ _ ha'
  · intro n a ha
    rw [hRB] at ha
    have h1 := strict_loc L n _ ha
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff p.primeCompl] at h1
    obtain ⟨⟨⟨b, hb⟩, s⟩, hx⟩ := h1
    simp only [← map_mul] at hx
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl L).1 hx
    refine ⟨c * s, ?_, ?_⟩
    · exact p.primeCompl.mul_mem c.2 s.2
    · have : (c : R) * s * a = c * b := by
        rw [mul_assoc, mul_comm (s : R) a]
        exact hc
      rw [this]
      exact Ideal.mul_mem_left _ _ hb
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkBern
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem UpperTheory.V.AlgebraTools.hkBern_reg {R : Type} [CommRing R] {n : ℕ} {a c : Fin n} (hac : a ≠ c)
    (y : MvPolynomial (Fin n) R) (h : (X a - X c) * y = 0) : y = 0 := by
  let φ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval fun j => if j = a then X a + X c else X j
  let ψ : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R :=
    aeval fun j => if j = a then X a - X c else X j
  have hψ : ψ.comp φ = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = a
    · simp [φ, ψ, hj, hac.symm]
    · simp [φ, ψ, hj]
  have h1 : φ (X a - X c) = X a := by simp [φ, hac.symm]
  have h2 : X a * φ y = X a * 0 := by rw [mul_zero, ← h1, ← map_mul, h, map_zero]
  have h3 : φ y = 0 := (MvPolynomial.isRegular_X (R := R) (n := a)).left h2
  have h4 := AlgHom.congr_fun hψ y
  rw [AlgHom.comp_apply, h3, map_zero, AlgHom.id_apply] at h4
  exact h4.symm

theorem UpperTheory.V.AlgebraTools.hkBern :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R, (X a - X c) * y = x - rename (swap a c) x ∧
        b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y)) ∧
      ∀ z : MvPolynomial (Fin n) R, z.IsSymmetric → ∀ w, b.T w * b.th z = b.th z * b.T w := by
  intro R _ n q H _ _ b
  have main : ∀ (a c : Fin n), a.val + 1 = c.val → ∀ x : MvPolynomial (Fin n) R, ∃ y : MvPolynomial (Fin n) R,
      (X a - X c) * y = x - rename (swap a c) x ∧
        b.T (swap a c) * b.th x = b.th (rename (swap a c) x) * b.T (swap a c) + (q - 1) • b.th (X a * y) := by
    intro a c hac
    have hX : ∀ j : Fin n, ∃ y : MvPolynomial (Fin n) R,
        (X a - X c) * y = X j - rename (swap a c) (X j) ∧
        b.T (swap a c) * b.th (X j) = b.th (rename (swap a c) (X j)) * b.T (swap a c) + (q - 1) • b.th (X a * y) := by
      intro j
      by_cases ha : j = a
      · subst ha
        refine ⟨1, by simp, ?_⟩
        rw [rename_X, swap_apply_left, mul_one]
        exact b.relA j c hac
      · by_cases hc : j = c
        · subst hc
          refine ⟨-1, by simp, ?_⟩
          rw [rename_X, swap_apply_right, mul_neg, mul_one, map_neg, smul_neg, ← sub_eq_add_neg]
          exact b.relB a j hac
        · refine ⟨0, by simp [swap_apply_of_ne_of_ne ha hc], ?_⟩
          rw [rename_X, swap_apply_of_ne_of_ne ha hc, mul_zero, map_zero, smul_zero, add_zero]
          exact b.comm a c hac j ha hc
    intro x
    induction x using MvPolynomial.induction_on with
    | C r =>
      refine ⟨0, by simp, ?_⟩
      rw [rename_C, mul_zero, map_zero, smul_zero, add_zero, ← MvPolynomial.algebraMap_eq, AlgHom.commutes,
        Algebra.commutes]
    | add p p' hp hp' =>
      obtain ⟨y, h1, h2⟩ := hp
      obtain ⟨y', h1', h2'⟩ := hp'
      refine ⟨y + y', ?_, ?_⟩
      · rw [mul_add, h1, h1', map_add (f := _)]; ring
      · rw [map_add (f := _), map_add (f := _), map_add (f := _), mul_add, h2, h2', mul_add, map_add (f := _), add_mul, smul_add]; abel
    | mul_X p j hp =>
      obtain ⟨y, h1, h2⟩ := hp
      obtain ⟨y', h1', h2'⟩ := hX j
      refine ⟨y * X j + rename (swap a c) p * y', ?_, ?_⟩
      · rw [map_mul]
        linear_combination (X j) * h1 + rename (swap a c) p * h1'
      · have e : X a * (y * X j + rename (swap a c) p * y') =
            (X a * y) * X j + rename (swap a c) p * (X a * y') := by ring
        rw [e, map_add (f := _), map_mul b.th (X a * y), map_mul b.th _ (X a * y'), map_mul (rename _), map_mul b.th p,
          map_mul b.th (rename _ p), ← mul_assoc, h2, add_mul, mul_assoc, h2', mul_add, smul_add, smul_mul_assoc,
          mul_smul_comm, mul_assoc]
        abel
  refine ⟨main, fun z hz => ?_⟩
  refine UpperTheory.V.AlgebraTools.hkInd n (fun w => b.T w * b.th z = b.th z * b.T w) ?_ ?_
  · simp only [b.T_one, one_mul, mul_one]
  · intro a c hac w hw ih
    obtain ⟨y, h1, h2⟩ := main a c hac z
    have hne : a ≠ c := by
      rintro rfl
      omega
    rw [hz (swap a c)] at h1 h2
    rw [sub_self] at h1
    rw [UpperTheory.V.AlgebraTools.hkBern_reg hne y h1, mul_zero, map_zero, smul_zero, add_zero] at h2
    rw [b.T_mul a c hac w hw, mul_assoc, ih, ← mul_assoc, h2, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplUniq
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.nonempty_algEquiv :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (B' : Type) [CommRing B'] [IsLocalRing B'] [Algebra R B'],
      IsCplAt R p B → IsCplAt R p B' → Nonempty (B ≃ₐ[R] B') := by
  intro R _ p B _ _ _ B' _ _ _ hB hB'
  haveI : IsAdicComplete (maximalIdeal B) B := hB.complete
  haveI : IsAdicComplete (maximalIdeal B') B' := hB'.complete
  obtain ⟨ψ, hψ, -⟩ := IsCplAt.existsUnique_lift R p B hB B' (algebraMap R B') hB'.comap_eq
  obtain ⟨χ, hχ, -⟩ := IsCplAt.existsUnique_lift R p B' hB' B (algebraMap R B) hB.comap_eq
  obtain ⟨_, -, huB⟩ := IsCplAt.existsUnique_lift R p B hB B (algebraMap R B) hB.comap_eq
  obtain ⟨_, -, huB'⟩ := IsCplAt.existsUnique_lift R p B' hB' B' (algebraMap R B') hB'.comap_eq
  have h1 : χ.comp ψ = RingHom.id B := by
    have ha : (χ.comp ψ).comp (algebraMap R B) = algebraMap R B := by
      rw [RingHom.comp_assoc, hψ, hχ]
    rw [huB _ ha, huB (RingHom.id B) (RingHom.id_comp _)]
  have h2 : ψ.comp χ = RingHom.id B' := by
    have ha : (ψ.comp χ).comp (algebraMap R B') = algebraMap R B' := by
      rw [RingHom.comp_assoc, hχ, hψ]
    rw [huB' _ ha, huB' (RingHom.id B') (RingHom.id_comp _)]
  refine ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom ψ χ h2 h1) ?_⟩
  intro x
  exact congrArg (fun φ : R →+* B' => φ x) hψ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaL
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.entry_of_single {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (a b : ι) :
    (single a a (1 : R) * M * single b b (1 : R) : Matrix ι ι R) a b = M a b := by
  simp

theorem UpperTheory.V.AlgebraTools.lemma_L :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ : Fin n → Γ →* Rˣ), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → (∀ g : Fin n → Γ, (List.ofFn fun i => ((r (g i) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - algebraMap R _ ((ψ i (g i) : Rˣ) : R)).prod = 0) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ z : MonoidAlgebra R Γ, (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z).charpoly.map (residue R) = ∏ i, (X - C (residue R (MonoidAlgebra.lift R R Γ ((Units.coeHom _).comp (ψ i)) z)))) → ∃ (z : MonoidAlgebra R Γ) (g : GL (Fin n) R), (∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z - MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ j)) z)) ∧ (∀ i, (g : Matrix (Fin n) (Fin n) R) * lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) i * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = single i i 1) ∧ ∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R) := by
  intro R Γ _ _ _ n r ψ hcard hprod hinj hchar
  obtain ⟨z, hz⟩ := sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hcard hinj
  have hord := ord_ext ((Units.coeHom _).comp r) (fun i => (Units.coeHom R).comp (ψ i)) hprod
  obtain ⟨hcoi, htri, hdiag⟩ := lag_triangular
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i))) z hord hz
  have hne := lag_ne_zero (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) _ hz (hchar z)
  obtain ⟨g, hg⟩ := coi_conj_single _ hcoi hne
  refine ⟨z, g, hz, hg, fun s => ?_⟩
  set e := lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z)
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) with he
  have hρ : MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r)
      (MonoidAlgebra.of R Γ s) = ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    simp [MonoidAlgebra.lift_of]
  have hχ : ∀ i, MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) (MonoidAlgebra.of R Γ s)
      = ((ψ i s : Rˣ) : R) := fun i => by
    simp [MonoidAlgebra.lift_of]
  have hinv : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 :=
    Units.inv_mul g
  have key : ∀ i j, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      ((g : Matrix (Fin n) (Fin n) R) * (e i * ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * e j)
        * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j := by
    intro i j
    refine (UpperTheory.V.AlgebraTools.entry_of_single (((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j).symm.trans ?_
    rw [← hg i, ← hg j]
    congr 1
    simp only [Units.val_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)), hinv, Matrix.one_mul]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [key, ← hρ, htri _ i j hji]
    simp
  · rw [key, ← hρ, hdiag, Matrix.mul_smul, Matrix.smul_mul, hg i, hχ]
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOneAlt
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem pair_lt {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) (u : Perm (Fin n)) (hu : u⁻¹ a < u⁻¹ c) :
    (b.T (swap a c) * b.T u - q • b.T u) + (b.T (swap a c) * b.T (swap a c * u) - q • b.T (swap a c * u)) = 0 := by
  have hu : b.T (swap a c * u) = b.T (swap a c) * b.T u := b.T_mul a c h u hu
  have hsq := b.T_sq a c h
  rw [hu, ← mul_assoc, hsq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  module

private theorem swap_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := by
    intro e
    rw [e] at h
    omega
  have key : ∀ w : Perm (Fin n), (b.T (swap a c) * b.T w - q • b.T w)
      + (b.T (swap a c) * b.T (swap a c * w) - q • b.T (swap a c * w)) = 0 := by
    intro w
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact pair_lt b h w hw
    · have hu : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
        simpa [Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have := pair_lt b h (swap a c * w) hu
      rw [← mul_assoc, swap_mul_self, one_mul] at this
      rw [add_comm]
      exact this
  have hsum : ∑ w, (b.T (swap a c) * b.T w - q • b.T w) = 0 := by
    refine Finset.sum_ninvolution (fun w => swap a c * w) key ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simp [mul_assoc] at this
      exact this.symm
    · intro w
      rw [← mul_assoc, swap_mul_self, one_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

theorem UpperTheory.V.AlgebraTools.hkOne :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ w, b.T w * b.one = q ^ invN w • b.one) ∧ b.one * b.one = poin (n := n) q • b.one := by
  intro R _ n q H _ _ b
  have hinv := UpperTheory.V.AlgebraTools.hkInv n
  have p1 : ∀ w, b.T w * b.one = q ^ invN w • b.one := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · rw [b.T_one, one_mul]
      simp [invN, hinv.2.2.1]
    · intro a c h w hw ih
      rw [b.T_mul a c h w hw, mul_assoc, ih, mul_smul_comm, swap_one b h, smul_smul,
        (hinv.1 a c h w hw).2.2, pow_succ]
  refine ⟨p1, ?_⟩
  show (∑ w, b.T w) * b.one = _
  rw [Finset.sum_mul]
  simp_rw [p1]
  rw [← Finset.sum_smul]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotQuot
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.regular_quotient_cotInd :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      IsRegularLocalRing (R ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (R ⧸ Ideal.span (Set.range x)) + (Fintype.card κ : ℕ) = ringKrullDim R ∧
      (Ideal.span (Set.range x)).IsPrime := by
  intro R _ _ κ _ x hx
  classical
  obtain ⟨s, y, -, hs, hc⟩ := cotInd_extend R κ x hx
  rw [Set.Sum.elim_range] at hs
  have hd : ringKrullDim R = ((Fintype.card κ + s : ℕ) : WithBot ℕ∞) := by
    rw [hc, IsRegularLocalRing.spanFinrank_maximalIdeal]
  set I := Ideal.span (Set.range x) with hI
  have hle : I ≤ maximalIdeal R := by
    rw [← hs]
    exact Ideal.span_mono Set.subset_union_left
  have hne : I ≠ ⊤ := fun h => Ideal.IsPrime.ne_top' (top_le_iff.mp (h ▸ hle))
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (R ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) = maximalIdeal (R ⧸ I) :=
    map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (y i)) = maximalIdeal (R ⧸ I) := by
    rw [← hmax, ← hs, Ideal.span_union, Ideal.map_sup, ← hI, Ideal.map_quotient_self, bot_sup_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hfin : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (s : ℕ) := by
    rw [← hspan]
    have h1 := Submodule.spanFinrank_span_le_ncard_of_finite (R := R ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (y i))
    have h2 : (Set.range fun i => Ideal.Quotient.mk I (y i)).ncard ≤ s := by
      rw [← Set.image_univ]
      exact (Set.ncard_image_le Set.finite_univ).trans (by simp [Set.ncard_univ])
    exact_mod_cast h1.trans h2
  have hdim : ((s : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    have h1 := ringKrullDim_le_ringKrullDim_quotient_add_encard (Set.range x)
      (by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        rintro _ ⟨k, rfl⟩
        exact hx.mem k)
    rw [hd] at h1
    have h2 : (Set.range x).encard ≤ (Fintype.card κ : ℕ∞) := by
      rw [← Set.image_univ]
      refine (Set.encard_image_le _ _).trans ?_
      rw [Set.encard_univ, ENat.card_eq_coe_fintype_card]
    have hnb : ringKrullDim (R ⧸ I) ≠ ⊥ := ringKrullDim_ne_bot
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hnb
    rw [← hn] at h1 ⊢
    have h3 : (Fintype.card κ : ℕ∞) + (s : ℕ∞) ≤ n + (Set.range x).encard := by
      exact_mod_cast h1
    have h4 : (s : ℕ∞) + (Fintype.card κ : ℕ∞) ≤ n + (Fintype.card κ : ℕ∞) := by
      rw [add_comm]
      exact h3.trans (by gcongr)
    have h5 : (s : ℕ∞) ≤ n := (ENat.add_le_add_iff_right (ENat.natCast_ne_top _)).mp h4
    exact_mod_cast h5
  have hreg : IsRegularLocalRing (R ⧸ I) := .of_spanFinrank_maximalIdeal_le _ (hfin.trans hdim)
  have heq : ringKrullDim (R ⧸ I) = (s : ℕ) :=
    le_antisymm ((ringKrullDim_le_spanFinrank_maximalIdeal _).trans hfin) hdim
  refine ⟨hreg, ?_, ?_⟩
  · rw [heq, hd, add_comm]
    push_cast
    rfl
  · exact (Ideal.Quotient.isDomain_iff_prime I).1 (GlobalTheory.isDomain_of_isRegularLocalRing _)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CentraliserRank
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.centraliser_rank :
    ∀ {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι] (a : ι → F) (P : Matrix ι ι F), Function.Injective a → P.charpoly = ∏ i, (X - C (a i)) → Module.finrank F (LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P)) = Fintype.card ι ∧ ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q := by
  intro F _ ι _ _ a P ha hP
  have hu : ∀ i j, i ≠ j → IsUnit (a i - a j) := fun i j hij =>
    (sub_ne_zero.2 (fun h => hij (ha h))).isUnit
  have hCH : aeval P (∏ i, (X - C (a i))) = 0 := by
    rw [← hP]; exact Matrix.aeval_self_charpoly P
  obtain ⟨hcoi, -, -, hcomm⟩ := UpperTheory.V.AlgebraTools.lag_coi a P hu hCH
  have hne := UpperTheory.V.AlgebraTools.lag_ne_zero a P hu (by
    rw [hP, Polynomial.map_prod]; simp)
  obtain ⟨g, hg⟩ := UpperTheory.V.AlgebraTools.coi_conj_single _ hcoi hne
  have hpoly : ∀ i, ∃ q : F[X], UpperTheory.V.AlgebraTools.lag a P i = aeval P q := fun i =>
    ⟨_ • _, by rw [UpperTheory.V.AlgebraTools.lag, map_smul]⟩
  set f := UpperTheory.V.AlgebraTools.lag a P with hf
  have hinj : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F) =
      (g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F) → A = B := by
    intro A B h
    exact (Units.mul_right_inj g).1 ((Units.mul_left_inj g⁻¹).1 h)
  have hmul : ∀ A B : Matrix ι ι F, (g : Matrix ι ι F) * (A * B) * ((g⁻¹ : GL ι F) : Matrix ι ι F) =
      ((g : Matrix ι ι F) * A * ((g⁻¹ : GL ι F) : Matrix ι ι F)) *
      ((g : Matrix ι ι F) * B * ((g⁻¹ : GL ι F) : Matrix ι ι F)) := by
    intro A B
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  have hspan : ∀ Y, P * Y = Y * P → ∃ c : ι → F, Y = ∑ i, c i • f i := by
    intro Y hY
    set Z := (g : Matrix ι ι F) * Y * ((g⁻¹ : GL ι F) : Matrix ι ι F) with hZ
    refine ⟨fun i => Z i i, hinj _ _ ?_⟩
    rw [Finset.mul_sum, Finset.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hg]
    rw [← hZ]
    ext i j
    rw [Matrix.sum_apply, Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst hij; simp
      · have h1 : Z * single j j (1 : F) = single j j 1 * Z := by
          rw [← hg j, hZ, ← hmul, ← hmul, (hcomm Y j hY.symm).eq]
        have h2 := congrFun (congrFun h1 i) j
        rw [Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hij] at h2
        rw [mul_one] at h2
        simp [hij, h2]
    · intro b _ hb
      simp [hb]
    · simp
  have hq : ∀ Y, P * Y = Y * P → ∃ q : F[X], Y = aeval P q := by
    intro Y hY
    obtain ⟨c, rfl⟩ := hspan Y hY
    choose q hq using hpoly
    exact ⟨∑ i, c i • q i, by simp [hq]⟩
  refine ⟨?_, hq⟩
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 : (∑ i, c i • f i) * f j = c j • f j := by
      rw [Finset.sum_mul, Finset.sum_eq_single j]
      · rw [smul_mul_assoc, (hcoi.idem j).eq]
      · intro b _ hb
        rw [smul_mul_assoc, hcoi.ortho hb, smul_zero]
      · simp
    rw [hc, zero_mul] at h1
    exact (smul_eq_zero.1 h1.symm).resolve_right (hne j)
  have hker : LinearMap.ker (LinearMap.mulLeft F P - LinearMap.mulRight F P) =
      Submodule.span F (Set.range f) := by
    apply le_antisymm
    · intro Y hY
      have hY' : P * Y = Y * P := by simpa [sub_eq_zero] using hY
      obtain ⟨c, rfl⟩ := hspan Y hY'
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have := (hcomm P i (Commute.refl P)).eq
      simpa [sub_eq_zero] using this
  rw [hker, finrank_span_eq_card hli]
end
