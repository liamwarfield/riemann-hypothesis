module

public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemExtIdSmulIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory

theorem localUnit_div_congr_one {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) (hx : IsUnitAt v x) (y : 𝓞 L)
    (hy : Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y) < 1) :
    y ∉ v.asIdeal ∧ ∃ k : Lˣ, (k : L) = (y : L) ∧
      Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1)
        ≤ WithZero.exp (-1 : ℤ) := by
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := hx
  have hy1 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) y) = 1 := by
    rw [← hx']
    apply Valuation.map_eq_of_sub_lt
    rw [Valuation.map_sub_swap, hx']
    exact hy
  have hy2 : v.valuation L (algebraMap (𝓞 L) L y) = 1 := by
    rw [← ReciprocityTheory.Aut.adic_valued_algebraMap, ← ReciprocityTheory.Aut.adic_algebraMap_R]
    exact hy1
  have hnot : y ∉ v.asIdeal := (HeightOneSpectrum.valuation_eq_one_iff_notMem v).mp hy2
  have hy0 : (y : L) ≠ 0 := by
    intro h
    apply hnot
    have : y = 0 := by exact_mod_cast h
    rw [this]
    exact v.asIdeal.zero_mem
  refine ⟨hnot, Units.mk0 (y : L) hy0, rfl, ?_⟩
  have hk : ((atFin v (Units.mk0 (y : L) hy0) : (v.adicCompletion L)ˣ) : v.adicCompletion L)
      = algebraMap (𝓞 L) (v.adicCompletion L) y := rfl
  have hne : algebraMap (𝓞 L) (v.adicCompletion L) y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy1
    exact zero_ne_one hy1
  have e : ((x * (atFin v (Units.mk0 (y : L) hy0))⁻¹ : (v.adicCompletion L)ˣ) :
      v.adicCompletion L) - 1 = ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y)
        * (algebraMap (𝓞 L) (v.adicCompletion L) y)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, hk, sub_mul, mul_inv_cancel₀ hne]
  rw [e, map_mul, map_inv₀, hy1, inv_one, mul_one]
  generalize Valued.v ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y) = g at hy
  by_cases hg : g = 0
  · rw [hg]; exact zero_le
  · rw [← WithZero.exp_log hg] at hy ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hy
    rw [WithZero.exp_le_exp]
    omega

theorem exists_nat_congr_of_absNorm_prime {L : Type} [Field L] [NumberField L]
    (I : Ideal (𝓞 L)) (hI : I ≠ ⊤) {p : ℕ} (hp : p.Prime) (hN : Ideal.absNorm I = p) (y : 𝓞 L) :
    ∃ a : ℕ, y - (a : 𝓞 L) ∈ I := by
  have := Fact.mk hp
  have hcard : Nat.card (𝓞 L ⧸ I) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 L ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : Nontrivial (𝓞 L ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h := mem_multiples_of_prime_card hcard (g := (1 : 𝓞 L ⧸ I))
    (g' := Ideal.Quotient.mk I y) one_ne_zero
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq, map_natCast, ← ha]
  simp


open Classical in
theorem localUnit_congr_global :
    ∀ (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ), IsUnitAt v x → (∃ (k : Lˣ) (y : 𝓞 L), (k : L) = (y : L) ∧ y ∉ v.asIdeal ∧ Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ)) ∧ ∀ p : ℕ, p.Prime → Ideal.absNorm v.asIdeal = p → ∃ (a : ℕ) (k : Lˣ), a.Coprime p ∧ (k : L) = (a : L) ∧ Valued.v (((x * (atFin v k)⁻¹ : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1) ≤ WithZero.exp (-1 : ℤ) := by
  intro L _ _ v x hx
  obtain ⟨y, hy⟩ := ReciprocityTheory.Aut.adic_exists_approx v (x : v.adicCompletion L) (le_of_eq hx)
  refine ⟨?_, fun p hp hN => ?_⟩
  · obtain ⟨h1, k, hk, h2⟩ := localUnit_div_congr_one v x hx y hy
    exact ⟨k, y, hk, h1, h2⟩
  · obtain ⟨a, ha⟩ := exists_nat_congr_of_absNorm_prime v.asIdeal v.isPrime.ne_top hp hN y
    have hya : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L))) < 1 := by
      have h3 : Valued.v (algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L)))
          = v.valuation L (algebraMap (𝓞 L) L (y - (a : 𝓞 L))) :=
        ReciprocityTheory.Aut.adic_valued_algebraMap v (algebraMap (𝓞 L) L (y - (a : 𝓞 L)))
      rw [h3]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr ha
    have hxa : Valued.v ((x : v.adicCompletion L)
        - algebraMap (𝓞 L) (v.adicCompletion L) (a : 𝓞 L)) < 1 := by
      have e : (x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) (a : 𝓞 L)
          = ((x : v.adicCompletion L) - algebraMap (𝓞 L) (v.adicCompletion L) y)
            + algebraMap (𝓞 L) (v.adicCompletion L) (y - (a : 𝓞 L)) := by
        rw [map_sub]; ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hy hya)
    obtain ⟨h1, k, hk, h2⟩ := localUnit_div_congr_one v x hx (a : 𝓞 L) hxa
    refine ⟨a, k, ?_, by simpa using hk, h2⟩
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    rintro ⟨c, rfl⟩
    apply h1
    have hpm : ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := hN ▸ Ideal.absNorm_mem v.asIdeal
    push_cast
    exact v.asIdeal.mul_mem_right _ hpm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint
open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Pointwise Classical

namespace GlobalTheory.Mem.RowsBundle

theorem exists_conj_involution (I : AutInst) :
    ∃ cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E), (∀ v, cj (cj v) = v) ∧
      (∀ v v', IsConj I v v' ↔ v' = cj v) ∧
      ∀ (m : ℕ) (v : HeightOneSpectrum (𝓞 I.E)), (m : 𝓞 I.E) ∈ v.asIdeal → (m : 𝓞 I.E) ∈ (cj v).asIdeal := by
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hst2 : ∀ a, st (st a) = a := fun a => RingOfIntegers.ext (by rw [hst, hst, star_star])
  have hsurj : Function.Surjective st := fun a => ⟨st a, hst2 a⟩
  let cj : HeightOneSpectrum (𝓞 I.E) → HeightOneSpectrum (𝓞 I.E) := fun v => v.comap st hsurj
  have hcj : ∀ v a, a ∈ (cj v).asIdeal ↔ st a ∈ v.asIdeal := fun v a => Iff.rfl
  refine ⟨cj, fun v => HeightOneSpectrum.ext (Ideal.ext fun a => by rw [hcj, hcj, hst2]), fun v v' => ?_,
    fun m v hv => by rw [hcj, map_natCast]; exact hv⟩
  constructor
  · intro h
    refine HeightOneSpectrum.ext (Ideal.ext fun b => ?_)
    rw [hcj]
    exact (h (st b) b (by rw [hst, star_star])).symm
  · rintro rfl a b hab
    have : b = st a := RingOfIntegers.ext hab
    subst this
    rw [hcj, hst2]

theorem meets_iff_card {X P : Type} (cj : X → X) (hc : ∀ v, cj (cj v) = v) (S : Set X) (hS : ∀ v ∈ S, cj v ∈ S)
    {m : ℕ} (hm : 0 < m) (hcard : S.ncard = 2 * m) (w : P → X) (hw : ∀ v, w v ∈ S) (hinj : Function.Injective w)
    (hn : ∀ v v', w v' ≠ cj (w v)) : (∀ u ∈ S, ∃ v, u = w v ∨ u = cj (w v)) ↔ Nat.card P = m := by
  let f : P ⊕ P → S := Sum.elim (fun v => ⟨w v, hw v⟩) (fun v => ⟨cj (w v), hS _ (hw v)⟩)
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg _ (hinj (congrArg Subtype.val h))
    · exact absurd (congrArg Subtype.val h) (hn _ _)
    · exact absurd (congrArg Subtype.val h).symm (hn _ _)
    · have h' : cj (w a) = cj (w b) := congrArg Subtype.val h
      exact congrArg _ (hinj (by rw [← hc (w a), h', hc]))
  have hS' : Nat.card S = 2 * m := hcard
  haveI : Finite S := Nat.finite_of_card_ne_zero (by omega)
  haveI : Finite P := Finite.of_injective _ (hf.comp Sum.inl_injective)
  have hP : Nat.card (P ⊕ P) = Nat.card P + Nat.card P := Nat.card_sum
  constructor
  · intro h
    have hs : Function.Surjective f := fun u => by
      obtain ⟨v, e | e⟩ := h u.1 u.2
      · exact ⟨Sum.inl v, Subtype.ext e.symm⟩
      · exact ⟨Sum.inr v, Subtype.ext e.symm⟩
    have := Nat.card_eq_of_bijective f ⟨hf, hs⟩
    omega
  · intro h u hu
    have hb := (Nat.bijective_iff_injective_and_card f).2 ⟨hf, by omega⟩
    obtain ⟨v | v, e⟩ := hb.2 ⟨u, hu⟩
    · exact ⟨v, Or.inl (congrArg Subtype.val e).symm⟩
    · exact ⟨v, Or.inr (congrArg Subtype.val e).symm⟩

theorem isChoice_of_card (I : AutInst) (g : Fin 2 → ℕ) (hg : ∀ k, (g k).Prime) (hne : g 0 ≠ g 1)
    (hsp : ∀ k (v : HeightOneSpectrum (𝓞 I.E)), ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal →
      Ideal.absNorm v.asIdeal = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ v.asIdeal ^ 2 ∧ ¬ IsConj I v v)
    {m : ℕ} (hm : 0 < m)
    (hcard : ∀ k, {v : HeightOneSpectrum (𝓞 I.E) | ((g k : ℕ) : 𝓞 I.E) ∈ v.asIdeal}.ncard = 2 * m) :
    (∃ w : ∀ _ : Fin 2, Fin m → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin m) w) ∧
      ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
        (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
        (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  obtain ⟨cj, hc, hconj, hmem⟩ := exists_conj_involution I
  obtain ⟨Pl₀, w₀, -, h₀⟩ := exists_choice I g hg hne hsp
  have key : ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)),
      (∀ k, Fintype.card (Pl k) = m) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) →
      (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
    intro Pl _ w h1 h2 h3 h4
    refine ⟨hg, hne, h₀.2.2.1, fun k v => ⟨h2 k v, (hsp k _ (h2 k v)).1⟩, h3, h4, fun k u hu => ?_⟩
    simp only [hconj] at h4 ⊢
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w k) (h2 k) (h3 k) (h4 k)).2
      (by rw [Nat.card_eq_fintype_card, h1]) u hu
  refine ⟨?_, key⟩
  obtain ⟨-, -, -, h2, h3, h4, h5⟩ := h₀
  have hP : ∀ k, Nat.card (Pl₀ k) = m := fun k => by
    simp only [hconj] at h4 h5
    exact (meets_iff_card cj hc _ (hmem (g k)) hm (hcard k) (w₀ k) (fun v => (h2 k v).1) (h3 k) (h4 k)).1 (h5 k)
  have e : ∀ k, Fin m ≃ Pl₀ k := fun k =>
    haveI : Finite (Pl₀ k) := Nat.finite_of_card_ne_zero (by rw [hP]; omega)
    (Finite.equivFinOfCardEq (hP k)).symm
  exact ⟨fun k v => w₀ k (e k v), key _ _ (fun _ => Fintype.card_fin m) (fun k v => (h2 k _).1)
    (fun k => (h3 k).comp (e k).injective) fun k v v' => h4 k _ _⟩

section Unip

variable {I : AutInst}

theorem hAf_eq_dot (u v : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u v =
    (fun i => sigR I.cm.sig (Af I.F) (u i)) ⬝ᵥ (I.J.map (inclE (F := I.F) (Af I.F)) *ᵥ v) := by
  simp only [hAf, hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hAf_inv_mulVec (x : I.Gf) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x⁻¹ *ᵥ y) z = hAf I y (I.fmat x *ᵥ z) := by
  have hx : cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) * I.J.map (inclE (F := I.F) (Af I.F)) * I.fmat x⁻¹ = _ := x⁻¹.2
  have hs : (fun i => sigR I.cm.sig (Af I.F) ((I.fmat x⁻¹ *ᵥ y) i)) =
      (fun i => sigR I.cm.sig (Af I.F) (y i)) ᵥ* cT (sigR I.cm.sig (Af I.F)) (I.fmat x⁻¹) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, Matrix.vecMul, dotProduct, cT, map_sum, mul_comm]
  have h1 : I.fmat x⁻¹ * I.fmat x = 1 := by rw [← fmat_mul, inv_mul_cancel, fmat_one]
  rw [hAf_eq_dot, hAf_eq_dot, hs, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  conv_rhs => rw [← hx, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem hAf_pow_adjoint (x : I.Gf) (m : ℕ) (y z : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I ((I.fmat x⁻¹ - 1) ^ m *ᵥ y) z = hAf I y ((I.fmat x - 1) ^ m *ᵥ z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← ih, Matrix.sub_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
    generalize (I.fmat x⁻¹ - 1) ^ m *ᵥ y = u
    have h := hAf_inv_mulVec x u z
    simp only [hAf, hform, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib] at h ⊢
    rw [h]

theorem sub_one_pow_mem {x : I.Gf} (hx : x ∈ I.Kset) (m : ℕ) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    (I.fmat x - 1) ^ m *ᵥ y ∈ I.Lf := by
  induction m with
  | zero => simpa using hy
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (mulVec_mem hx ih) ih

end Unip

end GlobalTheory.Mem.RowsBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIso
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIso
noncomputable section

namespace GlobalTheory.SqLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

abbrev sq (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {x : X} {j : L.ι} (h : x ∈ L.U j) : x ∈ (sq L).U (fun _ => j) :=
  Set.mem_iInter.2 fun _ => h

theorem gm_sq_g (f : Y ⟶ X) (y : Y) {j j' : L.ι} (hj : f y ∈ L.U j) (hj' : f y ∈ L.U j') :
    gm f y ((sq L).U (fun _ => j) ⊓ (sq L).U (fun _ => j')) ((sq L).g (fun _ => j) (fun _ => j')) =
      gm f y _ (L.g j j') ^ (2 : ℤ) := by
  refine (gm_linComb L (fun _ => 𝟙 X) (fun _ => 2) f y _ _ (mem_sq hj) (mem_sq hj')).trans ?_
  rw [Fintype.prod_unique, Category.comp_id]

def gq (w : LB.Iso (sq L') ((sq L).pull F)) (f : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι) : (Y.presheaf.stalk y)ˣ :=
  gw w f y (fun _ => j) (fun _ => k)

theorem gq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (f : Y ⟶ X') (y : Y) {j j' : L.ι} {k k' : L'.ι}
    (hj : F (f y) ∈ L.U j) (hj' : F (f y) ∈ L.U j') (hk : f y ∈ L'.U k) (hk' : f y ∈ L'.U k') :
    gq w f y j k = gm (f ≫ F) y _ (L.g j j') ^ (2 : ℤ) * (gm f y _ (L'.g k k') ^ (2 : ℤ))⁻¹ * gq w f y j' k' := by
  rw [gq, gq, hw Y f y _ _ _ _ (mem_sq hj) (mem_sq hj') (mem_sq hk) (mem_sq hk'), gm_sq_g (f ≫ F) y hj hj',
    gm_sq_g f y hk hk']

def pq (w : LB.Iso (sq L') ((sq L).pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (p : K → L.ι)
    (q : K → L'.ι) : (Z.presheaf.stalk z)ˣ := ∏ k, gq w (r ≫ φ' k) z (p k) (q k) ^ ε k

theorem trF_two {M : LB X} (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) (j j' : K → M.ι) :
    trF φ (fun k => 2 * ε k) r z j j' = trF φ ε r z j j' ^ (2 : ℤ) := by
  rw [trF, trF, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_mul, mul_comm]

theorem pq_trans {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (r : Z ⟶ Y)
    (z : Z) {p p' : K → L.ι} {q q' : K → L'.ι} (hp : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p') (hq : r z ∈ LB.wchart L' φ' q) (hq' : r z ∈ LB.wchart L' φ' q') :
    pq w φ' ε r z p q = trF (fun k => φ' k ≫ F) (fun k => 2 * ε k) r z p p' *
      (trF φ' (fun k => 2 * ε k) r z q q')⁻¹ * pq w φ' ε r z p' q' := by
  rw [trF_two, trF_two, pq, pq, trF, trF, ← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gq_trans hw (r ≫ φ' k) z (Set.mem_iInter.1 hp k) (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k)
    (Set.mem_iInter.1 hq' k), Category.assoc]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  rw [smul_add, smul_add, smul_comm (ε k) (2 : ℤ), smul_neg, smul_comm (ε k) (2 : ℤ)]

theorem exists_pq (w : LB.Iso (sq L') ((sq L).pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (p : K → L.ι) (q : K → L'.ι) :
    ∃ u : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q → gm r z _ u = pq w φ' ε r z p q := by
  have le : ∀ k, LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q ≤
      φ' k ⁻¹ᵁ (((sq L).pull F).U (fun _ => fun _ => p k) ⊓ (sq L').U (fun _ => q k)) := fun k y hy =>
    ⟨mem_pull.2 (mem_sq (Set.mem_iInter.1 hy.1 k)), mem_sq (Set.mem_iInter.1 hy.2 k)⟩
  exact ⟨∏ k, res (le k) (pullU (φ' k) _ (w.s (fun _ => fun _ => p k, fun _ => q k))) ^ ε k, fun Z r z hz =>
    (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
      ((gm_res r z (le k) hz _).trans (gm_pull r (φ' k) z _ (le k hz) _))))⟩

theorem exists_sq_up {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
  choose u hu using fun p q => exists_pq w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
    intro p
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ (u p q * res inf_le_right (a.s q) ^ 2) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 :=
      fun Z r z q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (hu p q Z r z hz)
        ((map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hz _))))
    obtain ⟨s, hs⟩ := glue_unit _ (fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_left)
      (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) (fun q => u p q * res inf_le_right (a.s q) ^ 2)
      (fun q q' y hy => by
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, pq_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hL _ _ (𝟙 Y) y hy.1.1, trF_two, gen_trans ha (𝟙 Y) y hy.1.2 hy.2.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
        abel)
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hz s).symm.trans ((congrArg (gm r z _) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (hs j _ (𝟙 Y) y q hj m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hj' m)).symm)
  rw [pq_trans hw φ' ε (𝟙 Y) y hj hj' m m, trF_self hL' _ _ (𝟙 Y) y m, inv_one, _root_.mul_one, _root_.mul_assoc]

theorem exists_sq_gen : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  intro X X' Y L L' F hL hL' w hwg K _ φ' ε a ha
  obtain ⟨t, ht, hv⟩ := exists_sq_up ((isGen_iff w).1 hwg) hL hL' a ha
  refine ⟨t, ht, fun Z z ψ J J' => ∏ k, gq w (ψ k) z (J (ψ k ≫ F)) (J' (ψ k)) ^ ε k, fun Z r z J J' hJ hJ' => ?_⟩
  refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans ?_
  simp only [pq, Category.assoc]
  rfl

end GlobalTheory.SqLB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIsoStatement
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_generator_through_squareIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}, L.IsLB → L'.IsLB →
    ∀ (w : LB.Iso (LB.LinComb L' (K := Fin 1) (fun _ => 𝟙 X') (fun _ => 2))
      ((LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)).pull F)), w.IsGen →
    ∀ {K : Type} [Fintype K] (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∃ W : ∀ (Z : Scheme.{0}) (z : Z), (K → (Z ⟶ X')) → ((Z ⟶ X) → L.ι) → ((Z ⟶ X') → L'.ι) →
          (Z.presheaf.stalk z)ˣ,
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι),
          Good L z J → Good L' z J' → val t r z J = W Z z (fun k => r ≫ φ' k) J J' * val a r z J' ^ 2 := by
  first | exact @GlobalTheory.SqLB.exists_sq_gen | exact GlobalTheory.SqLB.exists_sq_gen | (intros; apply GlobalTheory.SqLB.exists_sq_gen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenExtendDense

open GlobalTheory.GenericExtend GlobalTheory.DvrModel

theorem gm_eq_of_corr {X Y U HU H Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {I : Type} [Fintype I]
    {φ : I → (H ⟶ X)} {ε : I → ℤ} {jH : HU ⟶ H} {e : Y ⟶ H} {j : U ⟶ Y} {eU : U ⟶ HU}
    (heU : eU ≫ jH = j ≫ e)
    {t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)}
    {ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)} (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j))
    (κ : Z ⟶ U) (z : Z) (a : I → L.ι) (ha : e (j (κ z)) ∈ LB.wchart L φ a) :
    gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
      gm (κ ≫ j) z (LB.wchart L (fun i => e ≫ φ i) a) (ρ.s a) := by
  choose Jg hJg using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  have hG : Good L z Jg := hJg
  have hv := val_corr hG hc κ
  rw [val_pull hG, val_pull hG] at hv
  have hw : ∀ k, (κ ≫ eU) ≫ jH ≫ φ k = (κ ≫ j) ≫ e ≫ φ k := fun k => by
    simp only [Category.assoc, reassoc_of% heU]
  let a' : I → L.ι := fun k => Jg ((κ ≫ eU) ≫ jH ≫ φ k)
  have ha' : a' = fun k => Jg ((κ ≫ j) ≫ e ≫ φ k) := funext fun k => congrArg Jg (hw k)
  rw [val_of t (κ ≫ eU) z Jg a' (fun k => rfl),
    val_of ρ (κ ≫ j) z Jg a' (fun k => by rw [ha'])] at hv
  have hpt : jH ((κ ≫ eU) z) = e ((κ ≫ j) z) := by
    rw [← Scheme.Hom.comp_apply, Category.assoc, heU, ← Category.assoc, Scheme.Hom.comp_apply]
  have h1 : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a :=
    (wchart_comp L jH φ a).ge (show jH ((κ ≫ eU) z) ∈ LB.wchart L φ a by rw [hpt]; exact ha)
  have h2 : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a := (wchart_comp L e φ a).ge ha
  have h1' : (κ ≫ eU) z ∈ LB.wchart L (fun i => jH ≫ φ i) a' := hG.mem (fun i => jH ≫ φ i) (κ ≫ eU)
  have h2' : (κ ≫ j) z ∈ LB.wchart L (fun i => e ≫ φ i) a' := by
    rw [ha']; exact hG.mem (fun i => e ≫ φ i) (κ ≫ j)
  have htr : trF (L := L) (fun i => jH ≫ φ i) ε (κ ≫ eU) z a a' =
      trF (L := L) (fun i => e ≫ φ i) ε (κ ≫ j) z a a' := by
    unfold trF
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [hw k]
  rw [gen_trans ht (κ ≫ eU) z h1 h1', gen_trans hρ (κ ≫ j) z h2 h2', htr, hv]

theorem existsUnique_gen_extend : ∀ (Y U H HU X : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (p : H ⟶ Y) (e : Y ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  intro Y U H HU X _ j _ _ _ _ hY p e jH pU eU hsm hgi he hP heU L hL I _ φ ε t ρ ht hρ hc
  haveI := hsm
  haveI := hgi
  have := IsNormalScheme.of_pred hY
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have hN : (LB.LinComb L φ ε).IsLB := LB.isLB_linComb hL φ ε
  let iso := hP.isoPullback
  have hiso : iso.inv ≫ jH = pullback.fst p j := hP.isoPullback_inv_fst
  have hiso' : iso.hom ≫ pullback.fst p j = jH := hP.isoPullback_hom_fst
  have hisoa : ∀ {W : Scheme.{0}} (g : H ⟶ W), iso.inv ≫ jH ≫ g = pullback.fst p j ≫ g := fun g => by
    rw [← Category.assoc, hiso]
  have hpt : ∀ q, jH (iso.inv q) = pullback.fst p j q := fun q => by
    rw [← Scheme.Hom.comp_apply, hiso]
  have hle : ∀ a, pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a ≤
      iso.inv ⁻¹ᵁ LB.wchart L (fun i => jH ≫ φ i) a := fun a q hq =>
    (wchart_comp L jH φ a).ge (show jH (iso.inv q) ∈ LB.wchart L φ a by rw [hpt]; exact hq)
  let τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a)ˣ :=
    fun a => res (hle a) (pullU iso.inv _ (t.s a))
  have hτg : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback p j) (z : Z) (a),
      pullback.fst p j (r z) ∈ (LB.LinComb L φ ε).U a →
      gm r z _ (τ a) = gm (r ≫ iso.inv) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) :=
    fun Z r z a h => (gm_res r z (hle a) h _).trans (gm_pull r iso.inv z _ (hle a h) _)
  have hτ : Compat (LB.LinComb L φ ε) (pullback.fst p j) τ := fun Z r z a b ha hb => by
    have ha' : (r ≫ iso.inv) z ∈ LB.wchart L (fun i => jH ≫ φ i) a := hle a ha
    have hb' : (r ≫ iso.inv) z ∈ LB.wchart L (fun i => jH ≫ φ i) b := hle b hb
    rw [hτg Z r z a ha, hτg Z r z b hb, gen_trans ht (r ≫ iso.inv) z ha' hb']
    refine congrArg (· * _) (Eq.symm ((gm_linComb L φ ε (r ≫ pullback.fst p j) z a b ha hb).trans ?_))
    rw [trF]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Category.assoc, hisoa]
  have hle' : ∀ a, e ⁻¹ᵁ (LB.LinComb L φ ε).U a ≤ LB.wchart L (fun i => e ≫ φ i) a :=
    fun a => (wchart_comp L e φ a).ge
  let ρ' : ∀ a, Γ(Y, e ⁻¹ᵁ (LB.LinComb L φ ε).U a)ˣ := fun a => res (hle' a) (ρ.s a)
  let eU' : U ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 U) (by simp [he])
  have w : eU' ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU' ≫ pullback.snd p j = 𝟙 U := pullback.lift_snd _ _ _
  have hsec : eU ≫ pU = 𝟙 U := by
    rw [← cancel_mono j, Category.id_comp, Category.assoc, ← hP.w, reassoc_of% heU, he,
      Category.comp_id]
  have heU' : eU' ≫ iso.inv = eU := by
    rw [← cancel_mono iso.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply pullback.hom_ext
    · rw [w, Category.assoc, hiso', heU]
    · rw [hπ, Category.assoc, hP.isoPullback_hom_snd, hsec]
  have hτρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : I → L.ι),
      e (j (κ z)) ∈ (LB.LinComb L φ ε).U a →
      gm (κ ≫ eU') z (pullback.fst p j ⁻¹ᵁ (LB.LinComb L φ ε).U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ (LB.LinComb L φ ε).U a) (ρ' a) := by
    intro Z κ z a ha
    have hm : pullback.fst p j ((κ ≫ eU') z) ∈ (LB.LinComb L φ ε).U a := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, w]; exact ha
    have e₁ : gm ((κ ≫ eU') ≫ iso.inv) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) =
        gm (κ ≫ eU) z (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) := by
      rw [Category.assoc, heU']
    exact (hτg Z _ z a hm).trans (e₁.trans ((gm_eq_of_corr hL heU ht hρ hc κ z a ha).trans
      (gm_res (κ ≫ j) z (hle' a) ha _).symm))
  have key : ∀ a, ∀ y ∈ (LB.LinComb L φ ε).U a, Order.coheight y ≤ 1 →
      y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) ((LB.LinComb L φ ε).U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) ((LB.LinComb L φ ε).U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  let σ : ∀ a, Γ(H, (LB.LinComb L φ ε).U a)ˣ := fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩
  have hσ : ∀ a, pullU (pullback.fst p j) _ (σ a) = τ a := fun a ↦ Units.ext (hs a)
  have hgen : (⟨σ⟩ : LB.Gen (LB.LinComb L φ ε)).IsGen := fun a b ↦ Units.map_injective
      (f := ((pullback.fst p j).app ((LB.LinComb L φ ε).U a ⊓ (LB.LinComb L φ ε).U b)).hom.toMonoidHom)
      (hJ _) (by
    change pullU _ _ _ = pullU _ _ _
    refine unit_ext fun q hq ↦ ?_
    have := hτ _ (𝟙 _) q a b hq.1 hq.2
    rw [← hσ, ← hσ, gm_pull _ _ q _ hq.1, gm_pull _ _ q _ hq.2] at this
    rw [gm_pull _ _ q _ hq, gm_pull _ _ q _ hq, map_mul, gm_res _ q _ hq, gm_res _ q _ hq]
    exact this)
  have hτc : ∀ c : LB.Gen (LB.LinComb L φ ε), LB.pullGen L _ _ c jH = t → ∀ a,
      pullU (pullback.fst p j) _ (c.s a) = τ a := by
    rintro c rfl a
    refine unit_ext fun q hq ↦ ?_
    rw [gm_pull _ _ q _ hq, hτg _ (𝟙 _) q a hq]
    simp only [Category.id_comp]
    dsimp only [LB.pullGen]
    have h₁ : iso.inv q ∈ LB.wchart L (fun i => jH ≫ φ i) a := hle a hq
    have h₂ : jH (iso.inv q) ∈ LB.wchart L φ a := by rw [hpt]; exact hq
    exact ((gm_res iso.inv q _ h₁ _).trans ((gm_pull iso.inv jH q _ h₂ _).trans (congrArg (fun f => gm f q _ (c.s a)) hiso))).symm
  have hpg : LB.pullGen L _ _ (⟨σ⟩ : LB.Gen (LB.LinComb L φ ε)) jH = t := by
    refine congrArg LB.Gen.mk (funext fun a ↦ unit_ext fun y hy ↦ ?_)
    have hy' : jH y ∈ (LB.LinComb L φ ε).U a := (wchart_comp L jH φ a).le hy
    have h' : pullback.fst p j (iso.hom y) ∈ (LB.LinComb L φ ε).U a := by
      rw [← Scheme.Hom.comp_apply, hiso']; exact hy'
    have e₁ : gm jH y ((LB.LinComb L φ ε).U a) (σ a) =
        gm (𝟙 HU) y (LB.wchart L (fun i => jH ≫ φ i) a) (t.s a) := by
      refine (congrArg (fun f => gm f y ((LB.LinComb L φ ε).U a) (σ a)) hiso'.symm).trans
        ((gm_pull iso.hom _ y _ h' _).symm.trans ?_)
      rw [hσ]
      exact (hτg _ iso.hom y a h').trans (by rw [Iso.hom_inv_id])
    refine Eq.trans ?_ e₁
    dsimp only [LB.pullGen]
    rw [gm_res _ y _ hy, gm_pull _ _ y _ hy', Category.id_comp]
  refine ⟨⟨σ⟩, ⟨hgen, hpg⟩, ?_⟩
  rintro ⟨c⟩ ⟨-, hc'⟩
  refine congrArg LB.Gen.mk (funext fun a ↦ Units.map_injective
    (f := ((pullback.fst p j).app ((LB.LinComb L φ ε).U a)).hom.toMonoidHom) (hJ _) ?_)
  exact (hτc ⟨c⟩ hc' a).trans (hσ a).symm

end GlobalTheory.GenExtendDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueGeneratorExtendDenseProOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_generator_extend_dense_proOpen : ∀ (Y U H HU X : Scheme.{0}) [IsLocallyNoetherian Y] (j : U ⟶ Y) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j], Geo.Tor.IsNormalScheme Y → ∀ (p : H ⟶ Y) (e : Y ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  first | exact @GlobalTheory.GenExtendDense.existsUnique_gen_extend | exact GlobalTheory.GenExtendDense.existsUnique_gen_extend | (intros; apply GlobalTheory.GenExtendDense.existsUnique_gen_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflatten
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflatten
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecPowUnflat

theorem unflat : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  intro X Y L a n m hm g s'
  have le : ∀ J : Fin 1 → (Fin 1 → L.ι),
      LB.wchart (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (fun _ : Fin 1 => g) J ≤
        LB.wchart L (fun _ : Fin 1 => g) (fun k => J k 0) := fun J y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0
  refine ⟨⟨fun J => (Y.presheaf.map (homOfLE (le J)).op).hom (s'.f (fun k => J k 0)), fun J J' => ?_⟩, ?_⟩
  · refine fn_ext fun y hy => ?_
    have hy1 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) := le J hy.1
    have hy2 : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := le J' hy.2
    have hS : y ∈ (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J k 0) ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m)).U (fun k => J' k 0) := ⟨hy1, hy2⟩
    have c := congrArg (gs (𝟙 Y) y _) (s'.compat (fun k => J k 0) (fun k => J' k 0))
    rw [gs_res (𝟙 Y) y _ hS, gs_mul (𝟙 Y) y _ hS, gs_unit (𝟙 Y) y _ hS, gs_res (𝟙 Y) y _ hS] at c
    erw [gm_linComb L _ _ (𝟙 Y) y _ _ hy1 hy2] at c
    erw [gs_res (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy.1, gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, gs_res (𝟙 Y) y _ hy,
      gs_res (𝟙 Y) y _ hy.2, c]
    erw [gm_linComb _ _ _ (𝟙 Y) y J J' hy.1 hy.2]
    have i1 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J 0) := by
      simpa using Set.mem_iInter.1 hy.1 0
    have i2 : (𝟙 Y ≫ g) y ∈ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)).U (J' 0) := by
      simpa using Set.mem_iInter.1 hy.2 0
    simp only [Fin.prod_univ_one]
    erw [gm_linComb L _ _ (𝟙 Y ≫ g) y (J 0) (J' 0) i1 i2]
    simp only [Fin.prod_univ_one, Category.comp_id, Category.id_comp, hm, zpow_mul]
    rfl
  · intro Z r z j h
    exact (gs_res r z (le _) (Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun _ => h) _).symm

end GlobalTheory.SecPowUnflat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinCombPowSectionUnflattenStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linComb_pow_section_unflatten : ∀ {X Y : Scheme.{0}} (L : LB X) (a n m : ℤ), m = a * n → ∀ (g : Y ⟶ X) (s' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => g) (fun _ => m))), ∃ s : LB.Sec (LB.LinComb (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => a)) (K := Fin 1) (fun _ => g) (fun _ => n)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : L.ι), g (r z) ∈ L.U j → gs r z _ (s'.f fun _ => j) = gs r z _ (s.f fun _ => fun _ => j) := by
  first | exact @GlobalTheory.SecPowUnflat.unflat | exact GlobalTheory.SecPowUnflat.unflat | (intros; apply GlobalTheory.SecPowUnflat.unflat <;> assumption)
end
end
