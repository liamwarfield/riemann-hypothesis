module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqJet
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet

open MvPolynomial Formalism.L2.Pj

variable {R : Type} [CommRing R]

abbrev zz {κ : Type} (m : ℕ) (j : κ) : Jet R κ m := Ideal.Quotient.mk _ (X j)


variable (R) in
def Ij (κ : Type) (m : ℕ) : Ideal (Jet R κ m) := Ideal.span (Set.range (zz (R := R) (κ := κ) m))

theorem Ij_eq_map (κ : Type) (m : ℕ) :
    Ij R κ m = (orig R κ).map (Ideal.Quotient.mk (orig R κ ^ (m + 1))) := by
  unfold Ij orig
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem Ij_pow_eq_bot (κ : Type) (m : ℕ) : Ij R κ m ^ (m + 1) = ⊥ := by
  rw [Ij_eq_map, ← Ideal.map_pow, Ideal.map_quotient_self]

theorem eq_zero_of_mem_pow {κ : Type} {m k : ℕ} (hk : m + 1 ≤ k) {p : Jet R κ m} (hp : p ∈ Ij R κ m ^ k) :
    p = 0 := by
  have h := Ideal.pow_le_pow_right hk hp
  rw [Ij_pow_eq_bot] at h
  exact (Submodule.mem_bot _).1 h

theorem jetMap_alt_alt {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R) (hφ : ∀ i, φ i ∈ orig R κ') (j : κ) :
    jetMap (m := m) φ hφ (zz m j) = Ideal.Quotient.mk _ (φ j) := by
  simp only [jetMap, liftJet, Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  simp

theorem mem_pow_of_trunc_eq_zero {κ : Type} {m : ℕ} (p : Jet R κ (m + 1))
    (h : (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) p = 0) : p ∈ Ij R κ (m + 1) ^ (m + 1) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
  have hP : P ∈ orig R κ ^ (m + 1) := by
    have e : (jetTrunc : Jet R κ (m + 1) →ₐ[R] Jet R κ m) (Ideal.Quotient.mk _ P) =
        Ideal.Quotient.mk _ P := by
      first
      | rfl
      | simp [jetTrunc]
    rw [e, Ideal.Quotient.eq_zero_iff_mem] at h
    exact h
  rw [Ij_eq_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hP

theorem augmentation_jet_variable {κ : Type} (m : ℕ) (j : κ) : (jetAug : Jet R κ m →ₐ[R] R) (zz m j) = 0 := by
  simp [jetAug, liftJet, zz]

theorem jet_ext' {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A] {f g : Jet R κ m →ₐ[R] A}
    (h : ∀ j, f (zz m j) = g (zz m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j

theorem sub_aug_mem {κ : Type} {m : ℕ} (p : Jet R κ m) :
    p - algebraMap R _ ((jetAug : Jet R κ m →ₐ[R] R) p) ∈ Ij R κ m := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
  induction P using MvPolynomial.induction_on
  next a =>
    have e : (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (C a) : Jet R κ m) = algebraMap R _ a := rfl
    rw [e, AlgHom.commutes]
    simp
  next q r hq hr =>
    have h := Ideal.add_mem _ hq hr
    convert h using 1
    simp only [map_add (f := _)]
    abel
  next q j _ =>
    have hz : (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (X j) : Jet R κ m) ∈ Ij R κ m :=
      Ideal.subset_span ⟨j, rfl⟩
    have h0 : (jetAug : Jet R κ m →ₐ[R] R) (Ideal.Quotient.mk (orig R κ ^ (m + 1)) (X j)) = 0 :=
      augmentation_jet_variable m j
    rw [map_mul, map_mul, h0, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ hz

theorem map_pow_mem {κ κ' : Type} {m m' : ℕ} (f : Jet R κ m →ₐ[R] Jet R κ' m')
    (hf : ∀ j, f (zz m j) ∈ Ij R κ' m') (k : ℕ) {p : Jet R κ m} (hp : p ∈ Ij R κ m ^ k) :
    f p ∈ Ij R κ' m' ^ k := by
  have h1 : Ideal.map f (Ij R κ m) ≤ Ij R κ' m' := by
    rw [Ij, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact hf j
  have h2 : Ideal.map f (Ij R κ m ^ k) ≤ Ij R κ' m' ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h1 k
  exact h2 (Ideal.mem_map_of_mem f hp)

section Scale

abbrev sc {κ : Type} (m : ℕ) (c : R) : Jet R κ m →ₐ[R] Jet R κ m := jetScale (fun _ => c)

theorem scale_jet_variable {κ : Type} (m : ℕ) (c : R) (j : κ) : sc m c (zz m j) = c • zz m j := by
  simp only [sc, jetScale]
  rw [jetMap_alt_alt, map_mul, Algebra.smul_def]
  rfl

theorem aug_sc {κ : Type} (m : ℕ) (c : R) (p : Jet R κ m) :
    (jetAug : Jet R κ m →ₐ[R] R) (sc m c p) = (jetAug : Jet R κ m →ₐ[R] R) p := by
  have h : (jetAug : Jet R κ m →ₐ[R] R).comp (sc m c) = jetAug := by
    apply jet_ext'
    intro j
    rw [AlgHom.comp_apply, scale_jet_variable, map_smul, augmentation_jet_variable, smul_zero]
  exact congrArg (fun g : Jet R κ m →ₐ[R] R => g p) h

theorem sc_sub_mem {κ : Type} (m : ℕ) (c : R) (p : Jet R κ m) : sc m c p - p ∈ Ij R κ m := by
  have h1 := sub_aug_mem (sc m c p)
  have h2 := sub_aug_mem p
  rw [aug_sc] at h1
  have h3 := Ideal.sub_mem _ h1 h2
  rwa [sub_sub_sub_cancel_right] at h3

theorem sc_one_mem {κ : Type} (m : ℕ) (c : R) {b : Jet R κ m} (hb : b ∈ Ij R κ m) :
    sc m c b - c • b ∈ Ij R κ m ^ 2 := by
  have hb' : b ∈ Submodule.span (Jet R κ m) (Set.range (zz (R := R) (κ := κ) m)) := hb
  clear hb
  induction hb' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [scale_jet_variable, sub_self]
    exact Ideal.zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    have h := Ideal.add_mem _ hx hy
    convert h using 1
    rw [map_add (f := _), smul_add]
    abel
  | smul a x hx' hx =>
    have e1 : sc m c (a • x) - c • (a • x) =
        sc m c a * (sc m c x - c • x) + (sc m c a - a) * (c • x) := by
      simp only [smul_eq_mul, map_mul, Algebra.smul_def]
      ring
    rw [e1]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx) ?_
    rw [pow_two (Ij R κ m)]
    exact Ideal.mul_mem_mul (sc_sub_mem m c a) (Submodule.smul_of_tower_mem _ c hx')

theorem sc_pow_mem {κ : Type} (m : ℕ) (c : R) :
    ∀ (k : ℕ) {p : Jet R κ m}, p ∈ Ij R κ m ^ k → sc m c p - c ^ k • p ∈ Ij R κ m ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro p _
    simpa using sc_sub_mem m c p
  | succ k ih =>
    intro p hp
    rw [pow_succ (Ij R κ m) k] at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro a ha b hb
      have hsb : sc m c b ∈ Ij R κ m := by
        have h := Ideal.add_mem _ (sc_sub_mem m c b) hb
        simpa using h
      have e : sc m c (a * b) - c ^ (k + 1) • (a * b) =
          (sc m c a - c ^ k • a) * sc m c b + (c ^ k • a) * (sc m c b - c • b) := by
        simp only [map_mul, Algebra.smul_def, map_pow]
        ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ (Ij R κ m) (k + 1)]
        exact Ideal.mul_mem_mul (ih ha) hsb
      · have h2 := sc_one_mem m c hb
        have h3 : c ^ k • a ∈ Ij R κ m ^ k := Submodule.smul_of_tower_mem _ _ ha
        rw [show k + 1 + 1 = k + 2 by ring, pow_add (Ij R κ m) k 2]
        exact Ideal.mul_mem_mul h3 h2
    · intro x y hx hy
      have h := Ideal.add_mem _ hx hy
      convert h using 1
      rw [map_add (f := _), smul_add]
      abel

end Scale

section Kill

variable {n : ℕ}

def killS (i : Fin 2) (v : Fin 2 × Fin n) : MvPolynomial (Fin 2 × Fin n) R := if v.1 = i then 0 else X v

theorem killS_mem (i : Fin 2) (v : Fin 2 × Fin n) : killS (R := R) i v ∈ orig R (Fin 2 × Fin n) := by
  unfold killS
  split_ifs
  · exact Ideal.zero_mem _
  · exact X_mem_orig v

def kill (m : ℕ) (i : Fin 2) : Jet R (Fin 2 × Fin n) m →ₐ[R] Jet R (Fin 2 × Fin n) m :=
  jetMap (killS i) (killS_mem i)

def Kp (m : ℕ) (i : Fin 2) : Ideal (Jet R (Fin 2 × Fin n) m) :=
  Ideal.span (Set.range fun j : Fin n => zz (R := R) m (i, j))

theorem kill_alt_alt (m : ℕ) (i : Fin 2) (v : Fin 2 × Fin n) :
    kill (R := R) m i (zz m v) = if v.1 = i then 0 else zz m v := by
  rw [kill, jetMap_alt_alt, killS]
  split_ifs <;> simp [zz]

theorem poly_sub_kill_mem (i : Fin 2) (P : MvPolynomial (Fin 2 × Fin n) R) :
    P - aeval (killS i) P ∈ Ideal.span (Set.range fun j : Fin n => (X (i, j) : MvPolynomial (Fin 2 × Fin n) R)) := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp
  next p q hp hq =>
    rw [map_add (f := _), add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  next p v hp =>
    rw [map_mul, aeval_X]
    have e : p * X v - aeval (killS i) p * killS i v =
        (p - aeval (killS i) p) * X v + aeval (killS i) p * (X v - killS i v) := by ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    rcases v with ⟨a, b⟩
    unfold killS
    split_ifs with hv
    · have ha : a = i := hv
      subst ha
      rw [sub_zero]
      exact Ideal.subset_span ⟨b, rfl⟩
    · rw [sub_self]
      exact Ideal.zero_mem _

theorem sub_kill_mem (m : ℕ) (i : Fin 2) (e : Jet R (Fin 2 × Fin n) m) : e - kill m i e ∈ Kp m i := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective e
  have h1 : kill m i (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (aeval (killS i) P) := by
    simp only [kill, jetMap, liftJet, Ideal.Quotient.liftₐ_apply]
    erw [Ideal.Quotient.lift_mk]
  rw [h1, ← map_sub]
  have h2 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (orig R (Fin 2 × Fin n) ^ (m + 1)))
    (poly_sub_kill_mem i P)
  rw [Ideal.map_span, ← Set.range_comp] at h2
  exact h2

theorem mem_mul_of_kill (m : ℕ) (e : Jet R (Fin 2 × Fin n) m) (h0 : kill m 0 e = 0) (h1 : kill m 1 e = 0) :
    e ∈ Kp m 0 * Kp m 1 := by
  have key : ∀ x ∈ Kp (R := R) (n := n) m 0, x - kill m 1 x ∈ Kp m 0 * Kp m 1 := by
    intro x hx
    have hx' : x ∈ Submodule.span (Jet R (Fin 2 × Fin n) m)
        (Set.range fun j : Fin n => zz (R := R) m ((0 : Fin 2), j)) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [kill_alt_alt, if_neg (by simp), sub_self]
      exact Ideal.zero_mem _
    | zero => simp
    | add y z _ _ hy hz =>
      have h := Ideal.add_mem _ hy hz
      convert h using 1
      rw [map_add (f := _)]
      abel
    | smul a y hy' hy =>
      have e1 : a • y - kill m 1 (a • y) = y * (a - kill m 1 a) + kill m 1 a * (y - kill m 1 y) := by
        rw [smul_eq_mul, map_mul]
        ring
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_mul hy' (sub_kill_mem m 1 a)) (Ideal.mul_mem_left _ _ hy)
  have he0 : e ∈ Kp m 0 := by simpa [h0] using sub_kill_mem m 0 e
  simpa [h1] using key e he0

end Kill

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR IsUnivChart sp spMap spMap_comp comp_one')

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

section Maps

variable (d : ℕ)

abbrev sumJ (M : ℕ) : Jet R (Fin 1 × Fin d) M →ₐ[R] Jet R (Fin 2 × Fin d) M :=
  jetSubstP M fun p : Fin 1 × Fin d => (X ((0 : Fin 2), p.2) + X ((1 : Fin 2), p.2) : MvPolynomial (Fin 2 × Fin d) R)

abbrev cpy (M : ℕ) (i : Fin 2) : Jet R (Fin 1 × Fin d) M →ₐ[R] Jet R (Fin 2 × Fin d) M := jetCopy d M i

def diag (M : ℕ) : Jet R (Fin 2 × Fin d) M →ₐ[R] Jet R (Fin 1 × Fin d) M :=
  jetMap (fun q : Fin 2 × Fin d => (X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin d) R)) fun _ => X_mem_orig _

theorem sumJ_alt (M : ℕ) (p : Fin 1 × Fin d) :
    sumJ (R := R) d M (zz M p) = zz M ((0 : Fin 2), p.2) + zz M ((1 : Fin 2), p.2) := by
  rw [sumJ, jetSubstP, jetMap_alt_alt]
  simp only [map_add (f := _), MvPolynomial.constantCoeff_X, add_zero, map_zero, sub_zero]

theorem diag_alt_alt (M : ℕ) (q : Fin 2 × Fin d) : diag (R := R) d M (zz M q) = zz M ((0 : Fin 1), q.2) := by
  rw [diag, jetMap_alt_alt]

theorem copy_jet_variable (M : ℕ) (i : Fin 2) (p : Fin 1 × Fin d) : cpy (R := R) d M i (zz M p) = zz M (i, p.2) := by
  rw [cpy, jetCopy, jetMap_alt_alt]

theorem fin_one_pair_eq_local (p : Fin 1 × Fin d) : ((0 : Fin 1), p.2) = p := Prod.ext (Subsingleton.elim _ _) rfl

theorem diag_cpy_apply (M : ℕ) (i : Fin 2) (a : Jet R (Fin 1 × Fin d) M) : diag d M (cpy d M i a) = a := by
  have : (diag (R := R) d M).comp (cpy d M i) = AlgHom.id R _ :=
    jet_ext' fun p => by rw [AlgHom.comp_apply, copy_jet_variable, diag_alt_alt, fin_one_pair_eq_local]; rfl
  exact DFunLike.congr_fun this a

theorem diag_sum_apply (M : ℕ) (a : Jet R (Fin 1 × Fin d) M) : diag d M (sumJ d M a) = sc M 2 a := by
  have : (diag (R := R) d M).comp (sumJ d M) = sc M 2 :=
    jet_ext' fun p => by rw [AlgHom.comp_apply, sumJ_alt, map_add (f := _), diag_alt_alt, diag_alt_alt, scale_jet_variable, fin_one_pair_eq_local, two_smul]
  exact DFunLike.congr_fun this a

theorem aug_comp_sum (M : ℕ) : (jetAug : Jet R (Fin 2 × Fin d) M →ₐ[R] R).comp (sumJ d M) = jetAug :=
  jet_ext' fun p => by rw [AlgHom.comp_apply, sumJ_alt, map_add (f := _), augmentation_jet_variable, augmentation_jet_variable, augmentation_jet_variable, add_zero]

theorem aug_comp_cpy (M : ℕ) (i : Fin 2) : (jetAug : Jet R (Fin 2 × Fin d) M →ₐ[R] R).comp (cpy d M i) = jetAug :=
  jet_ext' fun p => by rw [AlgHom.comp_apply, copy_jet_variable, augmentation_jet_variable, augmentation_jet_variable]

end Maps

theorem aug_comp_trunc {κ : Type} (M : ℕ) :
    (jetAug : Jet R κ M →ₐ[R] R).comp (jetTrunc : Jet R κ (M + 1) →ₐ[R] Jet R κ M) = jetAug :=
  jet_ext' fun j => by
    show (jetAug : Jet R κ M →ₐ[R] R) (zz M j) = (jetAug : Jet R κ (M + 1) →ₐ[R] R) (zz (M + 1) j)
    rw [augmentation_jet_variable, augmentation_jet_variable]

theorem ker_aug_le {κ : Type} (m : ℕ) : RingHom.ker (jetAug : Jet R κ m →ₐ[R] R) ≤ Ij R κ m := by
  intro p hp
  have h := sub_aug_mem p
  rw [RingHom.mem_ker.1 hp, map_zero, sub_zero] at h
  exact h

theorem ker_aug_pow {κ : Type} {m k : ℕ} (hk : m + 1 ≤ k) : RingHom.ker (jetAug : Jet R κ m →ₐ[R] R) ^ k = ⊥ := by
  rw [← le_bot_iff, ← Ij_pow_eq_bot (R := R) κ m]
  exact (Ideal.pow_right_mono (ker_aug_le m) k).trans (Ideal.pow_le_pow_right hk)

variable {n : ℕ}

def cpyU (M : ℕ) (i : Fin 2) : JetR R (Fin n) M →ₐ[R] Jet R (Fin 2 × Fin n) M :=
  ReciprocityTheory.ChartRestriction.G.Chart.jetLift R (Ij R (Fin 2 × Fin n) M) (Ij_pow_eq_bot _ M) (fun j => zz M (i, j))
    (fun j => Ideal.subset_span ⟨(i, j), rfl⟩)

theorem cpyU_zR (M : ℕ) (i : Fin 2) (j : Fin n) : cpyU (R := R) M i (zR M j) = zz M (i, j) :=
  ReciprocityTheory.ChartRestriction.G.Chart.jetLift_zR _ _ _ _ j

section Univ

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G}
  (hx : IsUnivChart G n x)
include hx

theorem augOne (m : ℕ) : spMap (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) m) ≫ x m = 1 := by
  rw [ReciprocityTheory.ChartRestriction.G.Chart.jetAug_eq_comp (Fin n) m, ← spMap_comp, Category.assoc, hx.2.1 m, comp_one']

theorem one_eq {A : Type} [CommRing A] [Algebra R A] (m : ℕ) :
    spMap ((Algebra.ofId R A).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) m)) ≫ x m = 1 := by
  rw [← spMap_comp, Category.assoc, augOne hx, comp_one']

theorem uniq {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ) (hk : RingHom.ker aug ^ (m + 1) = ⊥)
    {ψ₁ ψ₂ : JetR R (Fin n) m →ₐ[R] A} (h1 : aug.comp ψ₁ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) m)
    (h2 : aug.comp ψ₂ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) m) (e : spMap ψ₁ ≫ x m = spMap ψ₂ ≫ x m) :
    ψ₁ = ψ₂ := by
  have hy : spMap aug ≫ (spMap ψ₁ ≫ x m) = 1 := by
    rw [← Category.assoc, spMap_comp, h1, augOne hx]
  exact (hx.2.2 A aug m hk _ hy).unique ⟨h1, rfl⟩ ⟨h2, e⟩

theorem coord {A : Type} [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ) (hk : RingHom.ker aug ^ (m + 1) = ⊥)
    (y : sp (R₀ := R) A ⟶ G) (hy : spMap aug ≫ y = 1) :
    ∃ ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) m ∧ y = spMap ψ ≫ x m :=
  (hx.2.2 A aug m hk y hy).exists

theorem aug_cpyU (M : ℕ) (i : Fin 2) :
    (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R).comp (cpyU M i) = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M :=
  ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, cpyU_zR, augmentation_jet_variable, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR]

omit hx in
theorem aug_kill (M : ℕ) (i : Fin 2) :
    (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R).comp (kill M i) = jetAug :=
  jet_ext' fun v => by
    rw [AlgHom.comp_apply, kill_alt_alt]
    split_ifs
    · rw [map_zero, augmentation_jet_variable]
    · rfl

theorem law (M : ℕ) : ∃ Φ : JetR R (Fin n) M →ₐ[R] Jet R (Fin 2 × Fin n) M,
    (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R).comp Φ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M ∧
    (spMap (cpyU M 0) ≫ x M) * (spMap (cpyU M 1) ≫ x M) = spMap Φ ≫ x M ∧
    ∀ j, Φ (zR M j) - zz M ((0 : Fin 2), j) - zz M ((1 : Fin 2), j) ∈ Kp M 0 * Kp M 1 := by
  have hkk : RingHom.ker (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R) ^ (M + 1) = ⊥ := ker_aug_pow le_rfl
  have hone : ∀ i, spMap (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R) ≫ (spMap (cpyU M i) ≫ x M) = 1 := fun i => by
    rw [← Category.assoc, spMap_comp, aug_cpyU hx, augOne hx]
  have hP : spMap (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R) ≫
      ((spMap (cpyU M 0) ≫ x M) * (spMap (cpyU M 1) ≫ x M)) = 1 := by
    rw [MonObj.comp_mul, hone, hone, _root_.mul_one]
  obtain ⟨Φ, hΦa, hΦ⟩ := coord hx _ M hkk _ hP
  have e0 : (kill M 1).comp (cpyU M 0) = cpyU (R := R) (n := n) M 0 := ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, cpyU_zR, kill_alt_alt, if_neg (by simp)]
  have e1 : (kill M 0).comp (cpyU M 1) = cpyU (R := R) (n := n) M 1 := ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
    rw [AlgHom.comp_apply, cpyU_zR, kill_alt_alt, if_neg (by simp)]
  have z0 : ∀ i : Fin 2, (kill (R := R) (n := n) M i).comp (cpyU (R := R) (n := n) M i) =
      (Algebra.ofId R _).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M) := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
      rw [AlgHom.comp_apply, cpyU_zR, kill_alt_alt, if_pos rfl, AlgHom.comp_apply, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR, map_zero]
  have hk : ∀ i i' : Fin 2, (kill (R := R) (n := n) M i).comp (cpyU (R := R) (n := n) M i') = cpyU M i' →
      spMap (kill (R := R) (n := n) M i) ≫ ((spMap (cpyU (R := R) (n := n) M 0) ≫ x M) *
        (spMap (cpyU (R := R) (n := n) M 1) ≫ x M)) = spMap (cpyU (R := R) (n := n) M i') ≫ x M →
      (kill (R := R) (n := n) M i).comp Φ = cpyU M i' := by
    intro i i' _ hprod
    refine uniq hx (jetAug : Jet R (Fin 2 × Fin n) M →ₐ[R] R) M hkk ?_ (aug_cpyU hx M i') ?_
    · rw [← AlgHom.comp_assoc, aug_kill, hΦa]
    · rw [← spMap_comp, Category.assoc, ← hΦ, hprod]
  have k1 : (kill M 1).comp Φ = cpyU M 0 := hk 1 0 e0 (by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, e0, z0, one_eq hx, _root_.mul_one])
  have k0 : (kill M 0).comp Φ = cpyU M 1 := hk 0 1 e1 (by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spMap_comp, spMap_comp, e1, z0, one_eq hx, _root_.one_mul])
  refine ⟨Φ, hΦa, hΦ, fun j => mem_mul_of_kill M _ ?_ ?_⟩
  · have h := DFunLike.congr_fun k0 (zR M j)
    rw [AlgHom.comp_apply, cpyU_zR] at h
    rw [map_sub, map_sub, h, kill_alt_alt, kill_alt_alt, if_pos rfl, if_neg (by simp), sub_zero, sub_self]
  · have h := DFunLike.congr_fun k1 (zR M j)
    rw [AlgHom.comp_apply, cpyU_zR] at h
    rw [map_sub, map_sub, h, kill_alt_alt, kill_alt_alt, if_neg (by simp), if_pos rfl, sub_zero, sub_self]

theorem top_step [Algebra ℚ R] {d M : ℕ} (hM : 2 ≤ M) (ψ : JetR R (Fin n) M →ₐ[R] Jet R (Fin 1 × Fin d) M)
    (hψa : (jetAug : Jet R (Fin 1 × Fin d) M →ₐ[R] R).comp ψ = ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) M)
    (hψ : ∀ j, ψ (zR M j) ∈ Ij R (Fin 1 × Fin d) M ^ M)
    (hhom : spMap (sumJ d M) ≫ (spMap ψ ≫ x M) =
      (spMap (cpy d M 0) ≫ spMap ψ ≫ x M) * (spMap (cpy d M 1) ≫ spMap ψ ≫ x M)) :
    ∀ j, ψ (zR M j) = 0 := by
  obtain ⟨Φ, hΦa, hΦ, hE⟩ := law hx M
  have hb : ∀ v : Fin 2 × Fin n, cpy d M v.1 (ψ (zR M v.2)) ∈ Ij R (Fin 2 × Fin d) M ^ M := fun v =>
    map_pow_mem _ (fun p => by rw [copy_jet_variable]; exact Ideal.subset_span ⟨_, rfl⟩) M (hψ v.2)
  obtain ⟨ev, hev⟩ : ∃ ev : Jet R (Fin 2 × Fin n) M →ₐ[R] Jet R (Fin 2 × Fin d) M,
      ∀ v, ev (zz M v) = cpy d M v.1 (ψ (zR M v.2)) := by
    refine ⟨liftJet (aeval fun v : Fin 2 × Fin n => cpy d M v.1 (ψ (zR M v.2))) ?_, fun v => ?_⟩
    · rw [← le_bot_iff, ← Ij_pow_eq_bot (R := R) (Fin 2 × Fin d) M]
      refine Ideal.pow_right_mono ?_ _
      rw [Ideal.span_le]
      rintro _ ⟨v, rfl⟩
      simp only [SetLike.mem_coe, aeval_X]
      exact Ideal.pow_le_self (by omega) (hb v)
    · show aeval _ (X v) = _
      rw [aeval_X]
  have ev_cpy : ∀ i, ev.comp (cpyU M i) = (cpy d M i).comp ψ := fun i =>
    ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by rw [AlgHom.comp_apply, cpyU_zR, hev, AlgHom.comp_apply]
  have haug2 : (jetAug : Jet R (Fin 2 × Fin d) M →ₐ[R] R).comp ev = jetAug := jet_ext' fun v => by
    have h1 := DFunLike.congr_fun (aug_comp_cpy (R := R) d M v.1) (ψ (zR M v.2))
    have h2 := DFunLike.congr_fun hψa (zR M v.2)
    rw [AlgHom.comp_apply] at h1 h2
    rw [AlgHom.comp_apply, hev, augmentation_jet_variable, h1, h2, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR]
  have hsum : (sumJ d M).comp ψ = ev.comp Φ := by
    refine uniq hx (jetAug : Jet R (Fin 2 × Fin d) M →ₐ[R] R) M (ker_aug_pow le_rfl) ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, aug_comp_sum, hψa]
    · rw [← AlgHom.comp_assoc, haug2, hΦa]
    · calc spMap ((sumJ d M).comp ψ) ≫ x M = spMap (sumJ d M) ≫ (spMap ψ ≫ x M) := by
            rw [← spMap_comp, Category.assoc]
        _ = (spMap ((cpy d M 0).comp ψ) ≫ x M) * (spMap ((cpy d M 1).comp ψ) ≫ x M) := by
            rw [hhom, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc]
        _ = (spMap (ev.comp (cpyU M 0)) ≫ x M) * (spMap (ev.comp (cpyU M 1)) ≫ x M) := by
            rw [ev_cpy, ev_cpy]
        _ = spMap ev ≫ ((spMap (cpyU M 0) ≫ x M) * (spMap (cpyU M 1) ≫ x M)) := by
            rw [MonObj.comp_mul, ← spMap_comp, ← spMap_comp, Category.assoc, Category.assoc]
        _ = spMap (ev.comp Φ) ≫ x M := by rw [hΦ, ← spMap_comp, Category.assoc]
  intro j
  have hmap : ∀ i, Ideal.map ev (Kp M i) ≤ Ij R (Fin 2 × Fin d) M ^ M := fun i => by
    rw [Kp, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j', rfl⟩, rfl⟩
    rw [SetLike.mem_coe, hev]
    exact hb (i, j')
  have hevE : ev (Φ (zR M j) - zz M ((0 : Fin 2), j) - zz M ((1 : Fin 2), j)) = 0 := by
    apply eq_zero_of_mem_pow (k := M + M) (by omega)
    have := Ideal.mem_map_of_mem ev (hE j)
    rw [Ideal.map_mul] at this
    rw [pow_add (Ij R (Fin 2 × Fin d) M) M M]
    exact Ideal.mul_mono (hmap 0) (hmap 1) this
  have hadd : sumJ d M (ψ (zR M j)) = cpy d M 0 (ψ (zR M j)) + cpy d M 1 (ψ (zR M j)) := by
    have e1 := DFunLike.congr_fun hsum (zR M j)
    rw [AlgHom.comp_apply, AlgHom.comp_apply] at e1
    have e2 : ev (Φ (zR M j)) = ev (Φ (zR M j) - zz M ((0 : Fin 2), j) - zz M ((1 : Fin 2), j)) +
        ev (zz M ((0 : Fin 2), j)) + ev (zz M ((1 : Fin 2), j)) := by
      rw [map_sub, map_sub]; abel
    rw [e1, e2, hevE, zero_add, hev, hev]
  have h2 : sc M 2 (ψ (zR M j)) = (2 : R) • ψ (zR M j) := by
    rw [← diag_sum_apply, hadd, map_add (f := _), diag_cpy_apply, diag_cpy_apply, two_smul]
  have h3 : sc M 2 (ψ (zR M j)) = (2 : R) ^ M • ψ (zR M j) :=
    sub_eq_zero.1 (eq_zero_of_mem_pow le_rfl (sc_pow_mem (R := R) (κ := Fin 1 × Fin d) M 2 M (hψ j)))
  have h4 : ((2 : R) ^ M - 2) • ψ (zR M j) = 0 := by rw [sub_smul, ← h3, ← h2, sub_self]
  have hu : IsUnit ((2 : R) ^ M - 2) := by
    have hq : ((2 : ℚ) ^ M - 2) ≠ 0 := by
      have : (4 : ℚ) ≤ 2 ^ M := by
        calc (4 : ℚ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ M := pow_le_pow_right₀ (by norm_num) hM
      linarith
    have := (isUnit_iff_ne_zero.2 hq).map (algebraMap ℚ R)
    rwa [map_sub, map_pow, map_ofNat] at this
  exact (hu.smul_eq_zero).1 h4

theorem triv [Algebra ℚ R] {d : ℕ} (δ : ∀ m, sp (R₀ := R) (Jet R (Fin 1 × Fin d) m) ⟶ G)
    (htr : ∀ m, spMap (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] Jet R (Fin 1 × Fin d) m) ≫ δ (m + 1) = δ m)
    (hhom : ∀ m, spMap (sumJ d m) ≫ δ m = (spMap (cpy d m 0) ≫ δ m) * (spMap (cpy d m 1) ≫ δ m))
    (h1 : δ 1 = 1) : ∀ m, δ m = 1 := by
  have hu : ∀ m, spMap (jetAug : Jet R (Fin 1 × Fin d) m →ₐ[R] R) ≫ δ m = 1 := by
    intro m
    have e := congrArg (fun f => spMap (jetAug : Jet R (Fin 2 × Fin d) m →ₐ[R] R) ≫ f) (hhom m)
    simp only [MonObj.comp_mul, ← Category.assoc, spMap_comp, aug_comp_sum, aug_comp_cpy] at e
    exact _root_.mul_eq_left.1 e.symm
  have step : ∀ m, δ (m + 1) = 1 := by
    intro m
    induction m with
    | zero => exact h1
    | succ m ih =>
      obtain ⟨ψ, hψa, hψ⟩ := coord hx (jetAug : Jet R (Fin 1 × Fin d) (m + 1 + 1) →ₐ[R] R) (m + 1 + 1)
        (ker_aug_pow le_rfl) (δ (m + 1 + 1)) (hu _)
      have ht : (jetTrunc : Jet R (Fin 1 × Fin d) (m + 1 + 1) →ₐ[R] Jet R (Fin 1 × Fin d) (m + 1)).comp ψ =
          (Algebra.ofId R _).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) (m + 1 + 1)) := by
        refine uniq hx (jetAug : Jet R (Fin 1 × Fin d) (m + 1) →ₐ[R] R) (m + 1 + 1) (ker_aug_pow (by omega)) ?_ ?_ ?_
        · rw [← AlgHom.comp_assoc, aug_comp_trunc, hψa]
        · exact AlgHom.ext fun a => by simp
        · rw [← spMap_comp, Category.assoc, ← hψ, htr, ih, one_eq hx]
      have hz : ∀ j, ψ (zR (m + 1 + 1) j) ∈ Ij R (Fin 1 × Fin d) (m + 1 + 1) ^ (m + 1 + 1) := fun j => by
        apply mem_pow_of_trunc_eq_zero
        have := DFunLike.congr_fun ht (zR (m + 1 + 1) j)
        rw [AlgHom.comp_apply, AlgHom.comp_apply, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR, map_zero] at this
        exact this
      have h0 := top_step hx (by omega) ψ hψa hz (by rw [← hψ]; exact hhom _)
      have hψ0 : ψ = (Algebra.ofId R _).comp (ReciprocityTheory.ChartRestriction.G.Chart.jetAug R (Fin n) (m + 1 + 1)) :=
        ReciprocityTheory.ChartRestriction.G.Chart.jet_ext fun j => by
          rw [h0 j, AlgHom.comp_apply, ReciprocityTheory.ChartRestriction.G.Chart.jetAug_zR, map_zero]
      rw [hψ, hψ0, one_eq hx]
  intro m
  cases m with
  | zero => rw [← htr 0, step 0, comp_one']
  | succ m => exact step m

end Univ

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqLoc
