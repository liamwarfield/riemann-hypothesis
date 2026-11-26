module

public import Development.EtaleCohomology.EtaleSheaves.CurveThroughGenericPointSpreadsToSmoothProperFamily2
public import Development.EtaleCohomology.EtaleSheaves.LeafDegCut
public import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
public import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafConsPfC
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafConsPfB
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafConsPfA
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafConsPfA
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut

theorem HK_pull_mk (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (F : Shv R) (n : ℤ) (z : Cocycle L (res R F) n) :
    HK.pull R f F n (CohomologyClass.mk z) = CohomologyClass.mk (zcomp (Cocycle.ofHom f) z (zero_add n)) := rfl

theorem HK_pull_comp (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (y : HK R M F n) : HK.pull R (f ≫ g) F n y = HK.pull R f F n (HK.pull R g F n y) := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  rw [HK_pull_mk, HK_pull_mk, HK_pull_mk]
  congr 1
  apply Cocycle.ext
  simp [zcomp, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]

theorem HK_pull_id (R : Type) [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ)
    (y : HK R K F n) : HK.pull R (𝟙 K) F n y = y := by
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective y
  rw [HK_pull_mk]
  congr 1
  apply Cocycle.ext
  simp [zcomp]

theorem map_congr {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) {a a' : K₁ ⟶ K₂} {b b' : L₁ ⟶ L₂} (ha : a = a') (hb : b = b')
    (c : φ₁ ≫ b = a ≫ φ₂) (c' : φ₁ ≫ b' = a' ≫ φ₂) :
    mappingCone.map φ₁ φ₂ a b c = mappingCone.map φ₁ φ₂ a' b' c' := by
  subst ha hb; rfl

theorem rmap_congr (R : Type) [CommRing R] {U E U' E' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') {u u2 : U' ⟶ U} {e e2 : E' ⟶ E}
    (hu : u = u2) (he : e = e2) (c : f' ≫ e = u ≫ f) (c2 : f' ≫ e2 = u2 ≫ f) :
    rmap R f f' u e c = rmap R f f' u2 e2 c2 := by
  subst hu he; rfl

theorem rmap_comp (R : Type) [CommRing R] {U E U' E' U'' E'' : Spc} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (c'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) :
    rmap R f f'' (u' ≫ u) (e' ≫ e) c'' = rmap R f' f'' u' e' c' ≫ rmap R f f' u e c := by
  unfold rmap
  exact (map_congr _ _ ((chains R).map_comp _ _) ((chains R).map_comp _ _) _ _).trans
    (mappingCone.map_comp _ _ _ _ _ _ _ _ _)

theorem rmap_id (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E) (c : f ≫ 𝟙 E = 𝟙 U ≫ f) :
    rmap R f f (𝟙 U) (𝟙 E) c = 𝟙 _ := by
  unfold rmap
  exact (map_congr _ _ ((chains R).map_id _) ((chains R).map_id _) _ _).trans (mappingCone.map_id _)

theorem rpl_comp (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (c'' : f'' ≫ (e' ≫ e) = (u' ≫ u) ≫ f) (n : ℤ) (y) :
    rpl q i f f'' (u' ≫ u) (e' ≫ e) c'' n y = rpl q i f' f'' u' e' c' n (rpl q i f f' u e c n y) := by
  simp only [rpl, rpull]
  rw [← HK_pull_comp, ← rmap_comp _ _ _ _ _ _ _ _ _ _ (by simp only [← Functor.map_comp, c'', Category.assoc])]
  congr 1

theorem rpl_id (q : ℕ) (i : ℤ) {U E : Scheme.{0}} (f : U ⟶ E) (c : f ≫ 𝟙 E = 𝟙 U ≫ f) (n : ℤ) (y) :
    rpl q i f f (𝟙 U) (𝟙 E) c n y = y := by
  simp only [rpl, rpull]
  rw [rmap_congr _ _ _ (sch.map_id _) (sch.map_id _) _ (by simp), rmap_id, HK_pull_id]

theorem rpl_bij (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (u : U' ⟶ U) (e : E' ⟶ E)
    (c : f' ≫ e = u ≫ f) [IsIso u] [IsIso e] (n : ℤ) : Function.Bijective (rpl q i f f' u e c n) := by
  have c2 : f ≫ inv e = inv u ≫ f' := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine Function.bijective_iff_has_inverse.2 ⟨rpl q i f' f (inv u) (inv e) c2 n, fun y => ?_, fun y => ?_⟩
  · rw [← rpl_comp q i f f' f u e (inv u) (inv e) c c2 (by simp), ]
    simp only [IsIso.inv_hom_id]
    exact rpl_id q i f _ n y
  · rw [← rpl_comp q i f' f f' (inv u) (inv e) u e c2 c (by simp)]
    simp only [IsIso.hom_inv_id]
    exact rpl_id q i f' _ n y

end LateralTheory.E.LeafConsPfA
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafConsPfB
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafConsPfA

theorem rpl_congr (q : ℕ) (i : ℤ) {U E U' E' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') {u u2 : U' ⟶ U} {e e2 : E' ⟶ E}
    (hu : u = u2) (he : e = e2) (c : f' ≫ e = u ≫ f) (c2 : f' ≫ e2 = u2 ≫ f) (n : ℤ) (y) :
    rpl q i f f' u e c n y = rpl q i f f' u2 e2 c2 n y := by
  subst hu he; rfl

instance (B : Scheme.{0}) : IsIso (top B).hom := by show IsIso (Iso.refl B).hom; infer_instance

abbrev uT {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    pullback (pullback.snd p (top B).hom ≫ (top B).hom) ι ⟶ pullback p ι :=
  pullback.map _ ι p ι (pullback.fst p (top B).hom) (𝟙 W) (𝟙 B) (by rw [Category.comp_id, pullback.condition]) (by simp)

theorem uT_comm {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    prU p ι (top B) ≫ pullback.fst p (top B).hom = uT p ι ≫ pullback.fst p ι := (pullback.lift_fst _ _ _).symm

instance {Y B : Scheme.{0}} (p : Y ⟶ B) : IsIso (pullback.fst p (top B).hom) := by infer_instance
instance {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) : IsIso (uT p ι) := by infer_instance

theorem rpl_comp' (q : ℕ) (i : ℤ) {U E U' E' U'' E'' : Scheme.{0}} (f : U ⟶ E) (f' : U' ⟶ E') (f'' : U'' ⟶ E'')
    (u : U' ⟶ U) (e : E' ⟶ E) (u' : U'' ⟶ U') (e' : E'' ⟶ E') (c : f' ≫ e = u ≫ f) (c' : f'' ≫ e' = u' ≫ f')
    (n : ℤ) (y) :
    rpl q i f' f'' u' e' c' n (rpl q i f f' u e c n y) =
      rpl q i f f'' (u' ≫ u) (e' ≫ e) (by rw [← Category.assoc, c', Category.assoc, c, Category.assoc]) n y :=
  (rpl_comp q i f f' f'' u e u' e' c c' _ n y).symm

abbrev TT (q : ℕ) (i : ℤ) {Y B W : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) (n : ℤ) :=
  rpl q i (pullback.fst p ι) (prU p ι (top B)) (uT p ι) (pullback.fst p (top B).hom) (uT_comm p ι) n

abbrev TL (q : ℕ) (i : ℤ) {B W : Scheme.{0}} (ι : W ⟶ B) (n : ℤ) :=
  rpl q i ι (prB ι (top B)) (pullback.snd (top B).hom ι) (top B).hom pullback.condition n

set_option maxHeartbeats 800000 in
theorem L1 {B Y0 Y1 Y2 : Scheme.{0}} (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) :
    pullback.fst (g2 ≫ g1 ≫ p) (top B).hom ≫ g2 ≫ g1 =
      mY (g1 ≫ p) g2 (top B) ≫ mY p g1 (top B) ≫ pullback.fst p (top B).hom := by
  simp only [mY, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]

set_option maxHeartbeats 800000 in
theorem L3 {B W Y : Scheme.{0}} (p : Y ⟶ B) (ι : W ⟶ B) :
    uT p ι ≫ pullback.snd p ι = toBW p ι (top B) ≫ pullback.snd (top B).hom ι := by
  simp only [uT, toBW, pullback.map]
  erw [pullback.lift_snd, pullback.lift_snd]

set_option maxHeartbeats 800000 in
theorem L2 {B W Y0 Y1 Y2 : Scheme.{0}} (ι : W ⟶ B) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1) :
    uT (g2 ≫ g1 ≫ p) ι ≫ pullback.map (g2 ≫ g1 ≫ p) ι p ι (g2 ≫ g1) (𝟙 W) (𝟙 B) (by simp) (by simp) =
      mW (g1 ≫ p) g2 ι (top B) ≫ mW p g1 ι (top B) ≫ uT p ι := by
  apply pullback.hom_ext
  · have := L1 p g1 g2
    simp only [mY] at this
    simp only [uT, mW, mY, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, pullback.map]
  · simp only [uT, mW, mY, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, pullback.map]
    simp

theorem LeafGlob_pf : LateralTheory.E.LeafConsPf.LeafGlob := by
  intro q _ i B W Y0 Y1 Y2 ι _ p g1 g2 K0 K1 K2 L f g ℓ l0 l1 l2 lL r0 r1 r2 rL mf mg mℓ
  refine ⟨fun n y => l0 (top B) n (TT q i p ι n y), fun n y => l2 (top B) n (TT q i (g2 ≫ g1 ≫ p) ι n y),
    fun n c => lL (top B) n (TL q i ι n c), ?_, ?_, ?_, ?_⟩
  · intro n
    exact (r2.1 _ n).1.comp (rpl_bij _ _ _ _ _ _ _ _).1
  · intro n
    exact (rL.1 _ n).2.comp (rpl_bij _ _ _ _ _ _ _ _).2
  · intro n y
    have h1 := mf (top B) n (TT q i p ι n y)
    have h2 := mg (top B) n (rpl q i (prU p ι (top B)) (prU (g1 ≫ p) ι (top B)) (mW p g1 ι (top B)) (mY p g1 (top B))
      (pullback.lift_fst _ _ _).symm n (TT q i p ι n y))
    show l2 (top B) n _ = l0 (top B) n (TT q i p ι n y) ≫ (shiftFunctor _ n).map (f ≫ g)
    rw [Functor.map_comp]
    refine Eq.trans ?_ (Category.assoc _ _ _)
    rw [← h1, ← h2]
    refine congrArg (l2 (top B) n) ?_
    rw [rpl_comp', rpl_comp', rpl_comp']
    apply rpl_congr
    · simpa only [Category.assoc] using L2 ι p g1 g2
    · simpa only [Category.assoc] using L1 p g1 g2
  · intro n c
    have h := mℓ (top B) n (TL q i ι n c)
    refine Eq.trans ?_ h
    refine congrArg (l2 (top B) n) ?_
    rw [rpl_comp', rpl_comp']
    apply rpl_congr
    · simpa only [Category.assoc] using L3 (g2 ≫ g1 ≫ p) ι
    · simp only [toBY]; exact pullback.condition

end LateralTheory.E.LeafConsPfB
end
end

namespace LateralTheory.E.LeafConsPfC

theorem LeafCons_of (hL : LateralTheory.E.LeafConsPf.LeafLoc) : LateralTheory.E.EtaleTopologySheaves.LeafCons :=
  LateralTheory.E.LeafConsPf.LeafCons_of hL LateralTheory.E.LeafConsPfB.LeafGlob_pf

end LateralTheory.E.LeafConsPfC
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LIdemLiftPf
noncomputable section

namespace LateralTheory.E.LIdemLiftPf

open Polynomial

def IdemLiftFin (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra A B] [Module.Finite A B]
    (ε : B ⧸ I.map (algebraMap A B)), IsIdempotentElem ε →
    ∃ e : B, IsIdempotentElem e ∧ Ideal.Quotient.mk _ e = ε

def FactLift (A : Type) [CommRing A] (I : Ideal A) : Prop :=
  ∀ (g : A[X]), g.Monic → ∀ n m : ℕ, g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
    ∃ P Q : A[X], P.Monic ∧ Q.Monic ∧ g = P * Q ∧
      P.map (Ideal.Quotient.mk I) = X ^ n ∧ Q.map (Ideal.Quotient.mk I) = (X - 1) ^ m

def LFact : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I], FactLift A I

def LFinOfFact : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ →
  FactLift A I → IdemLiftFin A I

def LRed : Prop := ∀ (A : Type) [CommRing A] (I : Ideal A), IdemLiftFin A I →
  LateralTheory.E.LChartPf.IdemLiftInt A I

theorem idem_of_mul_eq_zero {B : Type} [CommRing B] (x y : B) (hxy : x * y = 0) (hu : IsUnit (x + y)) :
    IsIdempotentElem (x * hu.unit⁻¹) := by
  have hx : x * x = x * (x + y) := by rw [mul_add, hxy, add_zero]
  have h1 : (x + y) * (hu.unit⁻¹ : Bˣ) = 1 := hu.mul_val_inv
  unfold IsIdempotentElem
  calc x * ↑hu.unit⁻¹ * (x * ↑hu.unit⁻¹) = x * x * (↑hu.unit⁻¹ * ↑hu.unit⁻¹) := by ring
    _ = x * ((x + y) * ↑hu.unit⁻¹) * ↑hu.unit⁻¹ := by rw [hx]; ring
    _ = x * ↑hu.unit⁻¹ := by rw [h1, mul_one]

theorem lRed : LRed := by
  intro A _ I hfin B _ _ _ ε hε
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ε
  have hb : b * b - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]
  rw [Ideal.map, Submodule.mem_span_set'] at hb
  obtain ⟨n, f, g, hfg⟩ := hb
  choose a ha hag using fun i => (g i).2
  let C : Subalgebra A B := Algebra.adjoin A (insert b (Set.range f))
  have hC : Module.Finite A C := by
    have := Algebra.finite_adjoin_of_finite_of_isIntegral (R := A) (s := insert b (Set.range f))
      ((Set.finite_range f).insert b) (fun x _ => Algebra.IsIntegral.isIntegral x)
    exact this
  have hbC : b ∈ C := Algebra.subset_adjoin (Set.mem_insert _ _)
  have hfC : ∀ i, f i ∈ C := fun i => Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  let bC : C := ⟨b, hbC⟩
  have hmem : bC * bC - bC ∈ I.map (algebraMap A C) := by
    have : bC * bC - bC = ∑ i, (⟨f i, hfC i⟩ : C) * algebraMap A C (a i) := by
      apply Subtype.ext
      simp only [bC, Subalgebra.coe_sub, Subalgebra.coe_mul, ← hfg, smul_eq_mul]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hag i]
    rw [this]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (ha i))
  have hidC : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A C)) bC) := by
    unfold IsIdempotentElem
    rw [← map_mul, Ideal.Quotient.eq]; exact hmem
  obtain ⟨e, he, hee⟩ := hfin C _ hidC
  refine ⟨(e : B), ?_, ?_⟩
  · unfold IsIdempotentElem; exact congrArg Subtype.val he.eq
  · rw [Ideal.Quotient.eq] at hee ⊢
    have := Ideal.mem_map_of_mem (C.val : C →ₐ[A] B).toRingHom hee
    rw [Ideal.map_map] at this
    simpa [bC] using this

theorem exists_monic_of_idem_mod {A : Type} [CommRing A] (I : Ideal A) (B : Type) [CommRing B] [Algebra A B]
    [Module.Finite A B] (b : B) (hb : b * b - b ∈ I.map (algebraMap A B)) :
    ∃ (g : A[X]) (d : ℕ), g.Monic ∧ aeval b g = 0 ∧
      g.map (Ideal.Quotient.mk I) = X ^ (d + 1) * (X - 1) ^ (d + 1) := by
  let φ : Module.End A B := LinearMap.mulLeft A (b * b - b)
  have hφ : LinearMap.range φ ≤ I • (⊤ : Submodule A B) := by
    rintro _ ⟨y, rfl⟩
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hb
  obtain ⟨p, hpm, -, hpc, hpφ⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A φ I hφ
  have hp0 : aeval (b * b - b) p = 0 := by
    have hφ' : φ = Algebra.lmul A B (b * b - b) := rfl
    rw [hφ', Polynomial.aeval_algHom_apply] at hpφ
    simpa using congrArg (fun ψ : Module.End A B => ψ 1) hpφ
  have hpmap : p.map (Ideal.Quotient.mk I) = X ^ p.natDegree := by
    ext k
    rw [coeff_map, coeff_X_pow]
    split_ifs with hk
    · subst hk; rw [hpm.coeff_natDegree, map_one]
    · rcases lt_or_gt_of_ne hk with h | h
      · rw [Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.pow_le_self (by omega) (hpc k)
      · rw [coeff_eq_zero_of_natDegree_lt h, map_zero]
  rcases subsingleton_or_nontrivial A with hA | hA
  · have h10 : (1 : B) = 0 := by rw [← map_one (algebraMap A B), Subsingleton.elim (1 : A) 0, map_zero]
    have : Subsingleton B := subsingleton_of_zero_eq_one h10.symm
    have h10' : (1 : A ⧸ I) = 0 := by rw [← map_one (Ideal.Quotient.mk I), Subsingleton.elim (1 : A) 0, map_zero]
    have : Subsingleton (A ⧸ I) := subsingleton_of_zero_eq_one h10'.symm
    exact ⟨p, 0, hpm, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have hqm : (X * X - X : A[X]).Monic := by
    rw [show (X * X - X : A[X]) = X ^ 2 - X by ring]
    exact monic_X_pow_sub (by rw [degree_X]; exact_mod_cast (by norm_num : 1 < 2))
  have hq : (X * X - X : A[X]).natDegree = 2 := by
    rw [show (X * X - X : A[X]) = X ^ 2 - X by ring]
    compute_degree!
  refine ⟨p.comp (X * X - X) * (X * X - X), p.natDegree, (hpm.comp hqm (by omega)).mul hqm, ?_, ?_⟩
  · rw [map_mul, aeval_comp]; simp [hp0]
  · simp only [Polynomial.map_mul, map_comp, hpmap, X_pow_comp, Polynomial.map_sub, map_X]
    rw [show (X * X - X : (A ⧸ I)[X]) = X * (X - 1) by ring, mul_pow]
    ring

theorem aeval_sub_mem_of_map_eq {A : Type} [CommRing A] (I : Ideal A) {B : Type} [CommRing B] [Algebra A B]
    (f f' : A[X]) (h : f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I)) (b : B) :
    aeval b f - aeval b f' ∈ I.map (algebraMap A B) := by
  have h1 : f - f' ∈ Ideal.map (C : A →+* A[X]) I := by
    rw [← Ideal.mk_ker (I := I), ← Polynomial.ker_mapRingHom, RingHom.mem_ker, map_sub]
    simp only [coe_mapRingHom, h, sub_self]
  have h2 := Ideal.mem_map_of_mem (aeval b).toRingHom h1
  rw [Ideal.map_map] at h2
  have h3 : (aeval b).toRingHom.comp (C : A →+* A[X]) = algebraMap A B := by ext; simp
  rw [h3] at h2
  simpa using h2

theorem isUnit_one_add_of_finite {A : Type} [CommRing A] (I : Ideal A) (hI : I ≤ Ideal.jacobson ⊥)
    {B : Type} [CommRing B] [Algebra A B] [Module.Finite A B] (s : B)
    (hs : s - 1 ∈ I.map (algebraMap A B)) : IsUnit s := by
  have key : (⊤ : Submodule A B) ≤ (Ideal.span {s}).restrictScalars A := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_
    intro y _
    have hy : y = s * y - (s - 1) * y := by ring
    rw [hy]
    refine Submodule.sub_mem_sup (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)) ?_
    rw [Ideal.smul_top_eq_map]
    exact Ideal.mul_mem_right _ _ hs
  have h1 : (1 : B) ∈ Ideal.span {s} := key Submodule.mem_top
  rw [Ideal.mem_span_singleton] at h1
  exact isUnit_of_dvd_one h1

theorem lFinOfFact : LFinOfFact := by
  intro A _ I hI hF B _ _ _ ε hε
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective ε
  set π := Ideal.Quotient.mk (I.map (algebraMap A B))
  have hb : b * b - b ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hε.eq, sub_self]
  obtain ⟨g, d, hgm, hgb, hgmap⟩ := exists_monic_of_idem_mod I B b hb
  obtain ⟨P, Q, -, -, hPQ, hP, hQ⟩ := hF g hgm _ _ hgmap
  have hcop : IsCoprime (X ^ (d + 1) : (A ⧸ I)[X]) ((X - 1) ^ (d + 1)) :=
    (show IsCoprime (X : (A ⧸ I)[X]) (X - 1) from ⟨1, -1, by ring⟩).pow
  obtain ⟨u0, v0, huv0⟩ := hcop
  obtain ⟨u, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective u0
  obtain ⟨v, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective v0
  have hπ : ∀ f f' : A[X], f.map (Ideal.Quotient.mk I) = f'.map (Ideal.Quotient.mk I) →
      π (aeval b f) = π (aeval b f') := fun f f' h =>
    Ideal.Quotient.eq.2 (aeval_sub_mem_of_map_eq I f f' h b)
  have hPb : π (aeval b P) = π b ^ (d + 1) := by
    rw [hπ P (X ^ (d + 1)) (by rw [hP]; simp)]; simp
  have hQb : π (aeval b Q) = (π b - 1) ^ (d + 1) := by
    rw [hπ Q ((X - 1) ^ (d + 1)) (by rw [hQ]; simp)]; simp
  have hUb : π (aeval b (u * P)) + π (aeval b (v * Q)) = 1 := by
    rw [← map_add (f := _), ← map_add (f := _), hπ (u * P + v * Q) 1 (by simp [Polynomial.map_add (f := _), Polynomial.map_mul, hP, hQ, huv0])]
    simp
  set x := aeval b (u * P)
  set y := aeval b (v * Q)
  have hxy : x * y = 0 := by
    simp only [x, y, ← map_mul]
    rw [show u * P * (v * Q) = u * v * g by rw [hPQ]; ring, map_mul, hgb, mul_zero]
  have hs : (x + y) - 1 ∈ I.map (algebraMap A B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_add (f := _), hUb, map_one, sub_self]
  have hu := isUnit_one_add_of_finite I hI (x + y) hs
  refine ⟨x * hu.unit⁻¹, idem_of_mul_eq_zero x y hxy hu, ?_⟩
  have hinv : π (hu.unit⁻¹ : Bˣ) = 1 := by
    have h1 : π (x + y) * π (hu.unit⁻¹ : Bˣ) = 1 := by rw [← map_mul, hu.mul_val_inv, map_one]
    rwa [map_add, hUb, one_mul] at h1
  have he : π b * π b = π b := hε.eq
  have hx : π x = π b := by
    have e1 : π x * (1 - π b) = 0 := by
      simp only [x, map_mul, hPb]
      rw [pow_succ, mul_assoc, mul_assoc, mul_sub, mul_one, he, sub_self, mul_zero, mul_zero]
    have e2 : π y * π b = 0 := by
      simp only [y, map_mul, hQb]
      rw [pow_succ, mul_assoc, mul_assoc, sub_mul, he, one_mul, sub_self, mul_zero, mul_zero]
    have e3 : π x = π x * π b := by linear_combination e1
    rw [e3]; linear_combination (π b) * hUb - e2
  rw [map_mul, hinv, mul_one, hx]

theorem LIdemLift_of (h1 : LFact) : LateralTheory.E.LChartPf.LIdemLift := by
  intro A _ I _
  exact lRed A I (lFinOfFact A I (by simpa only [Ideal.jacobson_bot] using (HenselianRing.jac (R := A) (I := I))) (h1 A I))

end LateralTheory.E.LIdemLiftPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.KerLocOf
section -- merged from Development.EtaleCohomology.EtaleSheaves.BijOfIso
section -- merged from Development.EtaleCohomology.EtaleSheaves.PushColim
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

abbrev PP (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) := pull (ZMod q) (sch.map (Spec.map f)) (tw q i) n
theorem PP_comp (q : ℕ) (i n : ℤ) {A B C : CommRingCat.{0}} (f : A ⟶ B) (g : B ⟶ C) (x) :
    PP q i n (f ≫ g) x = PP q i n g (PP q i n f x) := by
  rw [PP, Spec.map_comp, Functor.map_comp, pull_comp]
theorem unit_of {q : ℕ} {A B : CommRingCat.{0}} (f : A ⟶ B) (h : IsUnit (q : A)) : IsUnit (q : B) := by
  simpa using h.map f.hom

abbrev HR (q : ℕ) (i n : ℤ) {D Y : CommRingCat.{0}} (φ : D ⟶ Y) := Hrel (ZMod q) (sch.map (Spec.map φ)) (tw q i) n

abbrev RP (q : ℕ) (i n : ℤ) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z) (ψ : E ⟶ Z)
    (h : φ ≫ u = e ≫ ψ) : HR q i n φ →+ HR q i n ψ :=
  rpl q i (Spec.map φ) (Spec.map ψ) (Spec.map u) (Spec.map e) (by rw [← Spec.map_comp, ← Spec.map_comp, h]) n

theorem RP_comp (q : ℕ) (i n : ℤ) {D Y E Z E' Z' : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z) (ψ : E ⟶ Z)
    (h : φ ≫ u = e ≫ ψ) (e' : E ⟶ E') (u' : Z ⟶ Z') (ψ' : E' ⟶ Z') (h' : ψ ≫ u' = e' ≫ ψ') (e2 : D ⟶ E') (u2 : Y ⟶ Z')
    (h2 : φ ≫ u2 = e2 ≫ ψ') (he : e ≫ e' = e2) (hu : u ≫ u' = u2) (z : HR q i n φ) :
    RP q i n φ e2 u2 ψ' h2 z = RP q i n ψ e' u' ψ' h' (RP q i n φ e u ψ h z) :=
  rpull_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by rw [← hu, Spec.map_comp, Functor.map_comp])
    (by rw [← he, Spec.map_comp, Functor.map_comp]) n z

theorem RP_bd (q : ℕ) (i m n : ℤ) (hm : 1 + m = n) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z)
    (ψ : E ⟶ Z) (h : φ ≫ u = e ≫ ψ) (y) :
    RP q i n φ e u ψ h (bd _ _ _ m n hm y) = bd _ _ _ m n hm (PP q i m u y) := rpull_bd ..

theorem fgt_RP (q : ℕ) (i n : ℤ) {D Y E Z : CommRingCat.{0}} (φ : D ⟶ Y) (e : D ⟶ E) (u : Y ⟶ Z)
    (ψ : E ⟶ Z) (h : φ ≫ u = e ≫ ψ) (z : HR q i n φ) :
    fgt _ _ _ n (RP q i n φ e u ψ h z) = PP q i n e (fgt _ _ _ n z) := relNat _ _ _ _ _ _ _ n z

theorem pushColim {A Y C Y' : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) (w : Y ⟶ Y') (φ' : C ⟶ Y')
    (hpo : IsPushout φ c w φ') {J : Type} [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (s : D ⟶ (Functor.const J).obj C) (hc : IsColimit (Cocone.mk _ s))
    (ht : ∀ j, t.app j ≫ s.app j = c) :
    ∃ (E : J ⥤ CommRingCat.{0}) (p : D ⟶ E) (e : E ⟶ (Functor.const J).obj Y') (v : ∀ j, Y ⟶ E.obj j),
      Nonempty (IsColimit (Cocone.mk _ e)) ∧ (∀ j, IsPushout φ (t.app j) (v j) (p.app j)) ∧
      (∀ j, p.app j ≫ e.app j = s.app j ≫ φ') ∧ ∀ j k (f : j ⟶ k), v j ≫ E.map f = v k := by
  have : IsConnected J := IsFiltered.isConnected J
  let F : J ⥤ Under A := D.toUnder A (fun j => t.app j) (fun {j k} g => by
    have := t.naturality g
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
    exact this.symm)
  let cU : Cocone F :=
    { pt := Under.mk c
      ι := { app := fun j => Under.homMk (s.app j) (ht j)
             naturality := fun j k g => by
               apply Under.UnderMorphism.ext
               exact s.naturality g } }
  have hcU : IsColimit cU := isColimitOfReflects (Under.forget A) (by exact hc)
  have h2 := isColimitOfPreserves (Under.pushout φ ⋙ Under.forget Y) hcU
  let E : J ⥤ CommRingCat.{0} := F ⋙ Under.pushout φ ⋙ Under.forget Y
  let e : E ⟶ (Functor.const J).obj Y' :=
    ((Under.pushout φ ⋙ Under.forget Y).mapCocone cU).ι ≫ (Functor.const J).map hpo.flip.isoPushout.inv
  have hE : IsColimit (Cocone.mk _ e) :=
    h2.ofIsoColimit (Cocone.ext hpo.flip.isoPushout.symm (fun j => rfl))
  let p : D ⟶ E :=
    { app := fun j => (pushout.inl (t.app j) φ : D.obj j ⟶ pushout (t.app j) φ)
      naturality := fun j k g => by
        exact (pushout.inl_desc _ _ _).symm }
  refine ⟨E, p, e, fun j => pushout.inr (t.app j) φ, ⟨hE⟩, fun j => (IsPushout.of_hasPushout (t.app j) φ).flip,
    fun j => ?_, fun j k f => pushout.inr_desc _ _ _⟩
  have key : ∀ h, pushout.inl (t.app j) φ ≫ (pushout.desc (s.app j ≫ pushout.inl c φ) (pushout.inr c φ) h ≫
      hpo.flip.isoPushout.inv) = s.app j ≫ φ' := by
    intro h; rw [← Category.assoc, pushout.inl_desc, Category.assoc, hpo.flip.inl_isoPushout_inv]
  exact key _

theorem relAt (hB1 : B1) (q : ℕ) (i n : ℤ) {D Y' O : CommRingCat.{0}} (φ' : D ⟶ Y') (hq : IsUnit (q : D)) (o : D ⟶ O)
    (hIE : IE o) (hBC : BC q i φ' o) (z : HR q i n φ') (hz : PP q i n φ' (fgt _ _ _ n z) = 0) :
    ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (s : E ⟶ O) (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z)
      (h : IsPushout φ' e u ψ), Et e ∧ e ≫ s = o ∧ RP q i n φ' e u ψ h.w z = 0 := by
  obtain ⟨J, _, _, F, t, s, hc, hts⟩ := hIE
  have hZ := IsPushout.of_hasPushout φ' o
  set ψ := pushout.inr φ' o
  have hRE := hBC _ _ _ hZ
  obtain ⟨G, p, e, v, ⟨hG⟩, hpo, hpe, hv⟩ := pushColim φ' o _ ψ hZ F t s hc (fun j => (hts j).2)
  have hnat : ∀ {j k} (f : j ⟶ k), t.app j ≫ F.map f = t.app k := fun f => by simpa using (t.naturality f).symm
  have hs : ∀ {j k} (f : j ⟶ k), F.map f ≫ s.app k = s.app j := fun f => by simpa using s.naturality f
  have he : ∀ {j k} (f : j ⟶ k), G.map f ≫ e.app k = e.app j := fun f => by simpa using e.naturality f
  have hxO : PP q i n o (fgt _ _ _ n z) = 0 := by
    apply (hRE n).1
    change PP q i n ψ _ = _
    rw [map_zero, ← PP_comp, ← hZ.w, PP_comp, hz, map_zero]
  obtain ⟨j0⟩ : Nonempty J := IsFiltered.nonempty
  obtain ⟨k, f, hk⟩ := (hB1 q F _ hc n i).2 j0 (PP q i n (t.app j0) (fgt _ _ _ n z)) (unit_of (t.app j0) hq) (by
    change PP q i n (s.app j0) _ = 0
    rw [← PP_comp, (hts j0).2, hxO])
  change PP q i n (F.map f) _ = 0 at hk
  rw [← PP_comp, hnat] at hk
  have hm : 1 + (n - 1) = n := by omega
  obtain ⟨y, hy⟩ := exists_bd _ _ _ (n - 1) n hm (RP q i n φ' (t.app k) (v k) (p.app k) (hpo k).w z)
    (by rw [fgt_RP]; exact hk)
  obtain ⟨a, ha⟩ := (hRE (n - 1)).2 (PP q i (n - 1) (e.app k) y)
  obtain ⟨j, b, rfl⟩ := (hB1 q F _ hc (n - 1) i).1 a (unit_of o hq)
  change PP q i (n - 1) ψ (PP q i (n - 1) (s.app j) b) = _ at ha
  obtain ⟨l, g, hl⟩ := (hB1 q G _ hG (n - 1) i).2 (IsFiltered.max j k)
    (PP q i (n - 1) (G.map (IsFiltered.rightToMax j k)) y -
      PP q i (n - 1) (F.map (IsFiltered.leftToMax j k) ≫ p.app _) b) (unit_of (t.app _ ≫ p.app _) hq) (by
    change PP q i (n - 1) (e.app _) _ = 0
    rw [map_sub, ← PP_comp, ← PP_comp, he, Category.assoc, hpe, ← Category.assoc, hs, PP_comp, ha, sub_self])
  change PP q i (n - 1) (G.map g) _ = 0 at hl
  rw [map_sub, sub_eq_zero, ← PP_comp, ← PP_comp, ← G.map_comp, Category.assoc, ← p.naturality g,
    ← Category.assoc, PP_comp q i (n - 1) _ (p.app l)] at hl
  refine ⟨F.obj l, t.app l, s.app l, G.obj l, v l, p.app l, hpo l, (hts l).1, (hts l).2, ?_⟩
  rw [RP_comp q i n φ' (t.app k) (v k) (p.app k) (hpo k).w (F.map (IsFiltered.rightToMax j k ≫ g))
    (G.map (IsFiltered.rightToMax j k ≫ g)) (p.app l) (p.naturality _).symm _ _ _ (hnat _) (hv _ _ _), ← hy, RP_bd, hl]
  exact bd_pull ..

end LateralTheory.E.KernelLocalization
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut LateralTheory.E.KillCokPf.Asm

namespace LateralTheory.E.KernelLocalization

theorem bij_of_iso (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (n : ℤ) :
    Function.Bijective (pull R (sch.map f) F n) := by
  have h1 : ∀ x, pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull R (sch.map f) F n (pull R (sch.map (inv f)) F n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem cover_bij (hC : Coprod) (R : Type) [CommRing R] (F : Shv R) {ι : Type} {X : ι → Scheme.{0}} {S : Scheme.{0}}
    (π : ∀ j, X j ⟶ S) [IsIso (Sigma.desc π)] (n : ℤ) :
    Function.Bijective fun (x : H R (sch.obj S) F n) (j : ι) => pull R (sch.map (π j)) F n x := by
  have := (hC R F X n).comp (bij_of_iso R F (Sigma.desc π) n)
  convert this using 1
  funext x j
  simp only [Function.comp]
  rw [← pull_comp, ← Functor.map_comp, Sigma.ι_desc]

abbrev pr {ι : Type} (E : ι → CommRingCat.{0}) (j : ι) : CommRingCat.of (∀ k, E k) ⟶ E j :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k => E k) j)

theorem pi_bij (hC : Coprod) (q : ℕ) (i n : ℤ) {ι : Type} [Finite ι] (E : ι → CommRingCat.{0}) :
    Function.Bijective fun x (j : ι) => PP q i n (pr E j) x := by
  have : IsIso (Sigma.desc fun j => Spec.map (pr E j)) := inferInstanceAs (IsIso (sigmaSpec E))
  exact cover_bij hC _ _ _ n

theorem push_inj (hC : Coprod) (q : ℕ) (i n : ℤ) {ι : Type} [Finite ι] (E : ι → CommRingCat.{0}) {Z : CommRingCat.{0}}
    (ψ : CommRingCat.of (∀ k, E k) ⟶ Z) (y : H (ZMod q) (sch.obj (Spec Z)) (tw q i) n)
    (hy : ∀ j, PP q i n (pushout.inl ψ (pr E j)) y = 0) : y = 0 := by
  have h0 : IsIso (Sigma.desc fun j => Spec.map (pr E j)) := inferInstanceAs (IsIso (sigmaSpec E))
  have := FinitaryPreExtensive.isIso_sigmaDesc_fst (fun j => Spec.map (pr E j)) (Spec.map ψ) h0
  apply (cover_bij hC (ZMod q) (tw q i) (fun j => pullback.fst (Spec.map ψ) (Spec.map (pr E j))) n).1
  funext j
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ (IsPushout.of_hasPushout ψ (pr E j))
  simp only [map_zero]
  rw [← hp.isoPullback_inv_fst, Functor.map_comp, pull_comp]
  change pull _ _ _ _ (PP q i n _ y) = 0
  rw [hy, map_zero]

theorem rel_pi (hC : Coprod) (q : ℕ) (i n : ℤ) {D Y : CommRingCat.{0}} (φ : D ⟶ Y) {ι : Type} [Finite ι]
    (E : ι → CommRingCat.{0}) (e : ∀ j, D ⟶ E j) (z : HR q i n φ)
    (hz : ∀ j, ∃ (Z : CommRingCat.{0}) (u : Y ⟶ Z) (ψ : E j ⟶ Z) (h : IsPushout φ (e j) u ψ), RP q i n φ (e j) u ψ h.w z = 0)
    {Z : CommRingCat.{0}} (u : Y ⟶ Z) (ψ : CommRingCat.of (∀ k, E k) ⟶ Z) (h : IsPushout φ (piMap E e) u ψ) :
    RP q i n φ (piMap E e) u ψ h.w z = 0 := by
  have hpr : ∀ j, piMap E e ≫ pr E j = e j := fun j => by ext a; rfl
  have hw : ∀ j, φ ≫ u ≫ pushout.inl ψ (pr E j) = e j ≫ pushout.inr ψ (pr E j) := fun j => by
    rw [h.w_assoc, pushout.condition, ← Category.assoc, hpr]
  have hj : ∀ j, RP q i n ψ (pr E j) (pushout.inl ψ (pr E j)) (pushout.inr ψ (pr E j)) pushout.condition
      (RP q i n φ (piMap E e) u ψ h.w z) = 0 := fun j => by
    obtain ⟨Z', u', ψ', h', h0⟩ := hz j
    rw [← RP_comp q i n φ _ u ψ h.w _ _ _ _ (e j) _ (hw j) (hpr j) rfl,
      RP_comp q i n φ (e j) u' ψ' h'.w (𝟙 _) (h'.desc _ _ (hw j)) _ (by simp) (e j) _ (hw j) (by simp) (by simp),
      h0, map_zero]
  set z' := RP q i n φ (piMap E e) u ψ h.w z
  have hm : 1 + (n - 1) = n := by omega
  have hf : fgt _ _ _ n z' = 0 := by
    apply (pi_bij hC q i n E).1
    funext j
    simp only [map_zero]
    rw [← fgt_RP q i n ψ (pr E j) _ _ pushout.condition, hj, map_zero]
  obtain ⟨y, hy⟩ := exists_bd _ _ _ (n - 1) n hm z' hf
  have hb : ∀ j, ∃ w, PP q i (n - 1) (pushout.inr ψ (pr E j)) w = PP q i (n - 1) (pushout.inl ψ (pr E j)) y := fun j => by
    refine range_of_bd _ _ _ (n - 1) n hm _ ?_
    rw [← RP_bd q i (n - 1) n hm ψ (pr E j) _ _ pushout.condition, hy, hj]
  choose w hw' using hb
  obtain ⟨a, ha⟩ := (pi_bij hC q i (n - 1) E).2 w
  have hya : y - PP q i (n - 1) ψ a = 0 := push_inj hC q i (n - 1) E ψ _ fun j => by
    rw [map_sub, ← PP_comp, pushout.condition, PP_comp, ← hw' j, ← congrFun ha j, sub_self]
  rw [← hy, sub_eq_zero.1 hya]
  exact bd_pull ..

theorem relKill (hB1 : B1) (hC : Coprod) (q : ℕ) (i n : ℤ) {A Y D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (hq : IsUnit (q : A))
    (d : A ⟶ D) (hpts : LocPts q i φ d) (w : Y ⟶ Y') (φ' : D ⟶ Y') (hpo : IsPushout φ d w φ') (z : HR q i n φ')
    (hz : PP q i n φ' (fgt _ _ _ n z) = 0) :
    ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ),
      Et e ∧ SpS e ∧ RP q i n φ' e u ψ h.w z = 0 := by
  have h' : ∀ x : PrimeSpectrum D, ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧
      x ∈ Set.range (PrimeSpectrum.comap e.hom) ∧
      ∃ (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ), RP q i n φ' e u ψ h.w z = 0 := by
    intro x
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts x.asIdeal x.isPrime
    obtain ⟨E, e, s, Z, u, ψ, h, he, hes, h0⟩ := relAt hB1 q i n φ' (unit_of d hq) o hIE
      (fun Z u ψ h => hBC Z (w ≫ u) ψ (hpo.paste_vert h)) z hz
    refine ⟨E, e, he, ⟨⟨Q.comap s.hom, inferInstance⟩, PrimeSpectrum.ext ?_⟩, Z, u, ψ, h, h0⟩
    change (Q.comap s.hom).comap e.hom = _
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, hes, hQr]
  choose E e he hx hY using h'
  obtain ⟨s, hs⟩ := LateralTheory.E.KillCokPf.Lem.finite_subcover E e he hx
  refine ⟨_, piMap (fun k : s => E k.1) (fun k => e k.1), _, _, _, IsPushout.of_hasPushout _ _,
    LateralTheory.E.KillCokPf.Glue.et_pi _ _ (fun k => he k.1), sps_pi _ _ fun x => ?_,
    rel_pi hC q i n φ' _ _ z (fun k => hY k.1) _ _ (IsPushout.of_hasPushout _ _)⟩
  obtain ⟨r, hr, hxr⟩ := hs x
  exact ⟨⟨r, hr⟩, hxr⟩

end LateralTheory.E.KernelLocalization
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut

namespace LateralTheory.E.KernelLocalization

theorem KerLoc_of (hC : Coprod) (hD : LateralTheory.E.TruncationKernel.RelDesc) : KerLoc := by
  intro hH q _ i n A Y φ hq P hpush het hlow _ D d hPD hpts Y' w φ' hpo
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨z, rfl⟩ := relExact _ _ _ n x hx
  obtain ⟨E, e, Z, u, ψ, h, he, hs, h0⟩ := relKill hH.2.2.2.2.2.2.1 hC q i n φ hq d hpts w φ' hpo z hx
  have hz : z = 0 := (injective_iff_map_eq_zero _).1
    (hD hH q i n φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Z u ψ he hs (het d e hPD he) h) z h0
  rw [hz, map_zero]

end LateralTheory.E.KernelLocalization
end
end
