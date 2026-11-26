module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
open scoped BigOperators

namespace GlobalTheory

open Matrix in
theorem det_ne_zero_of_intertwines_of_span_eq_top {k : Type} [Field k] {G : Type} {r : ℕ}
    (M N : G → Matrix (Fin r) (Fin r) k) (hM : Submodule.span k (Set.range M) = ⊤)
    (B : Matrix (Fin r) (Fin r) k) (i j : Fin r) (hB : B i j ≠ 0)
    (h : ∀ g, N g * B = B * M g) : B.det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hall : ∀ X : Matrix (Fin r) (Fin r) k, ∃ Y, Y * B = B * X := by
    intro X
    have hle : Submodule.span k (Set.range M) ≤
        (LinearMap.range (LinearMap.mulRight k B)).comap (LinearMap.mulLeft k B) := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mem_range]
      exact ⟨N g, by simp [h g]⟩
    have hX := hle (hM ▸ Submodule.mem_top : X ∈ Submodule.span k (Set.range M))
    rw [Submodule.mem_comap, LinearMap.mem_range] at hX
    obtain ⟨Y, hY⟩ := hX
    exact ⟨Y, by simpa using hY⟩
  obtain ⟨c, hc⟩ : ∃ c, v c ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hv0 (funext hne)
  let X : Matrix (Fin r) (Fin r) k :=
    Matrix.of fun a b => if a = j then (if b = c then (v c)⁻¹ else 0) else 0
  have hXv : X *ᵥ v = Pi.single j 1 := by
    ext a
    by_cases ha : a = j
    · subst ha
      simp [X, Matrix.mulVec, dotProduct, hc]
    · simp [X, Matrix.mulVec, dotProduct, ha]
  obtain ⟨Y, hY⟩ := hall X
  have key : B *ᵥ (X *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← hY, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hi := congrFun key i
  rw [hXv] at hi
  simp [Matrix.mulVec, dotProduct, Pi.single_apply] at hi
  exact hB hi

theorem exists_gl_intertwiner_of_residual_span_eq_top :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (G : Type) [Group G] (r : ℕ) (ρ ρ' : G →* Matrix.GeneralLinearGroup (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∃ A : Matrix (Fin r) (Fin r) O, A.det ≠ 0 ∧ ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * A = A * ρ g) → ∃ U : Matrix.GeneralLinearGroup (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  intro O _ _ _ G _ r ρ ρ' hspan ⟨A, hdet, hA⟩
  by_cases hr : r = 0
  · subst hr
    exact ⟨1, fun g => Units.ext (Matrix.ext fun a _ => a.elim0)⟩
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero hr⟩⟩
  obtain ⟨p, -, hp⟩ := Finset.exists_min_image Finset.univ
    (fun q : Fin r × Fin r => IsDiscreteValuationRing.addVal O (A q.1 q.2)) Finset.univ_nonempty
  have hdvd : ∀ x y, A p.1 p.2 ∣ A x y := fun x y =>
    IsDiscreteValuationRing.addVal_le_iff_dvd.mp (hp (x, y) (Finset.mem_univ _))
  have hd : A p.1 p.2 ≠ 0 := by
    intro h0
    apply hdet
    have hA0 : A = 0 := by
      ext x y
      have hxy := hdvd x y
      rw [h0, zero_dvd_iff] at hxy
      simpa using hxy
    rw [hA0, Matrix.det_zero]
  choose C hC using hdvd
  generalize hdd : A p.1 p.2 = d at hC hd
  have hC1 : C p.1 p.2 = 1 :=
    mul_left_cancel₀ hd (((hC p.1 p.2).symm.trans hdd).trans (mul_one d).symm)
  have hAeq : A = d • Matrix.of C := by
    ext x y
    rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← hC]
  have hint : ∀ g, (ρ' g : Matrix (Fin r) (Fin r) O) * Matrix.of C =
      Matrix.of C * (ρ g : Matrix (Fin r) (Fin r) O) := by
    intro g
    have h1 := hA g
    rw [hAeq, Matrix.mul_smul, Matrix.smul_mul] at h1
    ext x y
    have hxy := congrFun (congrFun h1 x) y
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at hxy
    exact mul_left_cancel₀ hd hxy
  have hB : (Matrix.of C).map (IsLocalRing.residue O) p.1 p.2 ≠ 0 := by
    rw [Matrix.map_apply, Matrix.of_apply, hC1, map_one]
    exact one_ne_zero
  have hdet' := det_ne_zero_of_intertwines_of_span_eq_top
    (fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O))
    (fun g => (ρ' g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) hspan
    ((Matrix.of C).map (IsLocalRing.residue O)) p.1 p.2 hB
    (fun g => by rw [← Matrix.map_mul, ← Matrix.map_mul, hint g])
  have hunit : IsUnit (Matrix.of C).det := by
    by_contra hu
    apply hdet'
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).mpr hunit).unit, fun g => ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, IsUnit.unit_spec, hint g]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
noncomputable section

namespace GlobalTheory.ShapeNeg

variable {O : Type} [CommRing O] (M : Type) [AddCommGroup M] [Module O M]

def Lev (c : O) : Type := ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M))

variable {M}

instance (c : O) : AddCommGroup (Lev M c) := inferInstanceAs (AddCommGroup ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))
instance (c : O) : Module O (Lev M c) := inferInstanceAs (Module O ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))
instance (c : O) : TopologicalSpace (Lev M c) := ⊥
instance (c : O) : DiscreteTopology (Lev M c) := ⟨rfl⟩
instance (c : O) : IsTopologicalAddGroup (Lev M c) where
  continuous_add := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

def Lev.val {c : O} (x : Lev M c) : M :=
  Subtype.val (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) x

theorem Lev.smul_val {c : O} (x : Lev M c) : c • x.val = 0 := by
  have hx := LinearMap.mem_ker.1
    (Subtype.property (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) x)
  exact hx

@[ext] theorem Lev.ext {c : O} {x y : Lev M c} (h : x.val = y.val) : x = y := by
  exact Subtype.ext (p := fun m => m ∈ LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) h

theorem Lev.val_add {c : O} (x y : Lev M c) : (x + y).val = x.val + y.val := rfl
theorem Lev.val_smul {c : O} (a : O) (x : Lev M c) : (a • x).val = a • x.val := rfl
theorem Lev.val_zero {c : O} : (0 : Lev M c).val = 0 := rfl

def Lev.mk {c : O} (m : M) (h : c • m = 0) : Lev M c :=
  (⟨m, by simpa using h⟩ : ↥(LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)))

theorem Lev.val_mk {c : O} (m : M) (h : c • m = 0) : (Lev.mk m h).val = m := rfl

variable {G : Type} [Group G]

def levRep (ρ : Representation O G M) (c : O) : Representation O G (Lev M c) where
  toFun g :=
    { toFun := fun x => Lev.mk (ρ g x.val) (by rw [← map_smul, Lev.smul_val, map_zero])
      map_add' := fun x y => Lev.ext (by
        simpa only [Lev.val_mk, Lev.val_add] using map_add (ρ g) x.val y.val)
      map_smul' := fun a x => Lev.ext (by
        simpa only [Lev.val_mk, Lev.val_smul] using map_smulₛₗ (ρ g) a x.val) }
  map_one' := LinearMap.ext fun x => Lev.ext
    (congrArg (fun f : Module.End O M => f x.val) (map_one ρ))
  map_mul' g h := LinearMap.ext fun x => Lev.ext
    (congrArg (fun f : Module.End O M => f x.val) (map_mul ρ g h))

theorem levRep_val (ρ : Representation O G M) (c : O) (g : G) (x : Lev M c) :
    (levRep ρ c g x).val = ρ g x.val := rfl

abbrev levZ (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c}) :
    Module (ZMod (p ^ r)) (Lev M c) :=
  AddCommGroup.zmodModule (fun x => by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
    apply Lev.ext
    show ((p ^ r : ℕ) • x.val) = 0
    rw [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow, ← ha, mul_smul, Lev.smul_val, smul_zero])

def levRepZ (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (ρ : Representation O G M) :
    @Representation (ZMod (p ^ r)) G (Lev M c) _ _ _ (levZ p r h) :=
  letI := levZ (M := M) p r h
  { toFun := fun g => (levRep ρ c g).toAddMonoidHom.toZModLinearMap (p ^ r)
    map_one' := LinearMap.ext fun x =>
      congrArg (fun f : Module.End O (Lev M c) => f x) (map_one (levRep ρ c))
    map_mul' := fun g g' => LinearMap.ext fun x =>
      congrArg (fun f : Module.End O (Lev M c) => f x) (map_mul (levRep ρ c) g g') }

theorem levRepZ_apply (p r : ℕ) [NeZero (p ^ r)] {c : O} (h : ((p : O) ^ r) ∈ Ideal.span {c})
    (ρ : Representation O G M) (g : G) (x : Lev M c) :
    levRepZ p r h ρ g x = levRep ρ c g x := rfl

end GlobalTheory.ShapeNeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
noncomputable section

open PowerSeries

namespace GlobalTheory.NB.LT

def F (R : Type) [CommRing R] (l : ℕ) : Polynomial R :=
  Polynomial.X * (Polynomial.X + Polynomial.C (l : R)) ^ (l - 1)

abbrev EE (R : Type) [CommRing R] (l : ℕ) : Type :=
  AdicCompletion (Ideal.span {(l : Localization.Away (X : R⟦X⟧))}) (Localization.Away (X : R⟦X⟧))

variable {R S : Type} [CommRing R] [CommRing S] {l : ℕ}

private lemma subsingleton_of_isHausdorff_whole_ideal {I : Ideal R} [IsHausdorff I R] (h : I = ⊤) :
    Subsingleton R := by
  subst h
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : R, z = 0 := fun z =>
    IsHausdorff.haus ‹_› z fun n => by simp [Ideal.top_pow, SModEq.top]
  rw [key x, key y]

private lemma order_map_toNat_eq_natDegree_of_isDistinguishedAt {I : Ideal R} {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (hI : I ≠ ⊤) :
    ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat = p.natDegree := by
  have h1 : constantCoeff (1 : R⟦X⟧) ∉ I := by
    simpa [Ideal.eq_top_iff_one] using hI
  have := H.coe_natDegree_eq_order_map (p : R⟦X⟧) 1 h1 (by simp)
  rw [← this]
  simp

theorem _root_.GlobalTheory.NB.LT.exists_poly_mod [Nontrivial R] {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) (a : R⟦X⟧) :
    ∃ r : Polynomial R, r.degree < p.degree ∧ (p : R⟦X⟧) ∣ a - r := by
  have hI : I ≠ ⊤ := by
    intro h
    have := subsingleton_of_isHausdorff_whole_ideal (I := I) h
    exact not_subsingleton R this
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hd := D.isWeierstrassDivisionAt_div_mod a
  refine ⟨D.mod a, ?_, D.div a, sub_eq_iff_eq_add.mpr hd.eq_mul_add⟩
  have hlt := hd.degree_lt
  rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI] at hlt
  rwa [Polynomial.degree_eq_natDegree (Polynomial.Monic.ne_zero H.monic)]

theorem _root_.GlobalTheory.NB.LT.poly_dvd_of_dvd {I : Ideal R} [IsAdicComplete I R] {p : Polynomial R}
    (H : p.IsDistinguishedAt I) {r : Polynomial R} (h : (p : R⟦X⟧) ∣ (r : R⟦X⟧)) : p ∣ r := by
  by_cases hI : I = ⊤
  · have := subsingleton_of_isHausdorff_whole_ideal (I := I) hI
    rw [Subsingleton.elim r 0]
    exact dvd_zero p
  have hm := H.monic
  obtain ⟨h, hh⟩ := h
  have D := H.isWeierstrassDivisorAt' (I := I)
  have hdeg : (r %ₘ p).degree < ((map (Ideal.Quotient.mk I)) (p : R⟦X⟧)).order.toNat := by
    rw [order_map_toNat_eq_natDegree_of_isDistinguishedAt H hI]
    by_cases hs : Nontrivial R
    · exact (Polynomial.degree_modByMonic_lt r hm).trans_le Polynomial.degree_le_natDegree
    · rw [not_nontrivial_iff_subsingleton] at hs
      rw [Subsingleton.elim (r %ₘ p) 0]
      simp
  have hmul : (p : R⟦X⟧) * (h - ((r /ₘ p : Polynomial R) : R⟦X⟧)) = ((r %ₘ p : Polynomial R) : R⟦X⟧) := by
    have e := Polynomial.modByMonic_add_div r p
    have e' : ((r %ₘ p : Polynomial R) : R⟦X⟧) + (p : R⟦X⟧) * ((r /ₘ p : Polynomial R) : R⟦X⟧)
        = (r : R⟦X⟧) := by
      rw [← Polynomial.coe_mul, ← Polynomial.coe_add, e]
    rw [mul_sub, ← hh, ← e']
    ring
  have := (D.eq_zero_of_mul_eq hdeg hmul).2
  exact (Polynomial.modByMonic_eq_zero_iff_dvd hm).mp this

theorem _root_.GlobalTheory.NB.LT.algHom_coe {B : Type} [CommRing B] [Algebra R B] (σ : R⟦X⟧ →ₐ[R] B) (r : Polynomial R) :
    σ (r : R⟦X⟧) = Polynomial.aeval (σ X) r := by
  have e : σ.comp (Polynomial.coeToPowerSeries.algHom R) = Polynomial.aeval (σ X) :=
    Polynomial.algHom_ext (by simp)
  simpa using DFunLike.congr_fun e r

private lemma X_pow_dvd_sub_aeval_trunc (ρ : R⟦X⟧ →ₐ[R] R⟦X⟧) (hρ : X ∣ ρ X) (n : ℕ)
    (f : R⟦X⟧) : X ^ n ∣ ρ f - Polynomial.aeval (ρ X) (trunc n f) := by
  obtain ⟨g, hg⟩ : X ^ n ∣ f - (trunc n f : R⟦X⟧) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [coeff_trunc, hm]
  have e : ρ f - Polynomial.aeval (ρ X) (trunc n f) = ρ (X ^ n) * ρ g := by
    rw [← _root_.GlobalTheory.NB.LT.algHom_coe ρ, ← map_sub, hg, map_mul]
  rw [e, map_pow]
  exact (pow_dvd_pow_of_dvd hρ n).mul_right _

theorem _root_.GlobalTheory.NB.LT.algHom_ext_X (σ τ : R⟦X⟧ →ₐ[R] R⟦X⟧) (h : σ X = τ X) (hX : X ∣ σ X) : σ = τ := by
  refine AlgHom.ext fun f => PowerSeries.ext fun m => ?_
  have h1 := X_pow_dvd_sub_aeval_trunc σ hX (m + 1) f
  have h2 := X_pow_dvd_sub_aeval_trunc τ (h ▸ hX) (m + 1) f
  rw [h] at h1
  have h3 := dvd_sub h1 h2
  rw [sub_sub_sub_cancel_right] at h3
  have := (X_pow_dvd_iff.mp h3) m (Nat.lt_succ_self m)
  rwa [map_sub, sub_eq_zero] at this

end GlobalTheory.NB.LT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockIsTheRun
namespace GlobalTheory

theorem block_is_the_run : ∀ (n p t : ℕ) (a : ℕ → ℤ) (c : ℤ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    p + t ≤ n → p < t → n - (p + t) < t → (∀ j, p ≤ j → j < p + t → a j = a p) →
    (1 ≤ p → a p < a (p - 1)) → (p + t < n → a (p + t) < a p) →
    (∀ i < t, ∃ j < n, a j - j = c - i) → c = a p - p := by
  intro n p t a c hmono hpt hpt' hn hrun hleft hright hwin
  obtain ⟨j0, hj0n, hj0⟩ := hwin 0 (by omega)

  have key : ∀ i, i < t → j0 + i < n ∧ a (j0 + i) = a j0 := by
    intro i
    induction i with
    | zero => intro _; simpa using hj0n
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨j, hjn, hj⟩ := hwin (i + 1) hi
      push_cast at hj hj0
      have hge : j0 + i + 1 ≤ j := by
        by_contra hlt
        have := hmono j (j0 + i) (by omega) h1
        omega
      have hle := hmono (j0 + i) j (by omega) hjn
      have hj' : j = j0 + i + 1 := by omega
      refine ⟨by omega, ?_⟩
      rw [show j0 + (i + 1) = j by omega]
      omega
  have hq := (key (t - 1) (by omega)).1
  have hconst : ∀ k, j0 ≤ k → k < j0 + t → a k = a j0 := by
    intro k h1 h2
    have := (key (k - j0) (by omega)).2
    rwa [show j0 + (k - j0) = k by omega] at this
  rcases lt_trichotomy j0 p with h | h | h
  ·
    exfalso
    have e1 := hconst (p - 1) (by omega) (by omega)
    have e2 := hconst p (by omega) (by omega)
    have := hleft (by omega)
    omega
  · subst h
    push_cast at hj0
    omega
  ·
    exfalso
    have e1 := hconst (p + t - 1) (by omega) (by omega)
    have e2 := hconst (p + t) (by omega) (by omega)
    have e3 := hrun (p + t - 1) (by omega) (by omega)
    have := hright (by omega)
    omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProd
namespace GlobalTheory

theorem finsupp_vanishing_on_equiv_compl_prod :
    ∀ {I : Type} (S : Finset I) (n : ℕ),
    ∃ e : {l : I →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0} ≃ ({i : I // i ∉ S} →₀ (Fin n → ℤ)),
      ∀ (M : Type) [CommMonoid M] (r : I → (Fin n → ℤ) → M), (∀ i, r i 0 = 1) →
        ∀ l, (e l).prod (fun i v => r i.1 v) = l.1.prod r := by
  intro I S n
  classical
  refine ⟨{
    toFun := fun l => l.1.subtypeDomain (· ∉ S)
    invFun := fun l' => ⟨l'.embDomain (Function.Embedding.subtype _), by
      intro v hv
      apply Finsupp.embDomain_notin_range
      rintro ⟨i, rfl⟩
      exact i.2 hv⟩
    left_inv := by
      rintro ⟨l, hl⟩
      apply Subtype.ext
      refine Finsupp.ext fun v => ?_
      by_cases hv : v ∈ S
      · show Finsupp.embDomain _ _ v = l v
        rw [Finsupp.embDomain_notin_range, hl v hv]
        rintro ⟨i, rfl⟩
        exact i.2 hv
      · show Finsupp.embDomain _ _ v = l v
        have := Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∉ S))
          (l.subtypeDomain (· ∉ S)) ⟨v, hv⟩
        simpa using this
    right_inv := by
      intro l'
      refine Finsupp.ext fun i => ?_
      rw [Finsupp.subtypeDomain_apply]
      exact Finsupp.embDomain_apply_self (Function.Embedding.subtype (· ∉ S)) l' i }, ?_⟩
  intro M _ r _ l
  obtain ⟨l, hl⟩ := l
  show (l.subtypeDomain (· ∉ S)).prod (fun i v => r i.1 v) = l.prod r
  apply Finsupp.prod_subtypeDomain_index
  intro x hx hxS
  exact (Finsupp.mem_support_iff.mp hx) (hl x hxS)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProdStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_finsupp_compl_prod_eq : ∀ {I : Type} (S : Finset I) (n : ℕ),
    ∃ e : {l : I →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0} ≃ ({i : I // i ∉ S} →₀ (Fin n → ℤ)),
      ∀ (M : Type) [CommMonoid M] (r : I → (Fin n → ℤ) → M), (∀ i, r i 0 = 1) →
        ∀ l, (e l).prod (fun i v => r i.1 v) = l.1.prod r := by
  first | exact @GlobalTheory.finsupp_vanishing_on_equiv_compl_prod | exact GlobalTheory.finsupp_vanishing_on_equiv_compl_prod | (intros; apply GlobalTheory.finsupp_vanishing_on_equiv_compl_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorProductBasisCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorProductBasisCoordinates
open TensorProduct Module

theorem GlobalTheory.tensorBasisCoords : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by
  intro F _ B _ _ V _ _ n _ _ b
  let e : V ⊗[F] B ≃ₗ[F] (n → B) :=
    (TensorProduct.comm F V B) ≪≫ₗ (TensorProduct.congr (LinearEquiv.refl F B) b.equivFun) ≪≫ₗ
      TensorProduct.piScalarRight F F B n
  have h1 : ∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x := by
    intro v x i
    simp [e, TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  have hadd : ∀ y z : V ⊗[F] B, e (y + z) = e y + e z := fun y z => map_add e y z
  refine ⟨e, h1, ?_, ?_⟩
  · intro y
    rw [LinearEquiv.symm_apply_eq]
    funext j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    simp only [h1, Basis.repr_self, Finsupp.single_apply]
    simp
  · intro r f y
    induction y using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      rw [show (fun _ : n => f ((0 : n → B) _)) = 0 from by funext i; simp, Matrix.mulVec_zero]
    | tmul v x =>
      funext i
      rw [TensorProduct.map_tmul, h1]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, LinearMap.toMatrix_apply, h1, map_smul]
      simp_rw [← Algebra.smul_def, smul_smul]
      rw [← Finset.sum_smul]
      congr 1
      conv_lhs => rw [← b.sum_repr v]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Finsupp.finsetSum_apply]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    | add y z hy hz =>
      rw [map_add (f := _), hadd, hy, hz, hadd, ← Matrix.mulVec_add]
      congr 1
      funext i
      simp [map_add (f := _)]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorProductBasisCoordinatesStatement
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorProduct_basis_coordinates : ∀ (F : Type) [Field F] (B : Type) [CommRing B] [Algebra F B] (V : Type) [AddCommGroup V] [Module F V] (n : Type) [Fintype n] [DecidableEq n] (b : Basis n F V), ∃ e : V ⊗[F] B ≃ₗ[F] (n → B), (∀ v x i, e (v ⊗ₜ[F] x) i = b.repr v i • x) ∧ (∀ y : n → B, e.symm y = ∑ i, b i ⊗ₜ[F] y i) ∧ ∀ (r : V →ₗ[F] V) (f : B →ₗ[F] B) (y : V ⊗[F] B), e (TensorProduct.map r f y) = ((LinearMap.toMatrix b b r).map (algebraMap F B)).mulVec (fun i => f (e y i)) := by
  first | exact @GlobalTheory.tensorBasisCoords | exact GlobalTheory.tensorBasisCoords | (intros; apply GlobalTheory.tensorBasisCoords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralPi
namespace GlobalTheory.IntegralPi

open Polynomial

theorem isIntegral_pi {O : Type} [CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [∀ i, CommRing (R i)] [∀ i, Algebra O (R i)] (x : ∀ i, R i)
    (hx : ∀ i, IsIntegral O (x i)) : IsIntegral O x := by
  classical
  haveI := Fintype.ofFinite ι
  choose p hpm hp using hx
  refine ⟨∏ i, p i, monic_prod_of_monic _ _ (fun i _ => hpm i), ?_⟩
  rw [← aeval_def]
  funext j
  have key : (aeval x (∏ i, p i)) j = aeval (x j) (∏ i, p i) := by
    have := (aeval_algHom_apply (Pi.evalAlgHom O R j) x (∏ i, p i)).symm
    simpa using this
  rw [key, map_prod, Pi.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [aeval_def]; exact hp j)

theorem main : ∀ {O : Type} [inst : CommRing O] {ι : Type} [Finite ι] {R : ι → Type}
    [inst_2 : (i : ι) → CommRing (R i)] [inst_3 : (i : ι) → Algebra O (R i)] (x : (i : ι) → R i),
    (∀ (i : ι), IsIntegral O (x i)) → IsIntegral O x :=
  fun x hx => isIntegral_pi x hx

end GlobalTheory.IntegralPi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTwistedNorm
open Polynomial

namespace GlobalTheory

theorem antidiag_twisted_norm : ∀ (E : Type) [Field E] (c : E ≃+* E), (∀ x, c (c x) = x) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) E), Φ = Matrix.of (fun i j : Fin a => if j = i.rev then (-1 : E) ^ (i : ℕ) else 0) → Φ.transpose = (-1 : E) ^ (a - 1) • Φ ∧ IsUnit Φ.det ∧ ∀ δ : Matrix (Fin a) (Fin a) E, IsUnit δ.det → δ * (Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹) = (-1 : E) ^ (a - 1) • ((δ * Φ) * (((δ * Φ).map c).transpose)⁻¹) ∧ Φ * (((Φ * ((δ.map c).transpose)⁻¹ * Φ⁻¹).map c).transpose)⁻¹ * Φ⁻¹ = δ := by
  intro E _ c hc a Φ hΦ
  have hpm : ∀ n : ℕ, (-1 : E) ^ n * (-1 : E) ^ n = 1 := by
    intro n; rw [← mul_pow]; simp
  have hss : (-1 : E) ^ (a - 1) * (-1 : E) ^ (a - 1) = 1 := hpm _
  have hsign : ∀ i : Fin a, (-1 : E) ^ (i.rev : ℕ) = (-1 : E) ^ (a - 1) * (-1 : E) ^ (i : ℕ) := by
    intro i
    have hi := i.isLt
    rw [Fin.val_rev, ← pow_add]
    have : a - 1 + (i:ℕ) = (a - ((i:ℕ) + 1)) + 2 * (i:ℕ) := by omega
    rw [this, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  have hT : Φ.transpose = (-1 : E) ^ (a - 1) • Φ := by
    subst hΦ
    ext i j
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : j = i.rev
    · subst h
      simp only [Fin.rev_rev, if_true]
      exact hsign i
    · have h' : ¬ i = j.rev := by
        intro h2; apply h; rw [h2, Fin.rev_rev]
      simp [h, h']
  have hsq : Φ * Φ = (-1 : E) ^ (a - 1) • (1 : Matrix (Fin a) (Fin a) E) := by
    subst hΦ
    ext i k
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i.rev]
    · by_cases h : k = i
      · subst h
        simp only [Fin.rev_rev, if_true, hsign]
        rw [mul_one, mul_left_comm, hpm, mul_one]
      · have : ¬ k = i.rev.rev := by rwa [Fin.rev_rev]
        simp [this, h, Ne.symm h]
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hright : Φ * Φ.transpose = 1 := by
    rw [hT, Matrix.mul_smul, hsq, smul_smul, hss, one_smul]
  have hleft : Φ.transpose * Φ = 1 := by
    rw [hT, Matrix.smul_mul, hsq, smul_smul, hss, one_smul]
  have hinv : Φ⁻¹ = Φ.transpose := Matrix.inv_eq_left_inv hleft
  have hTinv : (Φ.transpose)⁻¹ = Φ := Matrix.inv_eq_left_inv hright
  have hdet : IsUnit Φ.det := Matrix.isUnit_det_of_left_inverse hleft
  have hΦc : Φ.map c = Φ := by
    subst hΦ
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hmapmul : ∀ A B : Matrix (Fin a) (Fin a) E, (A * B).map c = A.map c * B.map c :=
    fun A B => Matrix.map_mul (f := (c : E →+* E))
  have hmapinv : ∀ A : Matrix (Fin a) (Fin a) E, IsUnit A.det → (A⁻¹).map c = (A.map c)⁻¹ := by
    intro A hA
    refine (Matrix.inv_eq_left_inv ?_).symm
    rw [← hmapmul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ c.map_zero c.map_one]
  have hcc : ∀ A : Matrix (Fin a) (Fin a) E, (A.map c).map c = A := by
    intro A; ext i j; simp [hc]
  refine ⟨hT, hdet, fun δ hδ => ⟨?_, ?_⟩⟩
  · rw [hmapmul, hΦc, Matrix.transpose_mul, Matrix.mul_inv_rev, hTinv, hinv, hT]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  · have hYd : IsUnit ((δ.map c).transpose).det := by
      rw [Matrix.det_transpose]
      have h1 := RingHom.map_det (c : E →+* E) δ
      rw [RingHom.mapMatrix_apply] at h1
      have h2 : (δ.map c).det = c δ.det := h1.symm
      rw [h2]; exact hδ.map c
    have hΦTc : (Φ.transpose).map c = Φ.transpose := by rw [Matrix.transpose_map, hΦc]
    rw [hinv, hmapmul, hmapmul, hΦc, hΦTc, hmapinv _ hYd,
      Matrix.transpose_map, hcc, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose,
      Matrix.mul_inv_rev, Matrix.mul_inv_rev, hTinv, Matrix.nonsing_inv_nonsing_inv _ hδ, hinv]
    have e : Φ * (Φ * δ * Φ.transpose) * Φ.transpose = (Φ * Φ) * δ * (Φ.transpose * Φ.transpose) := by
      simp only [Matrix.mul_assoc]
    rw [e, ← Matrix.transpose_mul, hsq, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hss, one_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjoint
open Polynomial

namespace GlobalTheory.GalDisj

section
variable {k M F D : Type*} [Field k] [Field M] [Field F] [Field D] [Algebra k M] [Algebra k F]
  [Algebra k D] [Algebra M D] [Algebra F D] [IsScalarTower k M D] [IsScalarTower k F D]

end

private theorem natDegree_minpoly_le_natDegree_minpoly_map {k Ω D : Type} [Field k] [Field Ω] [Field D]
    [Algebra k Ω] (o : Ω →+* D) (F : Subfield D)
    (hF : ∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) (α : Ω) (hα : IsIntegral k α)
    (hsplit : ((minpoly k α).map (algebraMap k Ω)).Splits) :
    (minpoly k α).natDegree ≤ (minpoly F (o α)).natDegree := by
  set ψ : k →+* F := (o.comp (algebraMap k Ω)).codRestrict F (fun c => (hF _).2 ⟨c, rfl⟩)
  have hcomp : F.subtype.comp ψ = o.comp (algebraMap k Ω) := by ext; rfl
  have hcomp' : (algebraMap F D).comp ψ = o.comp (algebraMap k Ω) := by ext; rfl
  have hmon : ((minpoly k α).map ψ).Monic := (minpoly.monic hα).map ψ
  have hroot : aeval (o α) ((minpoly k α).map ψ) = 0 := by
    rw [aeval_def, eval₂_map, hcomp', ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hβ : IsIntegral F (o α) := ⟨_, hmon, hroot⟩
  have hdvd : minpoly F (o α) ∣ (minpoly k α).map ψ := minpoly.dvd F _ hroot
  have hP : ((minpoly k α).map ψ).map F.subtype = ((minpoly k α).map (algebraMap k Ω)).map o := by
    rw [map_map, map_map, hcomp]
  have hP0 : ((minpoly k α).map ψ).map F.subtype ≠ 0 := (hmon.map _).ne_zero
  have hGdvd : (minpoly F (o α)).map F.subtype ∣ ((minpoly k α).map ψ).map F.subtype :=
    Polynomial.map_dvd _ hdvd
  have hGs : ((minpoly F (o α)).map F.subtype).Splits := by
    refine Splits.of_dvd ?_ hP0 hGdvd
    rw [hP]
    exact hsplit.map o
  have hGm : ((minpoly F (o α)).map F.subtype).Monic := (minpoly.monic hβ).map _
  have hlift : (minpoly F (o α)).map F.subtype ∈ lifts o := by
    refine hGs.mem_lift_of_roots_mem_range hGm o fun a ha => ?_
    have h1 := Multiset.mem_of_le (Polynomial.roots.le_of_dvd hP0 hGdvd) ha
    rw [hP, hsplit.roots_map o] at h1
    obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 h1
    exact ⟨r, rfl⟩
  have hlift' : (minpoly F (o α)).map F.subtype ∈ lifts (o.comp (algebraMap k Ω)) := by
    rw [lifts_iff_coeff_lifts] at hlift ⊢
    intro n
    obtain ⟨y, hy⟩ := hlift n
    have hyF : o y ∈ F := by
      rw [hy, coeff_map]
      exact ((minpoly F (o α)).coeff n).2
    obtain ⟨c, rfl⟩ := (hF y).1 hyF
    exact ⟨c, hy⟩
  obtain ⟨g, hg⟩ := (mem_lifts _).1 hlift'
  have hinj : Function.Injective (o.comp (algebraMap k Ω)) := RingHom.injective _
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Polynomial.map_zero] at hg
    exact hGm.ne_zero hg.symm
  have hgα : aeval α g = 0 := by
    apply o.injective
    rw [map_zero, aeval_def, hom_eval₂, ← eval_map, hg, eval_map]
    exact minpoly.aeval F (o α)
  calc (minpoly k α).natDegree ≤ g.natDegree := natDegree_le_of_dvd (minpoly.dvd k α hgα) hg0
    _ = ((minpoly F (o α)).map F.subtype).natDegree := by
        rw [← hg, natDegree_map_eq_of_injective hinj]
    _ = (minpoly F (o α)).natDegree := natDegree_map_eq_of_injective (RingHom.injective _) _

theorem _root_.GlobalTheory.GalDisj.galois_linearDisjoint : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  intro k Ω D _ _ _ _ _ o F hF m x hx b hb hsum
  classical
  set M := IntermediateField.adjoin k (Set.range x)
  haveI : FiniteDimensional k M :=
    IntermediateField.finiteDimensional_adjoin fun y _ => Algebra.IsIntegral.isIntegral y
  obtain ⟨α', hα'⟩ := Field.exists_primitive_element k M
  set α : Ω := (α' : Ω) with hαdef
  have hxα : ∀ i, x i ∈ IntermediateField.adjoin k {α} := by
    intro i
    have h1 : (IntermediateField.adjoin k {α'}).map M.val = IntermediateField.adjoin k {α} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]; rfl
    rw [← h1, hα']
    exact ⟨⟨x i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩, trivial, rfl⟩
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim ≤ (minpoly F (o α)).natDegree := by
    rw [IntermediateField.adjoin.powerBasis_dim]
    exact natDegree_minpoly_le_natDegree_minpoly_map o F hF α hint (IsGalois.splits k α)
  have hli : LinearIndependent F (fun j : Fin pb.dim => o α ^ (j : ℕ)) :=
    (linearIndependent_pow (o α)).comp (Fin.castLE hdim) (Fin.castLE_injective hdim)
  set c : Fin m → Fin pb.dim → k := fun i j => pb.basis.repr ⟨x i, hxα i⟩ j
  have hexp : ∀ i, x i = ∑ j, c i j • α ^ (j : ℕ) := by
    intro i
    have h := congrArg Subtype.val (pb.basis.sum_repr ⟨x i, hxα i⟩)
    refine h.symm.trans ?_
    simp [c, pb, IntermediateField.adjoin.powerBasis_gen]
  have hd : ∀ j, ∑ i, o (algebraMap k Ω (c i j)) * b i = 0 := by
    have hmem : ∀ j, ∑ i, o (algebraMap k Ω (c i j)) * b i ∈ F := fun j =>
      F.sum_mem fun i _ => F.mul_mem ((hF _).2 ⟨_, rfl⟩) (hb i)
    intro j
    have := Fintype.linearIndependent_iff.1 hli (fun j => ⟨_, hmem j⟩) ?_ j
    · exact congrArg Subtype.val this
    rw [← hsum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hexp, Subfield.smul_def, map_sum, map_smul, Algebra.smul_def, map_mul, map_pow,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (∑ i, o (algebraMap k Ω (c i j)) * b i) * o α ^ (j : ℕ) = _
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  obtain ⟨g, hg⟩ := LinearMap.exists_extend hx.repr
  have hgx : ∀ i, g (x i) = Finsupp.single i 1 := by
    intro i
    have := LinearMap.congr_fun hg ⟨x i, Submodule.subset_span ⟨i, rfl⟩⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
    rw [this, hx.repr_eq_single i _ rfl]
  intro l
  calc b l = ∑ i, o (algebraMap k Ω (g (x i) l)) * b i := by
        simp [hgx, Finsupp.single_apply]
    _ = ∑ j : Fin pb.dim, o (algebraMap k Ω (g (α ^ (j : ℕ)) l)) *
          ∑ i, o (algebraMap k Ω (c i j)) * b i := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [hexp, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
          Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = 0 := by simp [hd]

end GlobalTheory.GalDisj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjointStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  first | exact @GlobalTheory.GalDisj.galois_linearDisjoint | exact GlobalTheory.GalDisj.galois_linearDisjoint | (intros; apply GlobalTheory.GalDisj.galois_linearDisjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCardAddMonoidHomZmodLe
namespace GlobalTheory

theorem natCard_addMonoidHom_zmod_le (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] [Finite A] :
    Nat.card (A →+ ZMod N) ≤ Nat.card A := by
  classical
  have : Fintype A := Fintype.ofFinite A

  have hinj : Function.Injective fun f : A →+ ZMod N ↦ (ZMod.stdAddChar (N := N)).compAddMonoidHom f :=
    AddChar.compAddMonoidHom_injective_right _ ZMod.injective_stdAddChar
  calc Nat.card (A →+ ZMod N) ≤ Nat.card (AddChar A ℂ) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card A := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfNodupSumMultisetOfEq
namespace GlobalTheory

theorem eq_of_nodup_sum_multiset_of_eq (ι : Type) [Fintype ι] [DecidableEq ι]
    (B : ι → Multiset ℂ) (h : (∑ i, B i).Nodup) (i j : ι) (hi : B i ≠ 0) (hij : B i = B j) :
    i = j := by
  by_contra hne
  have hle : B i + B j ≤ ∑ k, B k := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have hnd : (B i + B j).Nodup := Multiset.nodup_of_le hle h
  rw [← hij] at hnd
  obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hi
  exact Multiset.disjoint_left.1 (Multiset.nodup_add.1 hnd).2.2 ha ha

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLe
open Polynomial

namespace GlobalTheory

theorem norm_hasSum_sub_finset_sum_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by
  intro K _ _ ι f s I ε hε hs hf
  classical
  have h0 : Filter.Tendsto (fun J : Finset ι => ∑ i ∈ J, f i) Filter.atTop (nhds s) := hs
  have ht : Filter.Tendsto (fun J : Finset ι => ‖∑ i ∈ J, f i - ∑ i ∈ I, f i‖) Filter.atTop
      (nhds ‖s - ∑ i ∈ I, f i‖) :=
    (h0.sub tendsto_const_nhds).norm
  refine le_of_tendsto ht ?_
  filter_upwards [Filter.eventually_ge_atTop I] with J hJ
  rw [← Finset.sum_sdiff hJ, add_sub_cancel_right]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun i hi =>
    hf i (Finset.mem_sdiff.mp hi).2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormHasSumSubFinsetSumLeStatement
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by
  first | exact @GlobalTheory.norm_hasSum_sub_finset_sum_le | exact GlobalTheory.norm_hasSum_sub_finset_sum_le | (intros; apply GlobalTheory.norm_hasSum_sub_finset_sum_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteJumpsInfFiltration
namespace GlobalTheory

theorem finite_jumps_inf_filtration (E W : Type) [Field E] [AddCommGroup W] [Module E W]
    (D : Submodule E W) (F : ℤ → Submodule E W) (hD : Module.Finite E ↥D)
    (hF : ∀ a, F (a + 1) ≤ F a) :
    {a : ℤ | D ⊓ F (a + 1) ≠ D ⊓ F a}.Finite := by
  have hanti : Antitone F := antitone_int_of_succ_le hF
  have hfin : ∀ a, Module.Finite E ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le (S₂ := D) inf_le_left
  have key : ∀ a b : ℤ, D ⊓ F (a + 1) ≠ D ⊓ F a → a < b →
      Module.finrank E ↥(D ⊓ F b) < Module.finrank E ↥(D ⊓ F a) := by
    intro a b ha hab
    haveI := hfin a
    apply Submodule.finrank_lt_finrank_of_lt
    have h1 : D ⊓ F b ≤ D ⊓ F (a + 1) := inf_le_inf_left _ (hanti (by omega))
    have h2 : D ⊓ F (a + 1) < D ⊓ F a := lt_of_le_of_ne (inf_le_inf_left _ (hF a)) ha
    exact lt_of_le_of_lt h1 h2
  refine Set.Finite.of_injOn (f := fun a => Module.finrank E ↥(D ⊓ F a))
    (t := Set.Iic (Module.finrank E ↥D)) ?_ ?_ (Set.finite_Iic _)
  · intro a _
    exact Submodule.finrank_mono inf_le_left
  · intro a ha b hb hab
    rcases lt_trichotomy a b with h | h | h
    · exact absurd hab (key a b ha h).ne'
    · exact h
    · exact absurd hab (key b a hb h).ne

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntOfCompatibleZmodPow
namespace GlobalTheory

theorem exists_padicInt_of_compatible_zmod_pow :
    ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)),
      (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) →
      ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  intro p _ c hc
  let f : ∀ n : ℕ, Polynomial ℤ →+* ZMod (p ^ n) := fun n =>
    Polynomial.eval₂RingHom (Int.castRingHom _) (c n)
  have hf : ∀ (k₁ k₂ : ℕ) (hk : k₁ ≤ k₂),
      (ZMod.castHom (pow_dvd_pow p hk) (ZMod (p ^ k₁))).comp (f k₂) = f k₁ := by
    intro k₁ k₂ hk
    apply Polynomial.ringHom_ext
    · intro a
      simp [f]
    · simpa [f] using hc k₁ k₂ hk
  refine ⟨PadicInt.lift hf Polynomial.X, fun n => ?_⟩
  have h := congrArg (fun g : Polynomial ℤ →+* ZMod (p ^ n) => g Polynomial.X)
    (PadicInt.lift_spec hf n)
  simpa [f] using h

end GlobalTheory
end
