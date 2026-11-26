module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleChartGenericComparison
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleIntersectionSymmetry
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeFamilyInjectiveModelFacts

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XRootnumDual
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlagframeDual
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagframe_dual

theorem tri_inv {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {N : ℕ}
    (w u : Module.Basis (Fin N) Ω V) (h : ∀ i j, i < j → w.repr (u i) j = 0) :
    (∀ i j, i < j → u.repr (w i) j = 0) ∧ ∀ i, u.repr (w i) i = (w.repr (u i) i)⁻¹ := by
  have hM : (w.toMatrix u).BlockTriangular id := fun i j hij => h j i hij
  have hMN : w.toMatrix u * u.toMatrix w = 1 := Module.Basis.toMatrix_mul_toMatrix_flip w u
  haveI : Invertible (w.toMatrix u) := ⟨u.toMatrix w, Module.Basis.toMatrix_mul_toMatrix_flip u w, hMN⟩
  have hinv : (w.toMatrix u)⁻¹ = u.toMatrix w := Matrix.inv_eq_right_inv hMN
  have hN : (u.toMatrix w).BlockTriangular id := hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨fun i j hij => hN hij, fun i => ?_⟩
  have hii := congrFun (congrFun hMN i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at hii
  · simp only [Module.Basis.toMatrix_apply] at hii
    exact eq_inv_of_mul_eq_one_right hii
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hM hk, zero_mul]
    · rw [hN hk, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem repr_of_pair {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {N : ℕ} (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (w : Fin N → V) (w₁ : Module.Basis (Fin N) Ω V₁)
    (h : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) (y : V₁) (j : Fin N) :
    w₁.repr y j = β (w j.rev) y := by
  have hy := congrArg (β (w j.rev)) (w₁.sum_repr y)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hy
  simp only [map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.rev_inj] at hy
  rw [← hy]
  simp

theorem exists_dual {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {N : ℕ} (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (hβ : Function.Bijective β.flip) (u : Module.Basis (Fin N) Ω V) :
    ∃ u₁ : Module.Basis (Fin N) Ω V₁, ∀ v j, β v (u₁ j) = u.repr v j.rev := by
  let e := LinearEquiv.ofBijective β.flip hβ
  refine ⟨(u.dualBasis.reindex Fin.revPerm).map e.symm, fun v j => ?_⟩
  simp only [Module.Basis.map_apply, Module.Basis.reindex_apply, Fin.revPerm_symm, Fin.revPerm_apply]
  change e (e.symm (u.dualBasis j.rev)) v = _
  simp

end PositivityTheory.Xgn.A_flagframe_dual

theorem PositivityTheory.Xgn.t_flagframe_dual : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hD w b hE w₁ hw₁
  refine ⟨fun c hc j => ?_⟩
  have hne : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
  let m : Fin N → Ω := fun i => ∏ k, x ⟨k, c k⟩ ^ b i k
  have hm : ∀ i, m i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hne k)
  have hinvm : ∀ i, ∏ k, x ⟨k, c k⟩ ^ (-b i) k = (m i)⁻¹ := by
    intro i
    simp only [m, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  have hgr := hE.graded c hc
  have hex : ∀ i, ∃ v ∈ E.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = m i := by
    intro i
    have hmem : m i ∈ degLat O x (b i) c := ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← hgr i] at hmem
    exact hmem
  choose e he1 he2 he3 using hex
  have hP : (w.toMatrix e).BlockTriangular id := fun i j hij => he2 j i hij
  have hdet : IsUnit (w.det e) := by
    rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular hP]
    refine (Finset.prod_ne_zero_iff.mpr fun i _ => ?_).isUnit
    rw [Module.Basis.toMatrix_apply, he3]
    exact hm i
  have hbasis := (Module.Basis.is_basis_iff_det w).mpr hdet
  let eb : Module.Basis (Fin N) Ω V := Module.Basis.mk hbasis.1 hbasis.2.ge
  have heb : ∀ i, eb i = e i := fun i => Module.Basis.mk_apply _ _ _
  have htri := A_flagframe_dual.tri_inv w eb (by
    intro i k hik
    rw [heb]
    exact he2 i k hik)
  have hrep : ∀ y k, w₁.repr y k = β (w k.rev) y :=
    fun y k => A_flagframe_dual.repr_of_pair β w w₁ hw₁ y k
  have hstep : ∀ n : ℕ, ∀ v ∈ E.lat c, (∀ k : Fin N, n ≤ k.val → w.repr v k = 0) →
      ∀ k, eb.repr v k ∈ chartRing O (mseg x) c := by
    intro n
    induction n with
    | zero =>
      intro v _ hz k
      have hv0 : v = 0 := w.ext_elem fun i => by rw [hz i (Nat.zero_le _), map_zero]; rfl
      rw [hv0, map_zero]
      exact zero_mem _
    | succ n ih =>
      intro v hv hz k
      by_cases hn : n < N
      · let i : Fin N := ⟨n, hn⟩
        have hmem : w.repr v i ∈ degLat O x (b i) c := by
          rw [← hgr i]
          exact ⟨v, hv, fun j hij => hz j hij, rfl⟩
        obtain ⟨α, hα, hs⟩ := hmem
        have hv' : v - α • e i ∈ E.lat c := sub_mem hv (E.stable c α hα (e i) (he1 i))
        have hz' : ∀ k : Fin N, n ≤ k.val → w.repr (v - α • e i) k = 0 := by
          intro k hk
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          rcases Nat.lt_or_eq_of_le hk with hk | hk
          · have hik : i < k := hk
            rw [hz k hk, he2 i k hik, mul_zero, sub_zero]
          · have hik : k = i := Fin.ext hk.symm
            rw [hik, hs, he3]
            exact sub_self _
        have h1 := ih _ hv' hz' k
        have h2 : eb.repr v k = eb.repr (v - α • e i) k + α * eb.repr (e i) k := by
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          ring
        rw [h2]
        refine add_mem h1 (mul_mem hα ?_)
        rw [← heb, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · exact ih v hv (fun k hk => absurd k.isLt (by omega)) k
  have hcoef : ∀ v ∈ E.lat c, ∀ k, eb.repr v k ∈ chartRing O (mseg x) c :=
    fun v hv => hstep N v hv (fun k hk => absurd k.isLt (by omega))
  ext s
  constructor
  · rintro ⟨w', hw', hz, rfl⟩
    have key : β (e j.rev) w' = m j.rev * w₁.repr w' j := by
      conv_lhs => rw [← w.sum_repr (e j.rev)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j.rev]
      · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, he3, hrep w' j]
      · intro k _ hk
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
        rcases lt_or_gt_of_ne hk with hk | hk
        · have hjk : j < k.rev := Fin.lt_rev_iff.mp hk
          have hb : β (w k) w' = w₁.repr w' k.rev := by rw [hrep, Fin.rev_rev]
          rw [hb, hz _ hjk, mul_zero]
        · rw [he2 _ _ hk, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    refine ⟨β (e j.rev) w', (hD.2 c hc w').1 hw' (e j.rev) (he1 _), ?_⟩
    show w₁.repr w' j = β (e j.rev) w' * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k
    rw [key, hinvm, mul_comm (m j.rev), mul_assoc, mul_inv_cancel₀ (hm _), mul_one]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨f, hf⟩ := hD.1.2 (a • eb.coord j.rev)
    have hfv : ∀ v, β v f = a * eb.repr v j.rev := by
      intro v
      have := LinearMap.congr_fun hf v
      simpa using this
    refine ⟨f, (hD.2 c hc f).2 fun v hv => ?_, fun k hk => ?_, ?_⟩
    · rw [hfv]
      exact mul_mem ha (hcoef v hv _)
    · rw [hrep, hfv, htri.1 _ _ (Fin.rev_lt_rev.mpr hk), mul_zero]
    · show w₁.repr f j = a * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k
      rw [hrep, hfv, htri.2, heb, he3, hinvm]
end

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_rootnum_dual

section Lists

variable {K : Type*} {σ : Type*}

theorem headAdd_neg {A : List (K → ℤ) → ℤ} (hA : HeadAdd A) (u : K → ℤ)
    (l : List (K → ℤ)) : A ((-u) :: l) = -A (u :: l) := by
  let φ : (K → ℤ) →+ ℤ := AddMonoidHom.mk' (fun v => A (v :: l)) fun v w => hA v w l
  exact map_neg φ u

theorem map_neg_append {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A)
    (l r : List (K → ℤ)) : A (l.map (- ·) ++ r) = (-1) ^ l.length * A (l ++ r) := by
  induction l generalizing r with
  | nil => simp
  | cons u l ih =>
    rw [List.map_cons, List.cons_append, headAdd_neg hA,
      hp _ _ (List.perm_middle (a := u) (l₁ := l.map (- ·)) (l₂ := r)).symm, ih,
      hp _ _ (List.perm_middle (a := u) (l₁ := l) (l₂ := r)), List.length_cons, List.cons_append]
    ring

theorem length_classList (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ}
    (hH : H.IsHomogeneous n) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = n := by
  have h1 := hH (mem_support_iff.mp hμ)
  rw [← h1]
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply]
  simp [Finsupp.sum]

theorem polyVal_neg {A : List (K → ℤ) → ℤ} (hp : PermInv A) (hA : HeadAdd A)
    (cls : σ → K → ℤ) {H : MvPolynomial σ ℤ} {n : ℕ} (hH : H.IsHomogeneous n) :
    polyVal A (fun s => -cls s) H = (-1) ^ n * polyVal A cls H := by
  unfold polyVal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hperm : (classList (fun s => -cls s) μ).Perm ((classList cls μ).map (- ·) ++ []) := by
    unfold classList
    rw [List.append_nil, ← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList,
      Multiset.coe_toList, Multiset.map_map]
    rfl
  rw [hp _ _ hperm, map_neg_append hp hA, length_classList cls hH hμ, List.append_nil]
  ring

end Lists

section Numbers

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem isVerticalDivisor_swap {P : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) : IsVerticalDivisor P ϖ (-b) g f := by
  refine ⟨?_, hD.den_not_mem, hD.num_not_mem, ?_, ?_⟩
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨bg, bf, hg, hf, ?_⟩
    rw [← hb]
    funext k
    simp
  · intro W hW
    apply hD.vertical W
    unfold ratDiv at hW ⊢
    exact fun h => hW (sub_eq_zero.mpr (sub_eq_zero.mp h).symm)
  · intro W hW hPW hrel hϖ
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special W hW hPW hrel hϖ
    refine ⟨v, u, hv, hu, ?_⟩
    rw [← neg_sub]
    exact P.neg_mem h

theorem pairNum_dual {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ}
    (hP : IsModelOver P d) {N : ℕ} {b b' : Fin N → K → ℤ} {f g : Fin N → MRing ι O}
    (hD : ∀ i, IsVerticalDivisor P ϖ (b i - b' i) (f i) (g i))
    {k : ℕ} (hk : 1 ≤ k) {Q : List (K → ℤ)} (hQ : Q.length + k = d + 1) :
    pairNum P (fun j => -b j.rev) (fun j => -b' j.rev) (fun j => g j.rev) (fun j => f j.rev)
        (psumExpansion N k) Q =
      (-1) ^ k * pairNum P b b' f g (psumExpansion N k) Q := by
  unfold pairNum
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  have hH := isHomogeneous_psumExpansion N k i
  have hn : k - 1 + Q.length = d := by omega
  have hcls : (Sum.elim (fun j : Fin N => -b j.rev) (fun j : Fin N => -b' j.rev)) =
      fun s => -(Sum.elim (fun j : Fin N => b j.rev) (fun j : Fin N => b' j.rev)) s := by
    funext s
    cases s <;> simp
  unfold cycEval
  rw [mul_finsum]
  refine finsum_congr fun W => ?_
  have hr : ratDiv P (g i.rev) (f i.rev) W = -ratDiv P (f i.rev) (g i.rev) W := by
    unfold ratDiv
    ring
  rw [Fin.revPerm_apply]
  beta_reduce
  rw [hr]
  by_cases hW : ratDiv P (f i.rev) (g i.rev) W = 0
  · simp [hW]
  rw [classNum_eq_polyVal _ hH hn, hcls,
    polyVal_neg (listNum_perm W Q d)
      (listNum_headAdd IntNumAddFirst.full hϖ hP (hD i.rev) hW Q) _ hH,
    ← classNum_eq_polyVal _ hH hn, classNum_psumExpansion _ _ k _ hQ,
    classNum_psumExpansion _ _ k _ hQ]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

theorem root_dual {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ}
    (hP : IsModelOver P d) {N : ℕ} (b : Fin N → K → ℤ) {a : O} (ha : a ≠ 0)
    {j : ℕ} {Q : List (K → ℤ)} (hQ : j + Q.length = d) :
    cycEval (fun W => classNum (fun i : Fin N => -b i.rev) (psum (Fin N) ℤ j) Q W)
        (divCycle P (C a)) =
      (-1) ^ j * cycEval (fun W => classNum b (psum (Fin N) ℤ j) Q W) (divCycle P (C a)) := by
  have : P.IsPrime := hP.multiProj.isPrime
  have hC : (C a : MRing ι O) ∉ P := by
    intro hmem
    have h1 : a ∈ P.comap (C : O →+* MRing ι O) := hmem
    rw [hP.noTorsion] at h1
    exact ha (Ideal.mem_bot.mp h1)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hD := ScalarQuotient.isVerticalDivisor_const P ϖ u n hC
  have hH := isHomogeneous_psum N j
  unfold cycEval
  rw [mul_finsum]
  refine finsum_congr fun W => ?_
  by_cases hW : divCycle P (C ((u : O) * ϖ ^ n)) W = 0
  · simp only [hW, zero_mul, mul_zero]
  have hW' : ratDiv P (C ((u : O) * ϖ ^ n)) 1 W ≠ 0 := by
    unfold ratDiv
    rwa [divCycle_one, sub_zero]
  have e : polyVal (listNum W Q d) (fun i : Fin N => b i.rev) (psum (Fin N) ℤ j) =
      polyVal (listNum W Q d) b (psum (Fin N) ℤ j) := by
    conv_rhs => rw [← psum_isSymmetric (Fin N) ℤ j Fin.revPerm, polyVal_rename]
    rfl
  beta_reduce
  rw [classNum_eq_polyVal _ hH hQ, classNum_eq_polyVal _ hH hQ,
    polyVal_neg (listNum_perm W Q d) (listNum_headAdd IntNumAddFirst.full hϖ hP hD hW' Q)
      (fun i : Fin N => b i.rev) hH, e]
  ring

end Numbers

section Lattices

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem exists_system (R : Subalgebra O Ω) {N : ℕ} (L : AddSubgroup V) (h : LocFree R N L)
    (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Bijective β.flip) :
    ∃ (k : ℕ) (v : Fin k × Fin N → V) (l : Fin k × Fin N → V₁), (∀ i, v i ∈ L) ∧
      (∀ i, ∀ e ∈ L, β e (l i) ∈ R) ∧ (∀ e, ∑ i, β e (l i) • v i = e) ∧
      ∀ w, ∑ i, β (v i) w • l i = w := by
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := N) h
  choose l hl using fun i => hβ.2 (φ i)
  have hl' : ∀ i e, β e (l i) = φ i e := fun i e => by rw [← hl i]; rfl
  refine ⟨k, fun i => v i, l, fun i => (v i).2, fun i e he => ?_, fun e => ?_, fun w => ?_⟩
  · rw [hl']
    exact hφ i e he
  · simp only [hl']
    exact hv e
  · apply hβ.1
    ext e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.flip_apply, LinearMap.flip_apply, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← hv e, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, LinearMap.smul_apply, hl', smul_eq_mul, smul_eq_mul, mul_comm]

theorem dual_closure (R R' : Subalgebra O Ω) (hR : ∀ a ∈ R, a ∈ R') {N : ℕ} (L : AddSubgroup V)
    (h : LocFree R N L) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Bijective β.flip)
    (M : AddSubgroup V₁) (hM : ∀ w, w ∈ M ↔ ∀ v ∈ L, β v w ∈ R) (w : V₁) :
    w ∈ AddSubgroup.closure {v | ∃ a ∈ R', ∃ e ∈ M, v = a • e} ↔
      ∀ v ∈ AddSubgroup.closure {v | ∃ a ∈ R', ∃ e ∈ L, v = a • e}, β v w ∈ R' := by
  constructor
  · intro hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨a, ha, e, he, rfl⟩ := hw
      intro v hv
      induction hv using AddSubgroup.closure_induction with
      | mem v hv =>
        obtain ⟨c, hc, y, hy, rfl⟩ := hv
        rw [map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
        exact R'.mul_mem ha (R'.mul_mem hc (hR _ ((hM e).1 he y hy)))
      | zero => rw [map_zero, LinearMap.zero_apply]; exact R'.zero_mem
      | add x y _ _ hx hy => rw [map_add (f := _), LinearMap.add_apply]; exact R'.add_mem hx hy
      | neg x _ hx => rw [map_neg, LinearMap.neg_apply]; exact R'.neg_mem hx
    | zero => intro v _; rw [map_zero]; exact R'.zero_mem
    | add x y _ _ hx hy => intro v hv; rw [map_add (f := _)]; exact R'.add_mem (hx v hv) (hy v hv)
    | neg x _ hx => intro v hv; rw [map_neg]; exact R'.neg_mem (hx v hv)
  · intro hw
    obtain ⟨k, v, l, hv, hl, -, hs⟩ := exists_system R L h β hβ
    rw [← hs w]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure
      ⟨_, hw _ (AddSubgroup.subset_closure ⟨1, R'.one_mem, _, hv i, (one_smul _ _).symm⟩), _,
        (hM _).2 (hl i), rfl⟩

theorem dual_generic [IsDomain O] (R : Subalgebra O Ω) {N : ℕ} (L L' : AddSubgroup V)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L)
    (h : LocFree R N L') (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Bijective β.flip)
    (M M' : AddSubgroup V₁) (hM : ∀ w, w ∈ M ↔ ∀ v ∈ L, β v w ∈ R)
    (hM' : ∀ w, w ∈ M' ↔ ∀ v ∈ L', β v w ∈ R)
    (hg : ∀ v ∈ L', ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ L) :
    ∀ w ∈ M, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • w ∈ M' := by
  classical
  intro w hw
  obtain ⟨k, v, l, hv, hl, hs, -⟩ := exists_system R L' h β hβ
  choose c hc0 hc using fun i => hg (v i) (hv i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.2 fun i _ => hc0 i, (hM' _).2 fun e he => ?_⟩
  have key : algebraMap O Ω (∏ i, c i) • e ∈ L := by
    rw [← hs e, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [smul_comm, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), map_mul, mul_smul]
    exact hL _ (hl i e he) _ (hL _ (R.algebraMap_mem _) _ (hc i))
  have := (hM w).1 hw _ key
  rw [map_smul, LinearMap.smul_apply] at this
  rw [map_smul]
  exact this

end Lattices

section Bundles

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
  [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {x : (Σ k, ι k) → Ω} {N : ℕ} {V : Type} [AddCommGroup V] [Module Ω V]
  {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω}

theorem pull_dual {E : ChartBundle O (mseg x) N V} {F : ChartBundle O (mseg x) N V₁}
    (hD : IsDualLat O x β E.lat F.lat) {K' : Type} [Fintype K'] {ι' : K' → Type}
    [∀ k, Fintype (ι' k)] {z : (Σ k, ι' k) → Ω} {EB : ChartBundle O (mseg (joinCoord x z)) N V}
    {FB : ChartBundle O (mseg (joinCoord x z)) N V₁} (hE : IsPull O x z E EB)
    (hF : IsPull O x z F FB) : IsDualLat O (joinCoord x z) β EB.lat FB.lat := by
  refine ⟨hD.1, fun s hs w => ?_⟩
  have hx := A_pull_preserve.below_ne x z s hs
  rw [hE s hs, hF s hs]
  exact dual_closure _ _ (fun a ha => A_pull_line.map_mem (AlgHom.id O Ω) x z s hs a ha) _
    (((t_bundle_of_family O Ω K ι x N V).2 E).2 _ hx) β hD.1 _ (hD.2 _ hx) w

theorem sameGeneric_dual {E E' : ChartBundle O (mseg x) N V} {F F' : ChartBundle O (mseg x) N V₁}
    (hS : SameGeneric O x E E') (hD : IsDualLat O x β E.lat F.lat)
    (hD' : IsDualLat O x β E'.lat F'.lat) : SameGeneric O x F F' := by
  intro s hs
  have h := ((t_bundle_of_family O Ω K ι x N V).2 E).2 s hs
  have h' := ((t_bundle_of_family O Ω K ι x N V).2 E').2 s hs
  exact ⟨dual_generic _ _ _ h.1 h' β hD.1 _ _ (hD.2 s hs) (hD'.2 s hs) (hS s hs).2,
    dual_generic _ _ _ h'.1 h β hD.1 _ _ (hD'.2 s hs) (hD.2 s hs) (hS s hs).1⟩

end Bundles

end PositivityTheory.Xgn.A_rootnum_dual

open PositivityTheory.Xgn.A_rootnum_dual in
theorem PositivityTheory.Xgn.t_rootnum_dual : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsDualLat O x β E.lat F.lat → IsDualLat O x β E'.lat F'.lat → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = (-1) ^ k * ck O x d N E E' k L Q) ∧ ∀ (j : ℕ), j ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - j) → ∀ a : O, a ≠ 0 → rootNum O x d N F (psum (Fin N) ℤ j) L Q a = (-1) ^ j * rootNum O x d N E (psum (Fin N) ℤ j) L Q a := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d N V _ _ V₁ _ _ β E E' F F' hM hS hD hD'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨K', _, _, ι', _, z, EB, w, b, hm, hb, hj⟩ := GlobalTheory.T.same_generic_bundle_chain O Ω K ι x d hM N 1 V ![E, E'] (by
    intro j
    fin_cases j
    · exact fun s _ => ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩,
        fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
    · exact hS)
  have hp : IsPull O x z E (EB 0) := (hj 0).1
  have hp' : IsPull O x z E' (EB 1) := (hj 1).1
  obtain ⟨-, hB⟩ := (BundleExamples.isModelOver_iff O _ d).mp hm
  have hB' : IsModelOver (pointIdeal O (joinCoord x z)) d := hB
  have hSB := (PositivityTheory.Xgn.t_pull_preserve O Ω K ι x N V E E' K' ι' z _ _ hp hp').2.1 hS
  obtain ⟨-, f, g, hfp⟩ := GlobalTheory.T.same_generic_flag_comparison O Ω (K ⊕ K') (Sum.elim ι ι') (joinCoord x z) ϖ hϖ d hB' N V
    (EB 0) (EB 1) hSB w w (b 0) (b 1) (hj 0).2 (hj 1).2
    (fun i j hij => by simp [Module.Basis.repr_self, hij.ne])
  obtain ⟨FB, hF⟩ := (GlobalTheory.T.chart_bundle_base_extension O Ω K ι x N V₁ F).1 K' ι' z
  obtain ⟨F'B, hF'⟩ := (GlobalTheory.T.chart_bundle_base_extension O Ω K ι x N V₁ F').1 K' ι' z
  obtain ⟨w₁, hw₁⟩ := PositivityTheory.Xgn.A_flagframe_dual.exists_dual β hD.1 w
  have hw : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0 := fun i j => by
    rw [hw₁]; simp [Finsupp.single_apply]
  have hfp₁ : IsFlagPair ϖ (joinCoord x z) FB F'B w₁ w₁ (fun j => -b 0 j.rev) (fun j => -b 1 j.rev)
      (fun j => g j.rev) (fun j => f j.rev) := by
    refine ⟨PositivityTheory.Xgn.t_flagframe_dual O Ω _ _ _ N V V₁ _ _ β (pull_dual hD hp hF) w _ hfp.flag w₁ hw,
      PositivityTheory.Xgn.t_flagframe_dual O Ω _ _ _ N V V₁ _ _ β (pull_dual hD' hp' hF') w _ hfp.flag' w₁ hw,
      fun i j hij => by simp [Module.Basis.repr_self, hij.ne], fun i => ?_, fun i => ?_⟩
    · have h := isVerticalDivisor_swap (hfp.vertical i.rev)
      have e : -b 0 i.rev - -b 1 i.rev = -(b 0 i.rev - b 1 i.rev) := by abel
      rw [e]
      exact h
    · have h := hfp.generic i.rev
      rw [Module.Basis.repr_self, Finsupp.single_eq_same, one_mul] at h ⊢
      exact h.symm
  obtain ⟨h1, h2⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V E E' hS K' ι' z hm hb _ _ hp hp'
    w w _ _ f g hfp
  obtain ⟨h3, h4⟩ := GlobalTheory.T.same_generic_flag_difference O Ω K ι x ϖ hϖ d hM N V₁ F F' (sameGeneric_dual hS hD hD')
    K' ι' z hm hb _ _ hF hF' w₁ w₁ _ _ _ _ hfp₁
  refine ⟨fun k hk1 hk2 q L Q hQ => ?_, fun j hj q L Q hQ a ha => ?_⟩
  · rw [h1 k hk1 hk2 q L Q hQ, h3 k hk1 hk2 q L Q hQ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [pairNum_dual hϖ hB' hfp.vertical hk1 (by rw [length_classList _ hQ hμ]; omega)]
    ring
  · rw [h2 j _ (psum_isSymmetric _ _ j) (isHomogeneous_psum N j) hj q L Q hQ a ha,
      h4 j _ (psum_isSymmetric _ _ j) (isHomogeneous_psum N j) hj q L Q hQ a ha, Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    rw [root_dual hϖ hB' (b 0) ha (by rw [length_classList _ hQ hμ]; omega)]
    ring
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBundleIntersection
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBundleIntersection
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem ck_rootNum_dual : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsDualLat O x β E.lat F.lat → IsDualLat O x β E'.lat F'.lat → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = (-1) ^ k * ck O x d N E E' k L Q) ∧ ∀ (j : ℕ), j ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - j) → ∀ a : O, a ≠ 0 → rootNum O x d N F (psum (Fin N) ℤ j) L Q a = (-1) ^ j * rootNum O x d N E (psum (Fin N) ℤ j) L Q a :=
  @PositivityTheory.Xgn.t_rootnum_dual

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualBundleIntersectionStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_bundle_intersection : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (E E' : ChartBundle O (mseg x) N V) (F F' : ChartBundle O (mseg x) N V₁), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x E E' → IsDualLat O x β E.lat F.lat → IsDualLat O x β E'.lat F'.lat → (∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N F F' k L Q = (-1) ^ k * ck O x d N E E' k L Q) ∧ ∀ (j : ℕ), j ≤ d → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d - j) → ∀ a : O, a ≠ 0 → rootNum O x d N F (psum (Fin N) ℤ j) L Q a = (-1) ^ j * rootNum O x d N E (psum (Fin N) ℤ j) L Q a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_dual | exact GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ck_rootNum_dual <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticePermuted
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.RelK

section Lat

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ} {Sg : Type}
  {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s)

theorem mem_vanSub {i : ℕ} {g : (Fin n → F) → Ω} : g ∈ vanSub Ω F n i ↔
    ∀ y : Fin n → F, (∀ j : Fin n, i ≤ (j : ℕ) → y j = 0) → g y = 0 := by
  simp [vanSub, Submodule.mem_pi]

theorem mem_kk {τ : Sg} {i : ℕ} {m : Fin (r τ) → Ω} :
    m ∈ D.kk τ i ↔ ∃ g, (g, m) ∈ D.Th τ ∧ g ∈ vanSub Ω F n i := by
  simp only [LieLatticeData.kk, AddSubgroup.mem_map, AddSubgroup.mem_inf, AddSubgroup.mem_prod]
  constructor
  · rintro ⟨⟨g, m'⟩, ⟨h1, h2, -⟩, rfl⟩
    exact ⟨g, h1, h2⟩
  · rintro ⟨g, h1, h2⟩
    exact ⟨(g, m), ⟨h1, h2, AddSubgroup.mem_top _⟩, rfl⟩

theorem mem_xId {χ : F → Ω} {i : Fin n} {c : Ω} : c ∈ D.xId χ i ↔
    ∃ g ∈ D.M, ∃ h ∈ vanSub Ω F n ((i : ℕ) + 1), g + h = c • fun y : Fin n → F => χ (y i) := by
  simp only [LieLatticeData.xId, AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  rfl

theorem mem_stepGraph {τ : Sg} {χ : F → Ω} {i : Fin n} {c : Ω} {m : Fin (r τ) → Ω} :
    (c, m) ∈ D.stepGraph τ χ i ↔ ∃ g h, (g, m) ∈ D.Th τ ∧ h ∈ vanSub Ω F n ((i : ℕ) + 1) ∧
      g + h = c • fun y : Fin n → F => χ (y i) := by
  simp only [LieLatticeData.stepGraph, AddSubgroup.mem_comap, AddSubgroup.mem_sup]
  constructor
  · rintro ⟨⟨g, m'⟩, h1, ⟨h, m''⟩, h2, h3⟩
    have hz : m'' = 0 := (AddSubgroup.mem_prod.1 h2).2
    subst hz
    have e := congrArg Prod.fst h3
    have e' := congrArg Prod.snd h3
    simp at e e'
    subst e'
    exact ⟨g, h, h1, (AddSubgroup.mem_prod.1 h2).1, e⟩
  · rintro ⟨g, h, h1, h2, h3⟩
    refine ⟨(g, m), h1, (h, 0), AddSubgroup.mem_prod.2 ⟨h2, AddSubgroup.mem_bot.2 rfl⟩, ?_⟩
    simp [h3]

theorem mem_mulLat {V : Type} [AddCommGroup V] [Module Ω V] {c : Ω} {L : AddSubgroup V} {v : V} :
    v ∈ mulLat c L ↔ ∃ e ∈ L, v = c • e := by
  simp only [mulLat, AddSubgroup.mem_map, DistribSMul.toAddMonoidHom_apply]
  constructor
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩
  · rintro ⟨e, he, rfl⟩; exact ⟨e, he, rfl⟩

theorem mem_dotDual {R : Subalgebra o Ω} {N : ℕ} {L : AddSubgroup (Fin N → Ω)} {v : Fin N → Ω} :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

variable [Fintype F] {R : Subalgebra o Ω} {p : ℕ} {w : Ω}

theorem kk_zero (hb : D.Base R p w) (τ : Sg) : D.kk τ 0 = dotDual R (D.lie τ) := by
  ext m
  rw [mem_kk]
  constructor
  · rintro ⟨g, hg, -⟩
    exact ((hb.th τ).2.1 m).1 ⟨g, hg⟩
  · intro hm
    obtain ⟨g, hg⟩ := ((hb.th τ).2.1 m).2 hm
    refine ⟨g, hg, mem_vanSub.2 fun y hy => ?_⟩
    have : y = 0 := funext fun j => hy j (Nat.zero_le _)
    rw [this]
    exact (((hb.th τ).1 g).1 ⟨m, hg⟩).2

theorem kk_top (hb : D.Base R p w) (τ : Sg) : D.kk τ n = mulLat (p : Ω) (dotDual R (D.lie τ)) := by
  ext m
  rw [mem_kk, ← (hb.th τ).2.2 m]
  constructor
  · rintro ⟨g, hg, hv⟩
    have : g = 0 := funext fun y => mem_vanSub.1 hv y fun j hj => absurd j.2 (not_lt.2 hj)
    rwa [this] at hg
  · intro h
    exact ⟨0, h, (vanSub Ω F n n).zero_mem⟩

theorem kk_anti {i j : ℕ} (h : i ≤ j) (τ : Sg) : D.kk τ j ≤ D.kk τ i := by
  intro m hm
  obtain ⟨g, hg, hv⟩ := (mem_kk D).1 hm
  exact (mem_kk D).2 ⟨g, hg, mem_vanSub.2 fun y hy => mem_vanSub.1 hv y fun l hl => hy l (h.trans hl)⟩

theorem smul_mem_kk (hb : D.Base R p w) {τ : Sg} {i j : ℕ} (hi : i ≤ n) {m : Fin (r τ) → Ω}
    (hm : m ∈ D.kk τ j) : (p : Ω) • m ∈ D.kk τ i := by
  have h0 : m ∈ dotDual R (D.lie τ) := by
    rw [← kk_zero D hb τ]
    exact kk_anti D (Nat.zero_le j) τ hm
  exact kk_anti D hi τ (by rw [kk_top D hb τ]; exact mem_mulLat.2 ⟨m, h0, rfl⟩)

end Lat

section Step

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F]
  {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) {R : Subalgebra o Ω} {p : ℕ} {w : Ω}

theorem mem_of_mem_xId (hb : D.Base R p w) {χ : F → Ω} (h1 : χ 1 = 1) (h01 : (0 : F) ≠ 1)
    {i : Fin n} {c : Ω} (hc : c ∈ D.xId χ i) : c ∈ R := by
  classical
  obtain ⟨g, hg, h, hh, e⟩ := (mem_xId D).1 hc
  let y : Fin n → F := fun j => if j = i then 1 else 0
  have hy : h y = 0 := mem_vanSub.1 hh y fun j hj => by
    have : j ≠ i := fun hji => by
      rw [hji] at hj
      omega
    simp [y, this]
  have e' := congrFun e y
  have hyi : y i = 1 := by simp [y]
  simp only [Pi.add_apply, hy, add_zero, Pi.smul_apply, hyi, h1, smul_eq_mul, mul_one] at e'
  rw [← e']
  have := hb.M_le hg
  exact (AddSubgroup.mem_pi _).1 this y (Set.mem_univ _)

theorem exists_mul_mem_xId (hb : D.Base R p w) {χ : F → Ω} (hχ : ∀ a, χ a ∈ R) (i : Fin n) :
    ∃ m : ℕ, ∀ c ∈ R, (p : Ω) ^ m * c ∈ D.xId χ i := by
  obtain ⟨m, hm⟩ := hb.le_M
  refine ⟨m, fun c hc => (mem_xId D).2 ⟨_, hm (mem_mulLat.2 ⟨fun y => c * χ (y i), ?_, rfl⟩), 0,
    (vanSub Ω F n _).zero_mem, ?_⟩⟩
  · exact (AddSubgroup.mem_pi _).2 fun y _ => R.mul_mem hc (hχ _)
  · funext y
    simp [mul_assoc]

theorem step_facts (hb : D.Base R p w) {τ : Sg} {χ : F → Ω} (h0 : χ 0 = 0) {i : Fin n}
    {X : AddSubgroup Ω} (honto : (D.stepGraph τ χ i).map (AddMonoidHom.snd _ _) = D.kk τ i)
    (hinj : (D.stepGraph τ χ i).comap (AddMonoidHom.inl _ _) = X) :
    (∀ v m, (v, m) ∈ D.stepGraph τ χ i → v ∈ D.xId χ i ∧ m ∈ D.kk τ i) ∧
    (∀ v ∈ D.xId χ i, ∃ m, (v, m) ∈ D.stepGraph τ χ i) ∧
    (∀ m, (0, m) ∈ D.stepGraph τ χ i ↔ m ∈ D.kk τ ((i : ℕ) + 1)) ∧
    (∀ v, (v, 0) ∈ D.stepGraph τ χ i ↔ v ∈ X) ∧
    (∀ m ∈ D.kk τ i, ∃ v, (v, m) ∈ D.stepGraph τ χ i) := by
  refine ⟨fun v m h => ⟨?_, ?_⟩, fun v hv => ?_, fun m => ?_, fun v => ?_, fun m hm => ?_⟩
  · obtain ⟨g, h', hg, hh, e⟩ := (mem_stepGraph D).1 h
    exact (mem_xId D).2 ⟨g, (((hb.th τ).1 g).1 ⟨m, hg⟩).1, h', hh, e⟩
  · rw [← honto]
    exact ⟨(v, m), h, rfl⟩
  · obtain ⟨g, hg, h, hh, e⟩ := (mem_xId D).1 hv
    have hh0 : h 0 = 0 := mem_vanSub.1 hh 0 fun _ _ => rfl
    have e' := congrFun e 0
    simp only [Pi.add_apply, hh0, add_zero, Pi.smul_apply, Pi.zero_apply, h0, smul_zero] at e'
    obtain ⟨m, hm⟩ := ((hb.th τ).1 g).2 ⟨hg, e'⟩
    exact ⟨m, (mem_stepGraph D).2 ⟨g, h, hm, hh, e⟩⟩
  · rw [mem_stepGraph, mem_kk]
    constructor
    · rintro ⟨g, h, hg, hh, e⟩
      have : g = -h := by
        rw [zero_smul] at e
        exact eq_neg_of_add_eq_zero_left e
      exact ⟨g, hg, this ▸ (vanSub Ω F n _).neg_mem hh⟩
    · rintro ⟨g, hg, hv⟩
      exact ⟨g, -g, hg, (vanSub Ω F n _).neg_mem hv, by simp⟩
  · rw [← hinj]
    rfl
  · rw [← honto] at hm
    obtain ⟨⟨v, m'⟩, h, rfl⟩ := hm
    exact ⟨v, h⟩

end Step

section Line

variable {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type}

theorem chartMon_smul (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (a : K → ℤ) (p : ℕ) :
    chartMon x c ((p : ℤ) • a) = chartMon x c a ^ p := by
  simp only [chartMon, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul, zpow_natCast]

theorem powSpan_line {R : Subalgebra O Ω} {p : ℕ} {X Y : AddSubgroup Ω} {e : Ω}
    (hX : ∀ v, v ∈ X ↔ ∃ a ∈ R, v = a * e) (hY : ∀ v, v ∈ Y ↔ ∃ a ∈ R, v = a * e ^ p) :
    Y = powSpan R p X := by
  apply le_antisymm
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := (hY v).1 hv
    refine AddSubgroup.subset_closure ⟨a, ha, e ^ p, ⟨e, (hX e).2 ⟨1, R.one_mem, by simp⟩, rfl⟩, rfl⟩
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro v ⟨a, ha, _, ⟨b, hb, rfl⟩, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (hX b).1 hb
    exact (hY _).2 ⟨a * t ^ p, R.mul_mem ha (R.pow_mem ht p), by simp [mul_pow, mul_assoc]⟩

end Line

section Dot

variable {Ω : Type} [Field Ω]

noncomputable def dotB (N : ℕ) : (Fin N → Ω) →ₗ[Ω] (Fin N → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) add_dotProduct smul_dotProduct dotProduct_add dotProduct_smul

theorem dotB_apply (N : ℕ) (a b : Fin N → Ω) : dotB N a b = a ⬝ᵥ b := rfl

theorem dotB_bijective (N : ℕ) : Function.Bijective (dotB (Ω := Ω) N).flip := by
  classical
  constructor
  · intro a b h
    funext i
    have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [dotB_apply] using this
  · intro f
    refine ⟨fun i => f (Pi.single i 1), LinearMap.ext fun v => ?_⟩
    rw [LinearMap.flip_apply, dotB_apply]
    conv_rhs => rw [← Finset.univ_sum_single v]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : Pi.single i (v i) = v i • (Pi.single i 1 : Fin N → Ω) := by
      rw [← Pi.single_smul]
      simp
    rw [e, map_smul, smul_eq_mul]

end Dot

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Xb : Sg → Fin n → ChartBundle O (mseg x) 1 Ω) (T : ChartBundle O (mseg x) 1 Ω), (∀ τ i c, mseg x c ≠ 0 → (Xb τ i).lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → IsLine O x 1 0 T.lat → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∀ τ, ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → (k : ℤ) * rootNum O x d (r (φ τ)) (Lie (φ τ)) (psum (Fin (r (φ τ))) ℤ (k - 1)) L Q (p : O) = (-1) ^ (k - 1) * ∑ i, (ck O x d 1 (Xb (φ τ) i) T k L Q - (p : ℤ) ^ k * ck O x d 1 (Xb τ i) T k L Q) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d hmod F _ _ _ n Sg _ r s p hp w χ φ D hfam hG1 hG2 hF hline Xb T hXb
    hT Lie W Om OmHT hB τ k hk1 hk2 q L Q hQ
  have hinj : Function.Injective (algebraMap O Ω) := by
    obtain ⟨-, -, hc, -⟩ := hmod
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    have : a ∈ Ideal.comap (C : O →+* _) (mcIdeal O x) := by
      rw [Ideal.mem_comap]
      simp [mcIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcMap,
        MvPolynomial.algebraMap_apply, ha]
    rw [hc] at this
    simpa using this
  have hfc := GlobalTheory.T.lattice_family_injective_model_facts O Ω K ι x hinj p hp w χ φ D hfam
  have hbase := hfam.base
  have hch := hfam.char
  have hp0 : (p : O) ≠ 0 := hch.1
  have hpΩ : algebraMap O Ω (p : O) = (p : Ω) := map_natCast _ _
  have hBa := GlobalTheory.T.dvr_bundle_statement_a O Ω K ι
  have hKK : ∀ i : ℕ, ∃ E : ChartBundle O (mseg x) (r (φ τ)) (Fin (r (φ τ)) → Ω),
      ∀ c, mseg x c ≠ 0 → E.lat c = (D c).kk (φ τ) i := fun i =>
    (GlobalTheory.T.lattice_families_glue_to_bundle O Ω K ι x (r (φ τ)) _).1 _ ((hfc.2 (φ τ)).2.2.1 i)
      (fun c hc => (hG2 c hc).kk (φ τ) i)
  choose KK hKK using hKK

  have hSG : ∀ i j, i ≤ n → j ≤ n → SameGeneric O x (KK i) (KK j) := by
    intro i j hi hj c hc
    refine ⟨fun v hv => ⟨p, hp0, ?_⟩, fun v hv => ⟨p, hp0, ?_⟩⟩
    · rw [hKK i c hc] at hv
      rw [hKK j c hc, hpΩ]
      exact smul_mem_kk (D c) (hbase c hc) hj hv
    · rw [hKK j c hc] at hv
      rw [hKK i c hc, hpΩ]
      exact smul_mem_kk (D c) (hbase c hc) hi hv
  have hXT : ∀ (σ : Sg) (i : Fin n), SameGeneric O x (Xb σ i) T := by
    intro σ i c hc
    have hb := hbase c hc
    have hTc : ∀ v, v ∈ T.lat c ↔ v ∈ chartRing O (mseg x) c := by
      intro v
      rw [hT c hc v]
      simp [chartMon]
    have hχR : ∀ a, algebraMap O Ω (χ σ a) ∈ chartRing O (mseg x) c :=
      fun a => Subalgebra.algebraMap_mem _ _
    obtain ⟨m, hm⟩ := exists_mul_mem_xId (D c) hb hχR i
    refine ⟨fun v hv => ⟨1, one_ne_zero, ?_⟩, fun v hv => ⟨(p : O) ^ m, pow_ne_zero _ hp0, ?_⟩⟩
    · rw [hXb σ i c hc] at hv
      rw [map_one, one_smul, hTc]
      exact mem_of_mem_xId (D c) hb (by rw [(hch.2.2.2.2 σ).2, map_one]) hch.2.2.2.1 hv
    · rw [hXb σ i c hc, map_pow, hpΩ, smul_eq_mul]
      exact hm v ((hTc v).1 hv)
  have hstep : ∀ i : Fin n, ck O x d _ (KK i) (KK ((i : ℕ) + 1)) k L Q =
      ck O x d 1 (Xb (φ τ) i) T k L Q - (p : ℤ) ^ k * ck O x d 1 (Xb τ i) T k L Q := by
    intro i
    obtain ⟨u, a, hu, hl⟩ := hline τ i
    obtain ⟨PB, hPB⟩ := (GlobalTheory.T.chart_bundle_product O Ω K ι x).2.2.1 (u ^ (p : ℤ)) ((p : ℤ) • a)
      (zpow_ne_zero _ hu)
    have hA : IsLine O x u a (Xb τ i).lat := fun c hc v => by
      rw [hXb τ i c hc]
      exact hl c hc v
    have hPBlat : ∀ c, mseg x c ≠ 0 → PB.lat c = powSpan (chartRing O (mseg x) c) p
        ((D c).xId (fun a => algebraMap O Ω (χ τ a)) i) := by
      intro c hc
      refine powSpan_line (e := u * chartMon x c a) (fun v => hl c hc v) (fun v => ?_)
      rw [hPB c hc v, chartMon_smul, zpow_natCast, mul_pow]
    obtain ⟨hPT, hpow⟩ := GlobalTheory.T.line_bundle_chart_generic_comparison O Ω K ι x d hmod (Xb τ i) T PB u a (p : ℤ) hu hA hT
      (hXT τ i) hPB
    have hfacts := fun c (hc : mseg x c ≠ 0) => step_facts (D c) (hbase c hc) (τ := φ τ)
      (χ := fun a => algebraMap O Ω (χ (φ τ) a)) (i := i)
      (by rw [(hch.2.2.2.2 _).1, map_zero]) ((hF c hc).onto (φ τ) i) ((hF c hc).inj τ i)
    have hq : QuotEquiv O x (Xb (φ τ) i).lat PB.lat (KK i).lat (KK ((i : ℕ) + 1)).lat := by
      refine ⟨fun c => (D c).stepGraph (φ τ) (fun a => algebraMap O Ω (χ (φ τ) a)) i,
        ⟨((hfc.2 (φ τ)).2.1 i).2, fun c hc => ?_⟩, fun c hc => ?_⟩
      · obtain ⟨f1, f2, f3, f4, -⟩ := hfacts c hc
        rw [hXb _ i c hc, hKK (i : ℕ) c hc, hKK ((i : ℕ) + 1) c hc, hPBlat c hc]
        exact ⟨f1, f2, f3, fun v hv => (f4 v).2 hv⟩
      · obtain ⟨-, -, -, f4, f5⟩ := hfacts c hc
        rw [hKK (i : ℕ) c hc, hPBlat c hc]
        exact ⟨fun v hv => (f4 v).1 hv, f5⟩
    have hXP : SameGeneric O x (Xb (φ τ) i) PB := by
      intro c hc
      obtain ⟨f1, f2, f3, f4, -⟩ := hfacts c hc
      refine ⟨fun v hv => ⟨p, hp0, ?_⟩, fun v hv => ⟨1, one_ne_zero, ?_⟩⟩
      · rw [hXb _ i c hc] at hv
        rw [hPBlat c hc, hpΩ, ← f4]
        obtain ⟨m, hm⟩ := f2 v hv
        have hkm := (f1 v m hm).2
        have h1 : ((p : Ω) • v, (p : Ω) • m) ∈
            (D c).stepGraph (φ τ) (fun a => algebraMap O Ω (χ (φ τ) a)) i := by
          rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
          exact nsmul_mem hm p
        have h2 := (f3 _).2 (smul_mem_kk (D c) (hbase c hc) (Nat.succ_le_of_lt i.2) hkm)
        have h3 := sub_mem h1 h2
        simpa using h3
      · rw [hPBlat c hc] at hv
        rw [map_one, one_smul, hXb _ i c hc]
        exact (f1 v 0 ((f4 v).2 hv)).1
    have hEq := GlobalTheory.T.chart_bundle_intersection_symmetry O Ω K ι x d 1 (r (φ τ)) Ω (Fin (r (φ τ)) → Ω) (Xb (φ τ) i) PB (KK i)
      (KK ((i : ℕ) + 1)) hmod hXP (hSG _ _ i.2.le (Nat.succ_le_of_lt i.2)) hq k hk1 hk2 q L Q hQ
    have hsym := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.sameGeneric_symm O hPT
    have hc1 := (hBa x d 1 Ω (Xb (φ τ) i) T PB hmod (hXT _ i) hsym k hk1 hk2 q L Q hQ).1
    have hc2 := (hBa x d 1 Ω PB T PB hmod hPT hsym k hk1 hk2 q L Q hQ).2
    have hpw := hpow k hk1 hk2 q L Q hQ
    rw [← hEq, hc1, hc2, hpw]
    ring
  have htel : ∀ j, j ≤ n → ck O x d _ (KK 0) (KK j) k L Q =
      ∑ i ∈ Finset.range j, ck O x d _ (KK i) (KK (i + 1)) k L Q := by
    intro j
    induction j with
    | zero =>
      intro _
      have h00 := hSG 0 0 (Nat.zero_le _) (Nat.zero_le _)
      have := (hBa x d _ _ (KK 0) (KK 0) (KK 0) hmod h00 h00 k hk1 hk2 q L Q hQ).1
      simp only [Finset.range_zero, Finset.sum_empty]
      omega
    | succ j ih =>
      intro hj
      rw [Finset.sum_range_succ, ← ih (by omega)]
      exact (hBa x d _ _ (KK 0) (KK j) (KK (j + 1)) hmod (hSG _ _ (Nat.zero_le _) (by omega))
        (hSG _ _ (by omega) hj) k hk1 hk2 q L Q hQ).1
  have hd : IsDualLat O x (dotB (r (φ τ))) (Lie (φ τ)).lat (KK 0).lat := by
    refine ⟨dotB_bijective _, fun c hc v => ?_⟩
    rw [hKK 0 c hc, kk_zero (D c) (hbase c hc), mem_dotDual, (hB (φ τ) c hc).1]
    rfl
  have hrefl : SameGeneric O x (Lie (φ τ)) (Lie (φ τ)) := fun c _ =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have hdu := (GlobalTheory.T.dual_bundle_intersection O Ω K ι x d (r (φ τ)) _ _ (dotB (r (φ τ))) (Lie (φ τ)) (Lie (φ τ)) (KK 0)
    (KK 0) hmod hrefl hd hd).2 (k - 1) (by omega) q L Q hQ' (p : O) hp0
  have hscale : ∀ c, mseg x c ≠ 0 → ∀ v, v ∈ (KK n).lat c ↔
      ∃ e ∈ (KK 0).lat c, v = algebraMap O Ω (p : O) • e := by
    intro c hc v
    rw [hKK n c hc, hKK 0 c hc, kk_top (D c) (hbase c hc), kk_zero (D c) (hbase c hc), hpΩ, mem_mulLat]
  have hBd := (GlobalTheory.T.dvr_bundle_statement_d O Ω K ι x d (r (φ τ)) _ (KK 0) (KK n) (p : O) hp0 hmod hscale k hk1 hk2
    q L Q hQ).1
  have hsum : ∑ i : Fin n, (ck O x d 1 (Xb (φ τ) i) T k L Q - (p : ℤ) ^ k * ck O x d 1 (Xb τ i) T k L Q) =
      ck O x d _ (KK 0) (KK n) k L Q := by
    rw [htel n le_rfl, ← Fin.sum_univ_eq_sum_range
      (fun i => ck O x d _ (KK i) (KK (i + 1)) k L Q) n]
    exact Finset.sum_congr rfl fun i _ => (hstep i).symm
  have hs : ((-1 : ℤ) ^ (k - 1)) * (-1) ^ (k - 1) = 1 := by
    rw [← mul_pow]
    simp
  rw [hsum, hBd, hdu]
  linear_combination (-(k : ℤ) * rootNum O x d (r (φ τ)) (Lie (φ τ)) (psum (Fin (r (φ τ))) ℤ (k - 1)) L Q (p : O)) * hs

end GlobalTheory.CompanionTheory.Ar.Num.RelK
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModelOverModPLatticePermutedStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_over_mod_p_lattice_permuted : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d : ℕ), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → (∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Good₂ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → (∀ c, mseg x c ≠ 0 → (D c).Facts (chartRing O (mseg x) c) p (algebraMap O Ω w) (fun τ a => algebraMap O Ω (χ τ a)) φ) → (∀ τ i, ∃ (u : Ω) (a : _ → ℤ), u ≠ 0 ∧ IsLine O x u a fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → ∀ (Xb : Sg → Fin n → ChartBundle O (mseg x) 1 Ω) (T : ChartBundle O (mseg x) 1 Ω), (∀ τ i c, mseg x c ≠ 0 → (Xb τ i).lat c = (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) → IsLine O x 1 0 T.lat → ∀ (Lie W : ∀ τ, ChartBundle O (mseg x) (r τ) (Fin (r τ) → Ω)) (Om OmHT : ∀ τ, ChartBundle O (mseg x) (s τ) (Fin (s τ) → Ω)), HasBundles O x D Lie W Om OmHT → ∀ τ, ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → (k : ℤ) * rootNum O x d (r (φ τ)) (Lie (φ τ)) (psum (Fin (r (φ τ))) ℤ (k - 1)) L Q (p : O) = (-1) ^ (k - 1) * ∑ i, (ck O x d 1 (Xb (φ τ) i) T k L Q - (p : ℤ) ^ k * ck O x d 1 (Xb τ i) T k L Q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.RelK.main | exact GlobalTheory.CompanionTheory.Ar.Num.RelK.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.RelK.main <;> assumption)
end
