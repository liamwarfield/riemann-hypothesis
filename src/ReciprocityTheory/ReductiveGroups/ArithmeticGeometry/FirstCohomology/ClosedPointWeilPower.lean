module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

section Grp

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S}

lemma one_comp_hom (f : A ⟶ A) (hf : IsMonHom f) : (1 : T ⟶ A) ≫ f = 1 := by
  haveI := hf
  exact MonObj.one_comp f

lemma comp_act_nat {O : Type} [Ring O] (ρ : RingAct A O) (x : T ⟶ A) :
    ∀ n : ℕ, 1 ≤ n → x ≫ ρ.act (n : O) = x ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [ρ.map_one]
    · rw [Nat.cast_succ, ρ.map_add, ρ.map_one, padd, ← Category.assoc,
        CartesianMonoidalCategory.comp_lift, Category.comp_id, ih hpos, pow_succ, Hom.mul_def]

end Grp

section Weil

lemma weil_one_left (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (y : T ⟶ P.A) (hy : y ^ k = 1) : WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨H1, H2, -, -⟩ := hW S P k T
  obtain ⟨c, hc, -⟩ := H1 1 y (one_pow k) hy
  have hcc : WeilIs P.A P.L k 1 y (c * c) := by simpa using H2 1 1 y c c hc hc
  have huniq := (H1 1 y (one_pow k) hy).unique hc hcc

  have hc1 : c = 1 := mul_left_cancel (huniq.symm.trans (mul_one c).symm)
  rw [← hc1]
  exact hc

lemma weil_pow_eq_one (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) : c ^ k = 1 := by
  have hpow : ∀ n : ℕ, WeilIs P.A P.L k (x ^ n) y (c ^ n) := by
    intro n
    induction n with
    | zero => simpa using weil_one_left hW P k y hy
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact (hW S P k T).2.1 _ _ _ _ _ ih hc
  have h1 := hpow k
  rw [hx] at h1
  exact ((hW S P k T).1 1 y (one_pow k) hy).unique h1 (weil_one_left hW P k y hy)

lemma weil_unique (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (x y : T ⟶ P.A) (hx : x ^ k = 1) (hy : y ^ k = 1) (c c' : Γ(T.left, ⊤)ˣ)
    (hc : WeilIs P.A P.L k x y c) (hc' : WeilIs P.A P.L k x y c') : c = c' :=
  ((hW S P k T).1 x y hx hy).unique hc hc'

end Weil

section Gen

open ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace

lemma top_of_closedPoint {V : Type} [CommRing V] [IsLocalRing V] (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ U) : U = ⊤ := by
  refine eq_top_iff.mpr fun y _ => ?_
  exact (IsLocalRing.specializes_closedPoint (R := V) y).mem_open U.isOpen hU

theorem gen_local {V : Type} [CommRing V] [IsLocalRing V]
    (M : LB (Spec (CommRingCat.of V))) (hM : M.IsLB) : ∃ e : M.Gen, e.IsGen := by

  have hp : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ ⨆ i, M.U i := by
    rw [hM.cover]
    exact TopologicalSpace.Opens.mem_top _
  obtain ⟨i0, hi0⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  have htop : M.U i0 = ⊤ := top_of_closedPoint (M.U i0) hi0
  have hle : ∀ W : (Spec (CommRingCat.of V)).Opens, W ≤ M.U i0 := fun W => by
    rw [htop]
    exact le_top
  have hid : ∀ {W : (Spec (CommRingCat.of V)).Opens} (h0 : W ≤ W) (z : Γ(Spec (CommRingCat.of V), W)ˣ), res h0 z = z := by
    intro W h0 z
    have h1 : homOfLE h0 = 𝟙 W := rfl
    ext
    simp [res, h1]

  refine ⟨⟨fun i => res (le_inf le_rfl (hle _) : M.U i ≤ M.U i ⊓ M.U i0) (M.g i i0)⟩, ?_⟩
  intro i j
  have hc := hM.cocycle i j i0
  have h' : M.U i ⊓ M.U j ≤ M.U i ⊓ M.U j ⊓ M.U i0 := le_inf le_rfl (hle _)
  have hc' := congrArg (fun z => res h' z) hc
  simp only [map_mul, res_res', hid] at hc'
  simp only [res_res']
  exact hc'.symm

theorem gen_local_linComb {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X)
    (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ e : LB.Gen (LB.LinComb L φ ε), e.IsGen :=
  gen_local _ (by
    first
      | exact linComb_isLB
      | exact linComb_isLB hL
      | exact linComb_isLB (hL := hL)
      | exact linComb_isLB hL φ ε
      | exact linComb_isLB L hL φ ε
      | exact linComb_isLB (L := L) (φ := φ) (ε := ε) hL
      | exact linComb_isLB L φ ε hL)

end Gen

end ReciprocityTheory.ChartRestriction.G.H1.ClosedPointWeilPower
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPowAlg
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.H1

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def hv (θ : A → A → A → U) (k : ℕ) (a B x : A) : U := cubN θ k a B x * (θ a x B)⁻¹

theorem cub_rot (h : IsCub θ) (x y z : A) : θ x y z = θ y z x := by
  exact (h.s01 x y z).trans (h.s12 y x z)

private lemma prod_range_theta_mul_pow_eq_of_isCub (h : IsCub θ) (k : ℕ) (a M b x : A) :
    ∏ i ∈ Finset.range k, θ (a * M * b ^ i) b x =
      (∏ i ∈ Finset.range k, θ (M * b ^ i) b x) * θ a (M * b ^ k) x * (θ a M x)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ih]
    have e := h.coc a (M * b ^ k) b x
    rw [← mul_assoc a M (b ^ k), mul_assoc M (b ^ k) b, ← pow_succ b k] at e
    have hA : θ (a * M * b ^ k) b x =
        θ a (M * b ^ (k + 1)) x * θ (M * b ^ k) b x * (θ a (M * b ^ k) x)⁻¹ := by
      rw [← e, mul_inv_cancel_right]
    rw [hA]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

private lemma mul_inv_rearrange_of_two_relations (Q G' G0 P R S T V W : U) (c1 : P * R = T * V) (c2 : T * G0 = W * S) :
    Q * G' * G0⁻¹ * P⁻¹ * R⁻¹ * S = Q * V⁻¹ * (G' * W⁻¹) := by
  have hS : S = W⁻¹ * (T * G0) := by rw [c2, inv_mul_cancel_left]
  have hP : P = T * V * R⁻¹ := by rw [← c1, mul_inv_cancel_right]
  subst hS hP
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel

theorem hv_term (h : IsCub θ) (k : ℕ) (a M b x : A) :
    hv θ k (a * M) b x * (θ a M b)⁻¹ * θ a x b = hv θ k M b x * (θ a (M * b ^ k) x * (θ a M (x * b))⁻¹) := by
  have c1 := h.coc a M x b
  have c2 : θ a (M * x) b * θ a M x = θ a M (x * b) * θ a x b := by
    have e := h.coc M x b a
    rw [← cub_rot h a (M * x) b, ← cub_rot h a M x, ← cub_rot h a M (x * b), ← cub_rot h a x b] at e
    exact e
  simp only [hv, cubN]
  rw [prod_range_theta_mul_pow_eq_of_isCub h]
  exact mul_inv_rearrange_of_two_relations _ _ _ _ _ _ _ _ _ c1 c2

private lemma eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq {X Y R S F1 F0 : U} (e : X * R⁻¹ * S = Y * (F1 * F0⁻¹)) :
    X = Y * (F1 / F0) * R * S⁻¹ := by
  rw [div_eq_mul_inv, ← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem phiPow_indep (h : IsCub θ) (k : ℕ) (a b : A) :
    (∏ i ∈ Finset.range k, hv θ k (a * (b ^ k) ^ i) b (b ^ (k - 1 - i))) * cubN θ k 1 b a *
        (∏ i ∈ Finset.range k, θ a ((b ^ k) ^ i) b)⁻¹ =
      ∏ i ∈ Finset.range k, hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) := by
  have hf : ∀ i ∈ Finset.range k, hv θ k (a * (b ^ k) ^ i) b (b ^ (k - 1 - i)) =
      hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) *
        (θ a ((b ^ k) ^ (i + 1)) (b ^ (k - (i + 1))) / θ a ((b ^ k) ^ i) (b ^ (k - i))) *
        θ a ((b ^ k) ^ i) b * (θ a (b ^ (k - 1 - i)) b)⁻¹ := by
    intro i hi
    rw [Finset.mem_range] at hi
    have e := hv_term h k a ((b ^ k) ^ i) b (b ^ (k - 1 - i))
    have e1 : (b ^ k) ^ i * b ^ k = (b ^ k) ^ (i + 1) := (pow_succ _ _).symm
    have e2 : b ^ (k - 1 - i) * b = b ^ (k - i) := by
      rw [← pow_succ]
      congr 1
      omega
    have e3 : k - 1 - i = k - (i + 1) := by omega
    rw [e1, e2] at e
    rw [← e3]
    exact eq_mul_div_mul_mul_inv_of_mul_inv_mul_eq e
  have tel : ∏ i ∈ Finset.range k,
      (θ a ((b ^ k) ^ (i + 1)) (b ^ (k - (i + 1))) / θ a ((b ^ k) ^ i) (b ^ (k - i))) =
      θ a ((b ^ k) ^ k) (b ^ (k - k)) / θ a ((b ^ k) ^ 0) (b ^ (k - 0)) :=
    Finset.prod_range_div (fun j => θ a ((b ^ k) ^ j) (b ^ (k - j))) k
  have f1 : θ a ((b ^ k) ^ k) (b ^ (k - k)) = 1 := by
    rw [Nat.sub_self, pow_zero, ← cub_rot h 1 a, h.face]
  have f0 : θ a ((b ^ k) ^ 0) (b ^ (k - 0)) = 1 := by
    rw [pow_zero, cub_rot h a 1, h.face]
  have refl : ∏ i ∈ Finset.range k, θ a (b ^ (k - 1 - i)) b = ∏ i ∈ Finset.range k, θ a (b ^ i) b :=
    Finset.prod_range_reflect (fun j => θ a (b ^ j) b) k
  have cub : cubN θ k 1 b a = ∏ i ∈ Finset.range k, θ a (b ^ i) b := by
    simp only [cubN]
    apply Finset.prod_congr rfl
    intro i _
    rw [one_mul, cub_rot h a (b ^ i) b]
  rw [Finset.prod_congr rfl hf, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, Finset.prod_inv_distrib, tel, refl, cub, f1, f0]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_div, ofMul_one]
  abel

end ReciprocityTheory.ChartRestriction.G.H1
end
end
