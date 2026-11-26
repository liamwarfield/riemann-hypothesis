module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

namespace UpperTheory.Gal.W2.Seed

private lemma tyFn_mul_right {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a j : M) (hj : j ∈ J) :
    tyFn J ψ (a * j) = tyFn J ψ a * (((ψ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) := by
  unfold tyFn
  by_cases ha : a ∈ J
  · have haj : a * j ∈ J := J.mul_mem ha hj
    rw [dite_eq_left ha, dite_eq_left haj]
    have e : (⟨a * j, haj⟩ : J) = ⟨a, ha⟩ * ⟨j, hj⟩ := rfl
    rw [e, map_mul, mul_inv, Units.val_mul]
  · have haj : a * j ∉ J := fun h => ha ((J.mul_mem_cancel_right hj).1 h)
    rw [dite_eq_right ha, dite_eq_right haj, zero_mul]

private lemma tyFn_mul_left {M : Type} [Group M] (J : Subgroup M) (ψ : J →* ℂˣ) (a j : M) (hj : j ∈ J) :
    tyFn J ψ (j * a) = (((ψ ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) * tyFn J ψ a := by
  unfold tyFn
  by_cases ha : a ∈ J
  · have haj : j * a ∈ J := J.mul_mem hj ha
    rw [dite_eq_left ha, dite_eq_left haj]
    have e : (⟨j * a, haj⟩ : J) = ⟨j, hj⟩ * ⟨a, ha⟩ := rfl
    rw [e, map_mul, mul_inv, Units.val_mul]
  · have haj : j * a ∉ J := fun h => ha ((J.mul_mem_cancel_left hj).1 h)
    rw [dite_eq_right ha, dite_eq_right haj, mul_zero]

private lemma doset_left {X : Type} [Group X] (K : Subgroup X) (h k g : X) (hk : k ∈ K) :
    dosetInd ℂ K h (k * g) = dosetInd ℂ K h g := by
  have hiff : k * g ∈ DoubleCoset.doubleCoset h (K : Set X) (K : Set X) ↔
      g ∈ DoubleCoset.doubleCoset h (K : Set X) (K : Set X) := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨k⁻¹ * x, K.mul_mem (K.inv_mem hk) hx, y, hy, by
        rw [mul_assoc, mul_assoc, ← mul_assoc x, ← e, inv_mul_cancel_left]⟩
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨k * x, K.mul_mem hk hx, y, hy, by rw [e]; group⟩
  unfold dosetInd
  simp only [Set.indicator_apply, hiff, Pi.one_apply]

private lemma doset_right {X : Type} [Group X] (K : Subgroup X) (h k g : X) (hk : k ∈ K) :
    dosetInd ℂ K h (g * k) = dosetInd ℂ K h g := by
  have hiff : g * k ∈ DoubleCoset.doubleCoset h (K : Set X) (K : Set X) ↔
      g ∈ DoubleCoset.doubleCoset h (K : Set X) (K : Set X) := by
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    constructor
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨x, hx, y * k⁻¹, K.mul_mem hy (K.inv_mem hk), by
        rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    · rintro ⟨x, hx, y, hy, e⟩
      exact ⟨x, hx, y * k, K.mul_mem hy hk, by rw [e]; group⟩
  unfold dosetInd
  simp only [Set.indicator_apply, hiff, Pi.one_apply]

private lemma fin_reps {X : Type} [Group X] (A B : Subgroup X) (hAB : B.relIndex A ≠ 0) :
    ∃ R : Finset X, (∀ r ∈ R, r ∈ A) ∧ ∀ k ∈ A, ∃ r ∈ R, ∃ u ∈ B, k = r * u := by
  have hfin : Finite (A ⧸ B.subgroupOf A) := Subgroup.index_ne_zero_iff_finite.mp hAB
  haveI := Fintype.ofFinite (A ⧸ B.subgroupOf A)
  refine ⟨Finset.univ.image (fun q : A ⧸ B.subgroupOf A => ((q.out : A) : X)), ?_, ?_⟩
  · intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact (q.out).2
  · intro k hk
    set q : A ⧸ B.subgroupOf A := ((⟨k, hk⟩ : A) : A ⧸ B.subgroupOf A) with hq
    refine ⟨((q.out : A) : X), Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩,
      ((q.out : A) : X)⁻¹ * k, ?_, by group⟩
    have h1 : ((q.out : A) : A ⧸ B.subgroupOf A) = ((⟨k, hk⟩ : A) : A ⧸ B.subgroupOf A) := by
      rw [QuotientGroup.out_eq']
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
    simpa using h1

private lemma fin_doset {X M : Type} [Group X] [Group M] (T : TyLev X M) (h : X) :
    ∃ S : Finset X, ∀ g ∈ DoubleCoset.doubleCoset h (T.K : Set X) (T.K : Set X),
      ∃ s ∈ S, ∃ a b : T.K₀, g = (a : X) * s * b := by
  obtain ⟨R, -, hR⟩ := fin_reps T.K T.K₀ T.idx
  have hs := fun s : X => fin_reps T.K (T.K₀.map (MulAut.conj s).toMonoidHom)
    (Subgroup.relIndex_ne_zero_trans (T.cms s) T.idx)
  choose Rs _ hRs using hs
  refine ⟨R.biUnion (fun a => (Rs (h * a)).image (fun c => c * (h * a))), ?_⟩
  intro g hg
  obtain ⟨k, hk, k', hk', rfl⟩ := DoubleCoset.mem_doubleCoset.mp hg
  obtain ⟨a, ha, v, hv, rfl⟩ := hR k' hk'
  obtain ⟨c, hc, u, hu, rfl⟩ := hRs (h * a) k hk
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
  refine ⟨c * (h * a), Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩,
    1, ⟨t * v, T.K₀.mul_mem ht hv⟩, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, OneMemClass.coe_one, one_mul,
    Subgroup.coe_mul]
  group

theorem pTfAdm : TfAdm := by
  intro X M _ _ T h _
  have hlr : ∀ k (hk : k ∈ T.K) g, T.tf h (k * g) = (((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩)⁻¹ : ℂˣ) : ℂ) * T.tf h g ∧
      T.tf h (g * k) = (((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩)⁻¹ : ℂˣ) : ℂ) * T.tf h g := by
    intro k hk g
    constructor
    · unfold TyLev.tf
      rw [map_mul, tyFn_mul_left _ _ _ _ (T.fact.2 k hk), doset_left _ _ _ _ hk]
      ring
    · unfold TyLev.tf
      rw [map_mul, tyFn_mul_right _ _ _ _ (T.fact.2 k hk), doset_right _ _ _ _ hk]
      ring
  refine ⟨⟨?_, ?_, ?_⟩, hlr⟩
  · show IsBiInv T.K₀ (T.tf h) ∧ FinDosetSupp T.K₀ (T.tf h)
    constructor
    · intro a b g
      rw [(hlr b (T.le b.2) (a * g)).2, (hlr a (T.le a.2) g).1, T.ker a a.2, T.ker b b.2]
      simp
    · obtain ⟨S, hS⟩ := fin_doset T h
      refine ⟨S, fun g hg => hS g ?_⟩
      by_contra hn
      apply hg
      unfold TyLev.tf dosetInd
      rw [Set.indicator_of_notMem hn, mul_zero]
  · intro g hg
    by_contra hn
    apply hg
    unfold TyLev.tf tyFn
    rw [dite_eq_right hn]
    simp
  · intro j g
    have e : (⟨T.L.pr (T.L.loc j), T.fact.2 _ (T.fact.1 j j.2)⟩ : T.J) = j := Subtype.ext (T.L.pr_loc j)
    rw [(hlr _ (T.fact.1 j j.2) g).2, e]

end UpperTheory.Gal.W2.Seed
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PConvRing
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pConvRing :
    ConvRing := by
  intro X _ K hK f hf f' hf'
  refine ⟨Formalism.UG.Final.HeckeConvMem X K ℂ hK f hf f' hf', fun f'' hf'' => ?_⟩
  exact Formalism.UG.Final.HeckeAssoc X K ℂ hK f hf f' hf' f'' hf''
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAvgK
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pAvgK :
    ∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out := by
  intro X V _ _ _ K K₀ hle hidx Ψ hΨ
  haveI : Finite (K ⧸ K₀.subgroupOf K) := Nat.finite_of_card_ne_zero hidx
  haveI : Fintype (K ⧸ K₀.subgroupOf K) := Fintype.ofFinite _
  let e := Subgroup.quotientEquivProdOfLE hle
  let F : X ⧸ K → V := fun y => Ψ y.out
  have he : ∀ x : X ⧸ K₀, Ψ x.out = F (e x).1 := by
    intro x
    have h1 : (e x).1 = ((x.out : X) : X ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x.out
    simp only [F, h1, hk, hΨ k k.2]
  have hcard : Fintype.card (K ⧸ K₀.subgroupOf K) = K₀.relIndex K := by
    rw [Fintype.card_eq_nat_card]
    rfl
  have h2 : ∑ᶠ x : X ⧸ K₀, Ψ x.out = ∑ᶠ p : (X ⧸ K) × (K ⧸ K₀.subgroupOf K), F p.1 :=
    (finsum_congr he).trans (finsum_comp_equiv e (f := fun p => F p.1))
  rw [h2]
  by_cases hfin : (Function.support F).Finite
  · have hG : Function.HasFiniteSupport (fun p : (X ⧸ K) × (K ⧸ K₀.subgroupOf K) => F p.1) := by
      refine (hfin.prod (Set.finite_univ (α := K ⧸ K₀.subgroupOf K))).subset ?_
      intro p hp
      exact ⟨hp, trivial⟩
    rw [finsum_curry _ hG, smul_finsum]
    refine finsum_congr fun a => ?_
    show ∑ᶠ _ : K ⧸ K₀.subgroupOf K, Ψ a.out = _
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, hcard, Nat.cast_smul_eq_nsmul ℂ]
  · have h3 : ∑ᶠ y : X ⧸ K, Ψ y.out = 0 := finsum_of_infinite_support hfin
    rw [h3, smul_zero]
    apply finsum_of_infinite_support
    intro hG
    apply hfin
    refine (hG.image Prod.fst).subset ?_
    intro a ha
    exact ⟨(a, ((1 : K) : K ⧸ K₀.subgroupOf K)), ha, rfl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfCen
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfCen :
    (∀ (X V : Type) [Group X] [AddCommGroup V] [Module ℂ V] (K K₀ : Subgroup X), K₀ ≤ K → K₀.relIndex K ≠ 0 → ∀ Ψ : X → V, (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ x : X ⧸ K₀, Ψ x.out = ((K₀.relIndex K : ℕ) : ℂ) • ∑ᶠ y : X ⧸ K, Ψ y.out) → TfAdm → TfCen := by
  intro hsum hadm X M _ _ T z hz V _ _ Φ hΦ g
  have hidx : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr T.idx
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : X → V, ∀ x, Ψ x = T.tf z x • Φ (g * x) := ⟨_, fun _ => rfl⟩
  have hinv : ∀ k ∈ T.K, ∀ x, Ψ (x * k) = Ψ x := by
    intro k hk x
    have h1 := ((hadm X M T z hz.2).2 k hk x).2
    have h2 := hΦ k hk (g * x)
    rw [hΨ, hΨ, h1, ← mul_assoc, h2, smul_smul, mul_right_comm, Units.inv_mul, one_mul]
  have hsingle : ∑ᶠ y : X ⧸ T.K, Ψ y.out = Ψ z := by
    rw [finsum_eq_single _ (QuotientGroup.mk z : X ⧸ T.K)]
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul T.K z
      rw [hk]
      exact hinv k k.2 z
    · intro y hy
      have h0 : dosetInd ℂ T.K z y.out = 0 := by
        apply Set.indicator_of_notMem
        intro hm
        obtain ⟨a, ha, b, hb, e⟩ := DoubleCoset.mem_doubleCoset.mp hm
        have e' : y.out = z * (a * b) := by
          rw [e, ← hz.1 a, mul_assoc]
        have h2 : ((y.out : X) : X ⧸ T.K) = (z : X ⧸ T.K) := by
          rw [e']
          exact QuotientGroup.mk_mul_of_mem z (T.K.mul_mem ha hb)
        exact hy ((QuotientGroup.out_eq' y).symm.trans h2)
      rw [hΨ, TyLev.tf, h0, mul_zero, zero_smul]
  have hty : tyFn T.J T.ψ 1 = 1 := by
    unfold tyFn
    rw [dite_eq_left T.J.one_mem]
    have h1 : (⟨1, T.J.one_mem⟩ : T.J) = 1 := rfl
    rw [h1, map_one]
    simp
  have hdz : dosetInd ℂ T.K z z = 1 := by
    unfold dosetInd
    rw [Set.indicator_of_mem (DoubleCoset.mem_doubleCoset.mpr ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩)]
    rfl
  have hzz : T.tf z z = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ := by
    rw [TyLev.tf, hz.2, hty, hdz, mul_one, mul_one]
  have hs := hsum X V T.K T.K₀ T.le T.idx Ψ hinv
  unfold hAct
  simp only [hΨ] at hs hsingle
  rw [hs, hsingle, hzz, smul_smul, mul_inv_cancel₀ hidx, one_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfIdem
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

namespace UpperTheory.Gal.W2.Seed.TypeIdempotent

variable {X M : Type} [Group X] [Group M]

private theorem psi_inv (T : TyLev X M) (k : X) (hk : k ∈ T.K) (hk' : k⁻¹ ∈ T.K) :
    (((T.ψ ⟨T.L.pr k⁻¹, T.fact.2 _ hk'⟩)⁻¹ : ℂˣ) : ℂ) = ((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩ : ℂˣ) : ℂ) := by
  have e : (⟨T.L.pr k⁻¹, T.fact.2 _ hk'⟩ : T.J) = (⟨T.L.pr k, T.fact.2 k hk⟩ : T.J)⁻¹ := by
    ext
    simp
  rw [e, map_inv, inv_inv]

private theorem tf_right (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) (y : X) (c : T.K₀) :
    T.tf h (y * c) = T.tf h y := by
  have hk : (c : X) ∈ T.K := T.le c.2
  rw [((hA X M T h hh).2 c hk y).2, T.ker c c.2]
  simp

private theorem tf_left (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) (y : X) (c : T.K₀) :
    T.tf h ((c : X) * y) = T.tf h y := by
  have hk : (c : X) ∈ T.K := T.le c.2
  rw [((hA X M T h hh).2 c hk y).1, T.ker c c.2]
  simp

private theorem ty_act (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (Φ : X → V) (hΦ : ∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g) :
    T.IsTy (hAct T.K₀ (T.tf h) Φ) := by
  intro k hk g
  have hF : ∀ (y : X) (c : T.K₀), (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) (y * c) =
      (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) y := by
    intro y c
    simp only
    rw [← mul_assoc, tf_right hA T h hh _ c, ← mul_assoc, hΦ c c.2]
  have hs := P.finsum_out_mul T.K₀ k (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) hF
  simp only [inv_mul_cancel_left] at hs
  simp only [hAct, mul_assoc]
  rw [hs, smul_finsum]
  congr 1
  funext x
  rw [((hA X M T h hh).2 k⁻¹ (T.K.inv_mem hk) _).1, mul_smul, psi_inv T k hk (T.K.inv_mem hk)]

private theorem conv_left (hA : TfAdm) (hC : TfCen) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) :
    conv T.K₀ (T.tf 1) (T.tf h) = T.tf h := by
  funext g
  set Φ : X → ℂ := fun y => T.tf h (y⁻¹ * g) with hΦdef
  have hTy : T.IsTy Φ := by
    intro k hk y
    simp only [hΦdef, smul_eq_mul, mul_inv_rev, mul_assoc]
    rw [((hA X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1, psi_inv T k hk (T.K.inv_mem hk)]
  have hc := hC X M T 1 (by simp [TyLev.Cen]) ℂ Φ hTy 1
  simp only [hAct, conv, one_mul, mul_one, inv_one, smul_eq_mul, hΦdef] at hc ⊢
  exact hc

private theorem tf_one_not_mem (T : TyLev X M) (y : X) (hy : y ∉ T.K) : T.tf 1 y = 0 := by
  have hn : y ∉ DoubleCoset.doubleCoset (1 : X) (T.K : Set X) T.K := by
    rw [DoubleCoset.mem_doubleCoset]
    rintro ⟨a, ha, b, hb, rfl⟩
    exact hy (by simpa using T.K.mul_mem ha hb)
  simp [TyLev.tf, dosetInd, Set.indicator_apply, hn]

private theorem tf_one_one (T : TyLev X M) : T.tf 1 1 = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ := by
  have h1 : (1 : X) ∈ DoubleCoset.doubleCoset (1 : X) (T.K : Set X) T.K :=
    DoubleCoset.mem_doubleCoset.2 ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩
  have h2 : T.ψ ⟨1, T.J.one_mem⟩ = 1 := map_one T.ψ
  simp [TyLev.tf, tyFn, dosetInd, Set.indicator_apply, h1, T.J.one_mem, h2]

private theorem finsum_cosets (K K₀ : Subgroup X) (hle : K₀ ≤ K) (hi : K₀.relIndex K ≠ 0) (c : ℂ)
    (G : X ⧸ K₀ → ℂ) (h1 : ∀ z : X ⧸ K₀, z.out ∈ K → G z = c)
    (h0 : ∀ z : X ⧸ K₀, z.out ∉ K → G z = 0) :
    ∑ᶠ z, G z = ((K₀.relIndex K : ℕ) : ℂ) * c := by
  let φ : K ⧸ K₀.subgroupOf K → X ⧸ K₀ :=
    Quotient.map' (fun k : K => (k : X)) (fun a b hab => QuotientGroup.leftRel_apply.mpr (by
      have hab' := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using hab'))
  have hφ : ∀ k : K, φ (k : K ⧸ K₀.subgroupOf K) = ((k : X) : X ⧸ K₀) := fun k => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [hφ, hφ, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hab
  have hrange : ∀ z : X ⧸ K₀, z ∈ Set.range φ ↔ z.out ∈ K := by
    intro z
    constructor
    · rintro ⟨w, rfl⟩
      induction w using QuotientGroup.induction_on with | H k => ?_
      rw [hφ]
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K₀ (k : X)
      rw [hc]
      exact K.mul_mem k.2 (hle c.2)
    · intro hz
      refine ⟨((⟨z.out, hz⟩ : K) : K ⧸ K₀.subgroupOf K), ?_⟩
      rw [hφ]
      exact QuotientGroup.out_eq' z
  have hG : G = (Set.range φ).indicator (fun _ => c) := by
    funext z
    by_cases hz : z.out ∈ K
    · rw [Set.indicator_of_mem ((hrange z).2 hz), h1 z hz]
    · rw [Set.indicator_of_notMem (fun h => hz ((hrange z).1 h)), h0 z hz]
  rw [hG, ← finsum_mem_def, finsum_mem_range hinj]
  have hfin : Finite (K ⧸ K₀.subgroupOf K) := Nat.finite_of_card_ne_zero (by exact hi)
  haveI := Fintype.ofFinite (K ⧸ K₀.subgroupOf K)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  rfl

private theorem conv_right (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) :
    conv T.K₀ (T.tf h) (T.tf 1) = T.tf h := by
  funext g
  have hF : ∀ (y : X) (c : T.K₀), (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) (y * c) =
      (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) y := by
    intro y c
    simp only
    rw [tf_right hA T h hh y c, mul_inv_rev, mul_assoc,
      show ((c : X)⁻¹) = ((c⁻¹ : T.K₀) : X) from rfl, tf_left hA T 1 (map_one _) (y⁻¹ * g) c⁻¹]
  have hs := P.finsum_out_mul T.K₀ g (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) hF
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at hs
  simp only [conv]
  rw [← hs]
  rw [finsum_cosets T.K T.K₀ T.le T.idx (((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ * T.tf h g) _ ?_ ?_]
  · have hne : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 T.idx
    field_simp
  · intro z hz
    have hz' : (z.out)⁻¹ ∈ T.K := T.K.inv_mem hz
    rw [((hA X M T h hh).2 _ hz g).2]
    have e := ((hA X M T 1 (map_one _)).2 _ hz' 1).1
    rw [mul_one] at e
    rw [e, tf_one_one, psi_inv T _ hz hz']
    have hu := Units.inv_mul (T.ψ ⟨T.L.pr z.out, T.fact.2 _ hz⟩)
    linear_combination (T.tf h g * ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹) * hu
  · intro z hz
    rw [tf_one_not_mem T _ (fun h' => hz (by simpa using T.K.inv_mem h')), mul_zero]

end UpperTheory.Gal.W2.Seed.TypeIdempotent

open UpperTheory.Gal.W2.Seed.TypeIdempotent in
theorem UpperTheory.Gal.W2.Seed.pTfIdem : TfAdm → TfCen → TfIdem := by
  intro hA hC X M _ _ T h hh
  exact ⟨fun V _ _ Φ hΦ => ty_act hA T h hh Φ hΦ, conv_right hA T h hh, conv_left hA hC T h hh⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfComm
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem comm_conv (hRing : ConvRing) {X : Type} [Group X] {K : Subgroup X} (hK : IsCommensurated K)
    {f g h : X → ℂ} (hf : f ∈ Hecke ℂ K) (hg : g ∈ Hecke ℂ K) (hh : h ∈ Hecke ℂ K)
    (c₁ : conv K f h = conv K h f) (c₂ : conv K g h = conv K h g) :
    conv K (conv K f g) h = conv K h (conv K f g) := by
  calc conv K (conv K f g) h = conv K f (conv K g h) := (hRing X K hK f hf g hg).2 h hh
    _ = conv K f (conv K h g) := by rw [c₂]
    _ = conv K (conv K f h) g := ((hRing X K hK f hf h hh).2 g hg).symm
    _ = conv K (conv K h f) g := by rw [c₁]
    _ = conv K h (conv K f g) := (hRing X K hK h hh f hf).2 g hg

private theorem comm_cen (hAdm : TfAdm) (hCen : TfMulCen) (hRing : ConvRing) {X M : Type} [Group X] [Group M]
    (T : TyLev X M) {a b z z' : X} (ha : T.L.pr a = 1) (hb : T.L.pr b = 1) (hz : T.Cen z) (hz' : T.Cen z')
    (hab : conv T.K₀ (T.tf a) (T.tf b) = conv T.K₀ (T.tf b) (T.tf a)) :
    conv T.K₀ (T.tf (a * z)) (T.tf (b * z')) = conv T.K₀ (T.tf (b * z')) (T.tf (a * z)) := by
  have hK := T.cms
  have mA := (hAdm X M T a ha).1.1
  have mB := (hAdm X M T b hb).1.1
  have mZ := (hAdm X M T z hz.2).1.1
  have mZ' := (hAdm X M T z' hz'.2).1.1
  have cz := hCen X M T a z ha hz
  have cz' := hCen X M T b z' hb hz'
  have eBZ : conv T.K₀ (T.tf b) (T.tf z) = conv T.K₀ (T.tf z) (T.tf b) :=
    (hCen X M T b z hb hz).2.trans (hCen X M T b z hb hz).1.symm
  have eAZ' : conv T.K₀ (T.tf a) (T.tf z') = conv T.K₀ (T.tf z') (T.tf a) :=
    (hCen X M T a z' ha hz').2.trans (hCen X M T a z' ha hz').1.symm
  have eZZ' : conv T.K₀ (T.tf z) (T.tf z') = conv T.K₀ (T.tf z') (T.tf z) :=
    (hCen X M T z z' hz.2 hz').2.trans (hCen X M T z z' hz.2 hz').1.symm
  have mAZ := (hRing X T.K₀ hK _ mA _ mZ).1
  have h1 := comm_conv hRing hK mA mZ mB hab eBZ.symm
  have h2 := comm_conv hRing hK mA mZ mZ' eAZ' eZZ'
  have h3 := comm_conv hRing hK mB mZ' mAZ h1.symm h2.symm
  rw [← cz.2, ← cz'.2]
  exact h3.symm

theorem UpperTheory.Gal.W2.Seed.pTfComm : TfAdm → ConvRing → TfMulCen → TfMulL → TfMulR → TfLoc → TfComm := by
  intro hAdm hRing hCen hL hR hLoc X M M' M'' _ _ _ _ T L' Kw hF hAp z z' hz hz' t
  refine ⟨fun L'' t' h1 h2 => ?_, fun t' hc => ?_⟩
  · have ha : T.L.pr (L'.loc t) = 1 := hAp.1 t
    have hb : T.L.pr (L''.loc t') = 1 := h1.1 t'
    have hb' : L'.pr (L''.loc t') = 1 := h2.1 t'
    exact comm_cen hAdm hCen hRing T ha hb hz hz'
      ((hL X M M' T L' Kw hF hAp t _ hb hb').trans (hR X M M' T L' Kw hF hAp t _ hb hb').symm)
  · have ha : T.L.pr (L'.loc t) = 1 := hAp.1 t
    have hb : T.L.pr (L'.loc t') = 1 := hAp.1 t'
    refine comm_cen hAdm hCen hRing T ha hb hz hz' ?_
    funext g
    rw [hLoc X M M' T L' Kw hF hAp t t' g, hLoc X M M' T L' Kw hF hAp t' t g, hc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulCen
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem UpperTheory.Gal.W2.Seed.tf_mul_cen_apply {X M : Type} [Group X] [Group M] (T : TyLev X M)
    (h z : X) (hz : T.Cen z) (g : X) : T.tf (h * z) g = T.tf h (z⁻¹ * g) := by
  have hzc := hz.1
  have hpr : T.L.pr (z⁻¹ * g) = T.L.pr g := by
    rw [map_mul, map_inv, hz.2, inv_one, one_mul]
  have key : ∀ a b : X, a * (h * z) * b = z * (a * h * b) := by
    intro a b
    calc a * (h * z) * b = a * h * (z * b) := by group
      _ = a * h * (b * z) := by rw [hzc b]
      _ = (a * h * b) * z := by group
      _ = z * (a * h * b) := (hzc _).symm
  have hmem : g ∈ DoubleCoset.doubleCoset (h * z) (T.K : Set X) T.K ↔
      z⁻¹ * g ∈ DoubleCoset.doubleCoset h (T.K : Set X) T.K := by
    simp only [DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, by rw [key]; group⟩
    · rintro ⟨a, ha, b, hb, he⟩
      refine ⟨a, ha, b, hb, ?_⟩
      rw [key, ← he]
      group
  simp only [TyLev.tf, dosetInd, hpr, Set.indicator_apply, hmem, Pi.one_apply]

theorem UpperTheory.Gal.W2.Seed.pTfMulCen :
    TfAdm → TfCen → TfIdem → TfMulCen := by
  intro hAdm hCen hIdem X M _ _ T h z hh hz
  have hzc : ∀ y : X, z⁻¹ * y = y * z⁻¹ := fun y => (Commute.inv_left (hz.1 y : Commute z y)).eq
  refine ⟨?_, ?_⟩
  · funext g
    have hty : T.IsTy (V := ℂ) (fun y : X => T.tf h (y⁻¹ * g)) := by
      intro k hk y
      have e := ((hAdm X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1
      simp only [mul_inv_rev, mul_assoc]
      rw [e]
      simp only [map_inv, smul_eq_mul]
      congr 1
      rw [← map_inv]
      exact congrArg (fun u => ((T.ψ u : ℂˣ) : ℂ)) (Subtype.ext (inv_inv _))
    have e := hCen X M T z hz ℂ (fun y => T.tf h (y⁻¹ * g)) hty 1
    simp only [hAct, one_mul, smul_eq_mul] at e
    simp only [conv]
    rw [e, tf_mul_cen_apply T h z hz g]
  · funext g
    have e1 : conv T.K₀ (T.tf h) (T.tf z) g = conv T.K₀ (T.tf h) (T.tf 1) (z⁻¹ * g) := by
      simp only [conv]
      refine finsum_congr fun x => ?_
      congr 1
      have e := tf_mul_cen_apply T 1 z hz (x.out⁻¹ * g)
      rw [one_mul] at e
      rw [e, ← mul_assoc, ← mul_assoc, hzc]
    rw [e1, (hIdem X M T h hh).2.1, tf_mul_cen_apply T h z hz g]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfLoc
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfLoc :
    TfAdm → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfLoc := by
  intro hAdm hAc hDec X M M' _ _ _ T L' Kw hF hAp t t' g
  set Φ : X → ℂ := fun y => T.tf (L'.loc t') (y⁻¹ * g) with hΦ
  have key : ∀ (a b : T.J), (a : M) = (b : M)⁻¹ → (((T.ψ a)⁻¹ : ℂˣ) : ℂ) = (T.ψ b : ℂ) := by
    intro a b hab
    have hab' : a = b⁻¹ := Subtype.ext (by simpa using hab)
    subst hab'
    simp
  have hTy : T.IsTy Φ := by
    intro k hk y
    have hp : T.L.pr (L'.loc t') = 1 := hAp.1 t'
    have h1 := ((hAdm X M T (L'.loc t') hp).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1
    simp only [hΦ, smul_eq_mul, mul_inv_rev, mul_assoc]
    rw [h1]
    congr 1
    exact key _ _ (by simp)
  have hsum := hAc X M M' T L' Kw hF hAp t 1 (by simp [TyLev.Cen]) ℂ Φ hTy 1
  have hL : conv T.K₀ (T.tf (L'.loc t)) (T.tf (L'.loc t')) g = hAct T.K₀ (T.tf (L'.loc t * 1)) Φ 1 := by
    simp only [conv, hAct, mul_one, one_mul, smul_eq_mul, hΦ]
  have hpt : ∀ m : M', Φ (L'.loc m) = T.tf 1 (g * (L'.loc (L'.pr g))⁻¹) * dosetInd ℂ Kw t' (m⁻¹ * L'.pr g) := by
    intro m
    have e1 : T.L.pr ((L'.loc m)⁻¹ * g) = T.L.pr g := by simp [hAp.1 m]
    have e2 : T.L.pr ((L'.loc (L'.pr g))⁻¹ * g) = T.L.pr g := by simp [hAp.1]
    have hu : g * (L'.loc (L'.pr g))⁻¹ = (L'.loc (L'.pr g))⁻¹ * g := by
      have h0 : L'.pr ((L'.loc (L'.pr g))⁻¹ * g) = 1 := by simp [L'.pr_loc]
      have hc := L'.comm (L'.pr g) _ h0
      calc g * (L'.loc (L'.pr g))⁻¹
          = (L'.loc (L'.pr g) * ((L'.loc (L'.pr g))⁻¹ * g)) * (L'.loc (L'.pr g))⁻¹ := by simp
        _ = (((L'.loc (L'.pr g))⁻¹ * g) * L'.loc (L'.pr g)) * (L'.loc (L'.pr g))⁻¹ := by rw [hc]
        _ = (L'.loc (L'.pr g))⁻¹ * g := by simp
    have hmem : (L'.loc m)⁻¹ * g ∈ DoubleCoset.doubleCoset (L'.loc t') (T.K : Set X) T.K ↔
        m⁻¹ * L'.pr g ∈ DoubleCoset.doubleCoset t' (Kw : Set M') Kw ∧
          (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset 1 (T.K : Set X) T.K := by
      have h3 : L'.pr ((L'.loc m)⁻¹ * g) = m⁻¹ * L'.pr g := by simp [L'.pr_loc]
      have h4 : (L'.loc (m⁻¹ * L'.pr g))⁻¹ * ((L'.loc m)⁻¹ * g) = (L'.loc (L'.pr g))⁻¹ * g := by
        simp [mul_assoc]
      have hd := hDec X M' L' T.K Kw hF t' 1 (map_one _) ((L'.loc m)⁻¹ * g)
      rw [mul_one, h3, h4] at hd
      exact hd
    simp only [hΦ, TyLev.tf]
    rw [hu, e1, e2]
    simp only [dosetInd, Set.indicator_apply, hmem, Pi.one_apply]
    by_cases ha : m⁻¹ * L'.pr g ∈ DoubleCoset.doubleCoset t' (Kw : Set M') Kw <;>
      by_cases hb : (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset 1 (T.K : Set X) T.K <;>
      simp [ha, hb]
  rw [hL, hsum]
  simp only [one_mul, smul_eq_mul, hpt, conv]
  rw [mul_finsum]
  congr 1
  ext x
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetIff
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem loc_split {X M' : Type} [Group X] [Group M'] (L' : Loc X M') {K : Subgroup X} {Kw : Subgroup M'}
    (hF : L'.Fact K Kw) {k : X} (hk : k ∈ K) :
    ∃ a ∈ Kw, ∃ k₀ ∈ K, L'.pr k₀ = 1 ∧ k = L'.loc a * k₀ := by
  refine ⟨L'.pr k, hF.2 k hk, (L'.loc (L'.pr k))⁻¹ * k, K.mul_mem (K.inv_mem (hF.1 _ (hF.2 k hk))) hk, ?_, by group⟩
  simp [L'.pr_loc]

private theorem loc_key {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (a t b : M') {k₀ r k₁ : X}
    (h₀ : L'.pr k₀ = 1) (hr : L'.pr r = 1) (h₁ : L'.pr k₁ = 1) :
    L'.loc a * k₀ * (L'.loc t * r) * (k₁ * L'.loc b) = L'.loc (a * t * b) * (k₀ * r * k₁) := by
  have hprod : L'.pr (k₀ * r * k₁) = 1 := by simp [map_mul, h₀, hr, h₁]
  have e1 := L'.comm t k₀ h₀
  have e2 := L'.comm b (k₀ * r * k₁) hprod
  rw [map_mul, map_mul]
  calc L'.loc a * k₀ * (L'.loc t * r) * (k₁ * L'.loc b)
      = L'.loc a * (k₀ * L'.loc t) * r * k₁ * L'.loc b := by group
    _ = L'.loc a * (L'.loc t * k₀) * r * k₁ * L'.loc b := by rw [e1]
    _ = L'.loc a * L'.loc t * ((k₀ * r * k₁) * L'.loc b) := by group
    _ = L'.loc a * L'.loc t * L'.loc b * (k₀ * r * k₁) := by rw [← e2]; group

theorem UpperTheory.Gal.W2.Seed.pDosetIff :
    ∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K := by
  intro X M' _ _ L' K Kw hF t r hr g
  constructor
  · intro hg
    rw [DoubleCoset.mem_doubleCoset] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := hg
    obtain ⟨a, ha, k₀, hk₀, h₀, rfl⟩ := loc_split L' hF hx
    obtain ⟨b, hb, k₁, hk₁, h₁, rfl⟩ := loc_split L' hF hy
    have hc : L'.loc b * k₁ = k₁ * L'.loc b := L'.comm b k₁ h₁
    rw [hc, loc_key L' a t b h₀ hr h₁]
    have hpr : L'.pr (L'.loc (a * t * b) * (k₀ * r * k₁)) = a * t * b := by
      simp [map_mul, h₀, hr, h₁, L'.pr_loc]
    rw [hpr]
    refine ⟨?_, ?_⟩
    · rw [DoubleCoset.mem_doubleCoset]
      exact ⟨a, ha, b, hb, rfl⟩
    · rw [DoubleCoset.mem_doubleCoset, inv_mul_cancel_left]
      exact ⟨k₀, hk₀, k₁, hk₁, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [DoubleCoset.mem_doubleCoset] at h1 h2 ⊢
    obtain ⟨a, ha, b, hb, hab⟩ := h1
    obtain ⟨k₀, hk₀, k₁, hk₁, hk⟩ := h2
    have hg : g = L'.loc (L'.pr g) * (k₀ * r * k₁) := by
      rw [← hk]
      group
    have hpg := congrArg L'.pr hg
    simp only [map_mul, L'.pr_loc, hr, mul_one] at hpg
    have hpk : L'.pr k₀ * L'.pr k₁ = 1 := by
      calc L'.pr k₀ * L'.pr k₁ = (L'.pr g)⁻¹ * (L'.pr g * (L'.pr k₀ * L'.pr k₁)) := by group
        _ = 1 := by rw [← hpg]; group
    have hcr := L'.comm (L'.pr k₀) r hr
    have hk0 : L'.pr (k₀ * (L'.loc (L'.pr k₀))⁻¹) = 1 := by
      simp [map_mul, map_inv, L'.pr_loc]
    have hk1 : L'.pr (L'.loc (L'.pr k₀) * k₁) = 1 := by
      rw [map_mul, L'.pr_loc, hpk]
    have hsplit : k₀ * r * k₁ =
        k₀ * (L'.loc (L'.pr k₀))⁻¹ * r * (L'.loc (L'.pr k₀) * k₁) := by
      calc k₀ * r * k₁ = k₀ * (L'.loc (L'.pr k₀))⁻¹ * (L'.loc (L'.pr k₀) * r) * k₁ := by group
        _ = _ := by rw [hcr]; group
    refine ⟨L'.loc a * (k₀ * (L'.loc (L'.pr k₀))⁻¹), ?_, L'.loc (L'.pr k₀) * k₁ * L'.loc b, ?_, ?_⟩
    · exact K.mul_mem (hF.1 a ha) (K.mul_mem hk₀ (K.inv_mem (hF.1 _ (hF.2 _ hk₀))))
    · exact K.mul_mem (K.mul_mem (hF.1 _ (hF.2 _ hk₀)) hk₁) (hF.1 b hb)
    · rw [loc_key L' a t b hk0 hr hk1, ← hab, ← hsplit]
      exact hg
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDosetCosets
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

private theorem mul_mem_doubleCoset_iff_of_mem {X : Type} [Group X] (K : Subgroup X) (a g k : X) (hk : k ∈ K) :
    g * k ∈ DoubleCoset.doubleCoset a (K : Set X) K ↔ g ∈ DoubleCoset.doubleCoset a (K : Set X) K := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y * k⁻¹, K.mul_mem hy (K.inv_mem hk), by rw [← mul_assoc, ← h, mul_inv_cancel_right]⟩
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨x, hx, y * k, K.mul_mem hy hk, by rw [h, mul_assoc]⟩

private theorem loc_mem_doubleCoset_loc_iff {X M' : Type} [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X)
    (Kw : Subgroup M') (hF : L'.Fact K Kw) (t z : M') :
    L'.loc z ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K ↔
      z ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw := by
  simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    refine ⟨L'.pr x, hF.2 x hx, L'.pr y, hF.2 y hy, ?_⟩
    have h' := congrArg L'.pr h
    simpa [map_mul, L'.pr_loc] using h'
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨L'.loc x, hF.1 x hx, L'.loc y, hF.1 y hy, by rw [h, map_mul, map_mul]⟩

theorem UpperTheory.Gal.W2.Seed.pDosetCosets :
    ∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := by
  intro X M' _ _ L' K Kw hF t V _ _ Ψ hΨ
  set f : X ⧸ K → V := fun y => dosetInd ℂ K (L'.loc t) y.out • Ψ y.out with hf
  let φ : M' ⧸ Kw → X ⧸ K := fun x => ((L'.loc x.out : X) : X ⧸ K)
  have hφ : Function.Injective φ := by
    intro x x' h
    simp only [φ, QuotientGroup.eq] at h
    rw [← QuotientGroup.out_eq' x, ← QuotientGroup.out_eq' x', QuotientGroup.eq]
    have h2 := hF.2 _ h
    simpa [map_mul, map_inv, L'.pr_loc] using h2
  have hφf : ∀ x, f (φ x) = dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out) := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (L'.loc x.out)
    simp only [hf, φ, hk]
    rw [hΨ k k.2]
    simp only [dosetInd, Set.indicator, mul_mem_doubleCoset_iff_of_mem K _ _ _ k.2, loc_mem_doubleCoset_loc_iff L' K Kw hF,
      Pi.one_apply]
  have hsupp : Function.support f ⊆ Set.range φ := by
    intro y hy
    rw [Function.mem_support] at hy
    have hmem : y.out ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K := by
      by_contra hn
      apply hy
      simp [hf, dosetInd, hn]
    rw [DoubleCoset.mem_doubleCoset] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    refine ⟨((L'.pr a * t : M') : M' ⧸ Kw), ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul Kw (L'.pr a * t)
    simp only [φ, hk]
    rw [← QuotientGroup.out_eq' y, QuotientGroup.eq]
    set n := a * (L'.loc (L'.pr a))⁻¹ with hn
    have hn1 : L'.pr n = 1 := by simp [hn, L'.pr_loc]
    have hnK : n ∈ K := K.mul_mem ha (K.inv_mem (hF.1 _ (hF.2 a ha)))
    have hy' : y.out = L'.loc (L'.pr a * t) * (n * b) := by
      calc y.out = a * L'.loc t * b := hab
        _ = n * L'.loc (L'.pr a * t) * b := by simp [hn, map_mul, mul_assoc]
        _ = L'.loc (L'.pr a * t) * n * b := by rw [L'.comm _ n hn1]
        _ = _ := mul_assoc _ _ _
    rw [hy', map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact K.mul_mem (K.inv_mem (hF.1 _ k.2)) (K.mul_mem hnK hb)
  calc ∑ᶠ y : X ⧸ K, f y = ∑ᶠ y ∈ Set.range φ, f y := by
        rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp]
    _ = ∑ᶠ x, f (φ x) := finsum_mem_range hφ
    _ = _ := finsum_congr hφf
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfMulL
open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

theorem UpperTheory.Gal.W2.Seed.pTfMulL :
    TfAdm → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (r : X), L'.pr r = 1 → ∀ g, g ∈ DoubleCoset.doubleCoset (L'.loc t * r) (K : Set X) K ↔ L'.pr g ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw ∧ (L'.loc (L'.pr g))⁻¹ * g ∈ DoubleCoset.doubleCoset r (K : Set X) K) → TfMulL := by
  intro hAdm hAc hIff X M M' _ _ _ T L' Kw hF hAp t r hr hr'
  funext g₀
  set Φ : X → ℂ := fun y => T.tf r (y⁻¹ * g₀) with hΦ
  have hTy : T.IsTy Φ := by
    intro k hk g
    have hki : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [hΦ, mul_inv_rev, mul_assoc]
    rw [((hAdm X M T r hr).2 k⁻¹ hki (g⁻¹ * g₀)).1, smul_eq_mul]
    congr 2
    have e : (⟨T.L.pr k⁻¹, T.fact.2 _ hki⟩ : T.J) = (⟨T.L.pr k, T.fact.2 _ hk⟩ : T.J)⁻¹ :=
      Subtype.ext (map_inv _ _)
    rw [e, map_inv, inv_inv]
  have key := hAc X M M' T L' Kw hF hAp t 1 ⟨fun g => by group, map_one _⟩ ℂ Φ hTy 1
  have lhs : conv T.K₀ (T.tf (L'.loc t)) (T.tf r) g₀ = Formalism.UG.hAct T.K₀ (T.tf (L'.loc t * 1)) Φ 1 := by
    simp [conv, Formalism.UG.hAct, hΦ, smul_eq_mul]
  rw [lhs, key]
  have memKrK : ∀ y, y ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K → L'.pr y ∈ Kw := by
    intro y hy
    rw [DoubleCoset.mem_doubleCoset] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hy
    simp only [map_mul, hr', mul_one]
    exact Kw.mul_mem (hF.2 a ha) (hF.2 b hb)
  simp only [hΦ, one_mul, smul_eq_mul]
  rw [finsum_eq_single _ ((L'.pr g₀ : M' ⧸ Kw)) ?_]
  · obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul Kw (L'.pr g₀)
    rw [hw]
    have h1 : (L'.pr g₀ * w ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw) ↔
        L'.pr g₀ ∈ DoubleCoset.doubleCoset t (Kw : Set M') Kw := by
      simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, b, hb, e⟩
        refine ⟨a, ha, b * (w : M')⁻¹, Kw.mul_mem hb (Kw.inv_mem w.2), ?_⟩
        calc L'.pr g₀ = L'.pr g₀ * w * (w : M')⁻¹ := by group
          _ = a * t * b * (w : M')⁻¹ := by rw [e]
          _ = a * t * (b * (w : M')⁻¹) := by group
      · rintro ⟨a, ha, b, hb, e⟩
        exact ⟨a, ha, b * w, Kw.mul_mem hb w.2, by rw [e]; group⟩
    have h2 : ((L'.loc (L'.pr g₀ * w))⁻¹ * g₀ ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K) ↔
        (L'.loc (L'.pr g₀))⁻¹ * g₀ ∈ DoubleCoset.doubleCoset r (T.K : Set X) T.K := by
      have hwK : L'.loc w ∈ T.K := hF.1 w w.2
      have e : (L'.loc (L'.pr g₀ * w))⁻¹ * g₀ = (L'.loc w)⁻¹ * ((L'.loc (L'.pr g₀))⁻¹ * g₀) := by
        rw [map_mul, mul_inv_rev, mul_assoc]
      rw [e]
      simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
      constructor
      · rintro ⟨a, ha, b, hb, e2⟩
        refine ⟨L'.loc w * a, T.K.mul_mem hwK ha, b, hb, ?_⟩
        calc (L'.loc (L'.pr g₀))⁻¹ * g₀
            = L'.loc w * ((L'.loc w)⁻¹ * ((L'.loc (L'.pr g₀))⁻¹ * g₀)) := by group
          _ = L'.loc w * (a * r * b) := by rw [e2]
          _ = L'.loc w * a * r * b := by group
      · rintro ⟨a, ha, b, hb, e2⟩
        exact ⟨(L'.loc w)⁻¹ * a, T.K.mul_mem (T.K.inv_mem hwK) ha, b, hb, by rw [e2]; group⟩
    have hprm : ∀ m, T.L.pr ((L'.loc m)⁻¹ * g₀) = T.L.pr g₀ := by
      intro m
      rw [map_mul, map_inv, hAp.1, inv_one, one_mul]
    simp only [TyLev.tf, dosetInd, Set.indicator_apply, Pi.one_apply, hprm, h1, h2,
      hIff X M' L' T.K Kw hF t r hr' g₀]
    split_ifs <;> simp_all
  · intro x hx
    have hy : (L'.loc (Quotient.out x))⁻¹ * g₀ ∉ DoubleCoset.doubleCoset r (T.K : Set X) T.K := by
      intro hm
      apply hx
      have hh := memKrK _ hm
      rw [map_mul, map_inv, L'.pr_loc] at hh
      rw [← QuotientGroup.out_eq' x]
      exact QuotientGroup.eq.2 hh
    simp [TyLev.tf, dosetInd, Set.indicator_apply, hy]
end
