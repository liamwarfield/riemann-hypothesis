module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleGlobalSectionsFunctionFieldIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)

noncomputable section

namespace GlobalTheory.VolFin

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def gen (U : X.Opens) (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U _ h).hom

theorem generic_mem {U : X.Opens} {x : X} (hx : x ∈ U) : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 ⟨x, trivial, hx⟩

theorem gen_rs {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    gen V hV (rs X h a) = gen U (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a

theorem gen_injective (U : X.Opens) (h : genericPoint X ∈ U) : Function.Injective (gen U h) :=
  germ_injective_of_isIntegral X _ h

theorem eq_of_gen {U : X.Opens} {a b : Γ(X, U)} (h : ∀ hU, gen U hU a = gen U hU b) : a = b := by
  by_cases hU : genericPoint X ∈ U
  · exact gen_injective U hU (h hU)
  · have hb : U = ⊥ := by
      ext x
      exact ⟨fun hx => (hU (generic_mem hx)).elim, fun hx => hx.elim⟩
    subst hb
    exact Subsingleton.elim _ _

theorem exists_gen_eq (U : X.Opens) (f : X.functionField)
    (hf : ∀ x ∈ U, ∃ (V : X.Opens) (hx : x ∈ V) (a : Γ(X, V)), gen V (generic_mem hx) a = f) :
    ∃ a : Γ(X, U), ∀ hU, gen U hU a = f := by
  choose V hx a ha using hf
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => U ⊓ V x.1 x.2) U
    (fun x => homOfLE inf_le_left)
    (fun x hxU => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hxU, hx x hxU⟩)
    (fun x => rs X inf_le_right (a x.1 x.2))
    (fun x y => eq_of_gen (X := X) fun h =>
      ((gen_rs inf_le_left h _).trans ((gen_rs _ _ _).trans (ha _ _))).trans
        ((gen_rs inf_le_right h _).trans ((gen_rs _ _ _).trans (ha _ _))).symm)
  refine ⟨s, fun hU => ?_⟩
  have h1 : rs X (inf_le_left : U ⊓ V _ hU ≤ U) s = rs X inf_le_right (a _ hU) := hs ⟨_, hU⟩
  exact (gen_rs (inf_le_left : U ⊓ V _ hU ≤ U) ⟨hU, hx _ hU⟩ s).symm.trans
    ((congrArg _ h1).trans ((gen_rs _ _ _).trans (ha _ _)))

def tr (N : LB X) (i j : N.ι) (hi : genericPoint X ∈ N.U i) (hj : genericPoint X ∈ N.U j) :
    X.functionField := gen (N.U i ⊓ N.U j) ⟨hi, hj⟩ (N.g i j).val

theorem tr_mul {N : LB X} (hN : N.IsLB) (i j k : N.ι) (hi) (hj) (hk) :
    tr N i j hi hj * tr N j k hj hk = tr N i k hi hk := by
  have h := congrArg (fun u => gen (N.U i ⊓ N.U j ⊓ N.U k) ⟨⟨hi, hj⟩, hk⟩ (Units.val u))
    (hN.cocycle i j k)
  simp only [Units.val_mul, map_mul] at h
  exact (congrArg₂ (· * ·) (gen_rs _ _ _) (gen_rs _ _ _)).symm.trans (h.trans (gen_rs _ _ _))

theorem tr_ne_zero (N : LB X) (i j : N.ι) (hi) (hj) : tr N i j hi hj ≠ 0 :=
  ((N.g i j).isUnit.map _).ne_zero

theorem tr_self {N : LB X} (hN : N.IsLB) (i : N.ι) (hi) : tr N i i hi hi = 1 :=
  mul_left_cancel₀ (tr_ne_zero N i i hi hi) ((tr_mul hN i i i hi hi hi).trans (_root_.mul_one _).symm)

theorem gen_sec {N : LB X} (s : N.Sec) (i j : N.ι) (hi) (hj) :
    gen _ hi (s.f i) = tr N i j hi hj * gen _ hj (s.f j) := by
  have h := congrArg (gen (N.U i ⊓ N.U j) ⟨hi, hj⟩) (s.compat i j)
  rw [map_mul] at h
  exact (gen_rs _ _ _).symm.trans (h.trans (congrArg _ (gen_rs _ _ _)))

theorem gen_constFn (p : X ⟶ Sp K) (U : X.Opens) (h) (a : K) :
    gen U h (constFn p U a) = gen ⊤ trivial (constFn p ⊤ a) := by
  rw [← gen_rs le_top h]
  congr 1
  exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := ⊤) (fun _ _ => trivial) (homOfLE (le_top : U ≤ ⊤)).op)).symm

theorem exists_sec {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (f : X.functionField)
    (hf : ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) :
    ∃ s : N.Sec, gen _ h₀ (s.f j₀) = f := by
  have H : ∀ j, ∃ a : Γ(X, N.U j), ∀ hj, gen _ hj a = tr N j j₀ hj h₀ * f := by
    intro j
    by_cases hj : genericPoint X ∈ N.U j
    · obtain ⟨a, ha⟩ := exists_gen_eq (N.U j) (tr N j j₀ hj h₀ * f) fun x hx => by
        obtain ⟨i, hi⟩ := hc x
        obtain ⟨a, ha⟩ := hf i
        refine ⟨N.U j ⊓ W i, ⟨hx, hi⟩,
          rs X (inf_le_inf_left _ (hW i)) (N.g j (c i)).val * rs X inf_le_right a, ?_⟩
        rw [map_mul, gen_rs, gen_rs, ha, ← tr_mul hN j (c i) j₀ hj (hW i (hη i)) h₀]
        unfold tr
        ring
      exact ⟨a, ha⟩
    · exact ⟨0, fun h => (hj h).elim⟩
  choose a ha using H
  refine ⟨⟨a, fun i j => eq_of_gen fun h => ?_⟩, ?_⟩
  · rw [map_mul]
    refine (gen_rs _ _ _).trans ((ha i h.1).trans ?_)
    rw [← tr_mul hN i j j₀ h.1 h.2 h₀, _root_.mul_assoc, ← ha j h.2]
    exact congrArg _ (gen_rs (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) h (a j)).symm
  · rw [ha, tr_self hN, _root_.one_mul]

theorem lineBundle_global_sections_functionField_iff [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (V : Submodule K X.functionField)
    (hV : ∀ f, f ∈ V ↔ ∀ i, ∃ a, gen (W i) (hη i) a = f * tr N (c i) j₀ (hW i (hη i)) h₀) (r : ℕ) :
    SectionsHaveFiniteDimension p N r ↔ Module.Finite K V ∧ Module.finrank K V = r := by
  let θ : N.Sec → V := fun s => ⟨gen _ h₀ (s.f j₀), (hV _).2 fun i =>
    ⟨rs X (hW i) (s.f (c i)), by rw [gen_rs, gen_sec s (c i) j₀ _ h₀, _root_.mul_comm]⟩⟩
  have hθ : Function.Surjective θ := fun f => by
    obtain ⟨s, hs⟩ := exists_sec hN j₀ h₀ W c hW hη hc f ((hV f).1 f.2)
    exact ⟨s, Subtype.ext hs⟩
  have key : ∀ (s : Fin r → N.Sec) (t : N.Sec) (a : Fin r → K),
      (∀ j, t.f j = ∑ i, constFn p _ (a i) * (s i).f j) ↔ ∑ i, a i • θ (s i) = θ t := by
    intro s t a
    have e : ∀ j hj, gen _ hj (∑ i, constFn p _ (a i) * (s i).f j) =
        tr N j j₀ hj h₀ * ((∑ i, a i • θ (s i) : V) : X.functionField) := by
      intro j hj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, AddSubmonoidClass.coe_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, gen_constFn, ← halg, gen_sec (s i) j j₀ hj h₀, SetLike.val_smul, Algebra.smul_def]
      ring
    constructor
    · intro h
      apply Subtype.ext
      have := e j₀ h₀
      rw [tr_self hN, _root_.one_mul, ← h j₀] at this
      exact this.symm
    · intro h j
      refine eq_of_gen fun hj => ?_
      rw [e, h, gen_sec t j j₀ hj h₀]
  constructor
  · rintro ⟨s, hs⟩
    have hb : Function.Bijective (Fintype.linearCombination K fun i => θ (s i)) := by
      rw [Function.bijective_iff_existsUnique]
      intro f
      obtain ⟨t, rfl⟩ := hθ f
      simpa only [key, Fintype.linearCombination_apply] using hs t
    have E := LinearEquiv.ofBijective _ hb
    exact ⟨Module.Finite.equiv E, by rw [← E.finrank_eq, Module.finrank_fin_fun]⟩
  · rintro ⟨hf, hr⟩
    let b := Module.finBasisOfFinrankEq K V hr
    choose s hs using fun i => hθ (b i)
    refine ⟨s, fun t => ?_⟩
    simp only [key, hs]
    refine ⟨b.equivFun (θ t), b.sum_equivFun _, fun a ha => ?_⟩
    rw [← ha, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

def ffMap (ψ : X ⟶ Y) (hψ : ψ (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  (Y.presheaf.stalkSpecializes (x := ψ (genericPoint X)) (y := genericPoint Y)
    (hψ ▸ specializes_rfl) ≫ ψ.stalkMap (genericPoint X)).hom

theorem ffMap_gen (ψ : X ⟶ Y) (hψ) (U : Y.Opens) (h) (h') (a : Γ(Y, U)) :
    ffMap ψ hψ (gen U h a) = gen (ψ ⁻¹ᵁ U) h' ((ψ.app U).hom a) := by
  have := Y.presheaf.germ_stalkSpecializes_apply (x := ψ (genericPoint X)) h
    (hψ ▸ specializes_rfl) a
  exact (congrArg (ψ.stalkMap (genericPoint X)).hom this).trans
    (ψ.germ_stalkMap_apply U _ h' a)

omit [IsIntegral Y] in
theorem tr_linComb (N : LB Y) (ψ : X ⟶ Y) (ε : ℤ) (e : ℕ) (hε : ε = e) (J J' : PUnit → N.ι)
    (h) (h') (h'') :
    tr (LB.LinComb N (K := PUnit) (fun _ => ψ) (fun _ => ε)) J J' h h' =
      gen (ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩))) h'' ((ψ.app _).hom (N.g _ _).val) ^ e := by
  subst hε
  unfold tr LB.LinComb
  dsimp only
  rw [Fintype.prod_unique, zpow_natCast, Units.val_pow_eq_pow_val, map_pow]
  exact congrArg (· ^ e) (gen_rs _ _ _)

theorem tr_lbPow (N : LB X) (e : ℕ) (J J' : PUnit → N.ι) (h) (h') (k) (k') :
    tr (lbPow N e) J J' h h' = tr N (J ⟨⟩) (J' ⟨⟩) k k' ^ e := by
  rw [tr_linComb N (𝟙 X) e e rfl J J' h h' ⟨k, k'⟩]
  rfl

theorem tr_pull (N : LB Y) (ψ : X ⟶ Y) (hψ) (J J' : PUnit → N.ι) (h) (h') (k) (k') :
    tr (N.pull ψ) J J' h h' = ffMap ψ hψ (tr N (J ⟨⟩) (J' ⟨⟩) k k') := by
  have h'' : genericPoint X ∈ ψ ⁻¹ᵁ (N.U (J ⟨⟩) ⊓ N.U (J' ⟨⟩)) :=
    ⟨LB.wchart_le N _ J ⟨⟩ h, LB.wchart_le N _ J' ⟨⟩ h'⟩
  rw [tr_linComb N ψ 1 1 rfl J J' h h' h'', pow_one]
  exact (ffMap_gen ψ hψ _ _ _ _).symm

theorem tr_pw (N : LB X) (d : ℕ) (i j : N.ι) (h) (h') :
    tr (pw N d) i j h h' = tr N i j h h' ^ d := by
  unfold tr AbLaw.pw
  dsimp only
  rw [zpow_natCast, Units.val_pow_eq_pow_val, map_pow]

theorem mem_basicOpen_iff {U : X.Opens} (h) (a : Γ(X, U)) :
    genericPoint X ∈ X.basicOpen a ↔ gen U h a ≠ 0 :=
  (X.mem_basicOpen a _ h).trans (isUnit_iff_ne_zero (G₀ := X.functionField))

theorem eventually_mul_pow {W D : X.Opens} (hW : IsAffineOpen W) (h) (u : Γ(X, W))
    (hu : gen W h u ≠ 0) (hD : X.basicOpen u ≤ D) (hD') (a : Γ(X, D)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ b, gen W h b = gen D hD' a * gen W h u ^ n := by
  have := hW.isLocalization_basicOpen u
  have hb := (mem_basicOpen_iff h u).2 hu
  obtain ⟨⟨b, _, m, rfl⟩, hm⟩ := IsLocalization.surj (Submonoid.powers u) (rs X hD a)
  have h1 : gen D hD' a * gen W h u ^ m = gen W h b := by
    have h2 := congrArg (gen _ hb) hm
    rw [map_mul, gen_rs] at h2
    have h3 : ∀ x : Γ(X, W), gen _ hb (algebraMap Γ(X, W) Γ(X, X.basicOpen u) x) = gen W h x :=
      fun x => gen_rs (X.basicOpen_le u) hb x
    rw [h3, h3, map_pow] at h2
    exact h2
  filter_upwards [Filter.eventually_ge_atTop m] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact ⟨b * u ^ k, by rw [map_mul, map_pow, ← h1, pow_add, _root_.mul_assoc]⟩

theorem exists_frac {D : X.Opens} (hD : IsAffineOpen D) (h) (t : X.functionField) :
    ∃ a b : Γ(X, D), gen D h b ≠ 0 ∧ t * gen D h b = gen D h a := by
  haveI : Nonempty D := ⟨⟨_, h⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X D hD
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors Γ(X, D)) t
  exact ⟨a, b, fun h0 => nonZeroDivisors.ne_zero hb (gen_injective D h (h0.trans (map_zero _).symm)),
    hab⟩

end GlobalTheory.VolFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TendstoOfSandwich
namespace GlobalTheory.VolFin

open Module Filter Topology

section Alg

variable {K F F' : Type} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] {ι : Type}

def piece (R : ι → Subalgebra K F) (γ : ι → F) (e : ℕ) : Submodule K F where
  carrier := {f | ∀ i, f * γ i ^ e ∈ R i}
  add_mem' ha hb i := by rw [add_mul]; exact (R i).add_mem (ha i) (hb i)
  zero_mem' i := by rw [zero_mul]; exact (R i).zero_mem
  smul_mem' c a ha i := by rw [smul_mul_assoc]; exact (R i).smul_mem (ha i) c

theorem mem_piece {R : ι → Subalgebra K F} {γ : ι → F} {e : ℕ} {f : F} :
    f ∈ piece R γ e ↔ ∀ i, f * γ i ^ e ∈ R i := Iff.rfl

theorem mul_mem_piece {R : ι → Subalgebra K F} {γ : ι → F} {e e' : ℕ} {a b : F}
    (ha : a ∈ piece R γ e) (hb : b ∈ piece R γ e') : a * b ∈ piece R γ (e + e') := mem_piece.2 fun i => by
  have hab := (R i).mul_mem (mem_piece.1 ha i) (mem_piece.1 hb i)
  rw [pow_add]
  convert hab using 1
  ring

def Den (R : ι → Subalgebra K F) (γ : ι → F) : Prop :=
  ∀ u : F, ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ q * u ∈ piece R γ c

theorem Den.finset {R : ι → Subalgebra K F} {γ : ι → F} (h : Den R γ) (s : Finset F) :
    ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ ∀ u ∈ s, q * u ∈ piece R γ c := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, 1, mem_piece.2 fun i => by simp, one_ne_zero, by simp⟩
  | insert u s hu ih =>
    obtain ⟨c, q, hq, hq0, hs⟩ := ih
    obtain ⟨c', q', hq', hq'0, hu'⟩ := h u
    refine ⟨c + c', q * q', mul_mem_piece hq hq', mul_ne_zero hq0 hq'0, ?_⟩
    intro v hv
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [mul_assoc]
      exact mul_mem_piece hq hu'
    · rw [mul_right_comm]
      exact mul_mem_piece (hs v hv) hq'

theorem Den.family {R : ι → Subalgebra K F} {γ : ι → F} (h : Den R γ) {κ : Type} [Finite κ]
    (u : κ → F) : ∃ c, ∃ q ∈ piece R γ c, q ≠ 0 ∧ ∀ k, q * u k ∈ piece R γ c := by
  classical
  have := Fintype.ofFinite κ
  obtain ⟨c, q, hq, hq0, hs⟩ := h.finset (Finset.univ.image u)
  exact ⟨c, q, hq, hq0, fun k => hs _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))⟩

variable [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F'] [Finite ι]

theorem upper {R : ι → Subalgebra K F} {γ : ι → F} {R' : ι → Subalgebra K F'} (h : Den R γ)
    (hG : ∀ i, ∃ (n : ℕ) (g : Fin n → F'), ∀ t ∈ R' i, ∃ w : Fin n → F,
      (∀ l, w l ∈ R i) ∧ t = ∑ l, w l • g l)
    (hfin : ∀ e, Module.Finite K (piece R γ e)) :
    ∃ c, ∀ e, Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e) ∧
      finrank K (piece R' (fun i => algebraMap F F' (γ i)) e) ≤
        finrank F F' * finrank K (piece R γ (e + c)) := by
  classical
  choose n g hg using hG
  have b : Basis (Fin (finrank F F')) F F' := Module.finBasis F F'
  obtain ⟨c, q, -, hq0, hu⟩ := h.family (κ := Σ i : ι, Fin (n i) × Fin (finrank F F'))
    (fun k => b.repr (g k.1 k.2.1) k.2.2)
  refine ⟨c, fun e => ?_⟩
  have := hfin (e + c)
  have key : ∀ f ∈ piece R' (fun i => algebraMap F F' (γ i)) e, ∀ j,
      q * b.repr f j ∈ piece R γ (e + c) := by
    intro f hf j
    refine mem_piece.2 fun i => ?_
    obtain ⟨w, hw, hfw⟩ := hg i _ (mem_piece.1 hf i)
    have hfw' : (γ i ^ e) • f = ∑ l, w l • g i l := by
      rw [Algebra.smul_def, map_pow, mul_comm]
      exact hfw
    have h1 : γ i ^ e * b.repr f j = ∑ l, w l * b.repr (g i l) j := by
      have := congrArg (fun x => b.repr x j) hfw'
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, Finsupp.finsetSum_apply] using this
    have h2 : q * b.repr f j * γ i ^ (e + c) = ∑ l, w l * (q * b.repr (g i l) j * γ i ^ c) := by
      rw [pow_add, show q * b.repr f j * (γ i ^ e * γ i ^ c)
        = (γ i ^ e * b.repr f j) * (q * γ i ^ c) by ring, h1, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [h2]
    exact Subalgebra.sum_mem _ fun l _ => (R i).mul_mem (hw l) (mem_piece.1 (hu ⟨i, l, j⟩) i)
  let Φ : piece R' (fun i => algebraMap F F' (γ i)) e →ₗ[K] (Fin (finrank F F') → piece R γ (e + c)) :=
    { toFun := fun f j => ⟨q * b.repr f j, key f f.2 j⟩
      map_add' := fun f f' => by
        funext j
        apply Subtype.ext
        simp [mul_add]
      map_smul' := fun a f => by
        funext j
        apply Subtype.ext
        simp only [SetLike.val_smul, RingHom.id_apply, Pi.smul_apply]
        rw [← algebraMap_smul F a (f : F'), map_smul, Finsupp.smul_apply, smul_eq_mul,
          Algebra.smul_def]
        ring }
  have hinj : Function.Injective Φ := by
    intro f f' hff
    apply Subtype.ext
    apply b.repr.injective
    ext j
    have := congrArg (fun x => ((x j : piece R γ (e + c)) : F)) hff
    simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact mul_left_cancel₀ hq0 this
  have : Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e) :=
    Module.Finite.of_injective Φ hinj
  refine ⟨this, ?_⟩
  calc finrank K (piece R' (fun i => algebraMap F F' (γ i)) e)
      ≤ finrank K (Fin (finrank F F') → piece R γ (e + c)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = finrank F F' * finrank K (piece R γ (e + c)) := by
        simp [Module.finrank_pi_fintype]

omit [IsScalarTower K F F'] [Module.Finite F F'] in
theorem mem_span_of_frac (S : Subalgebra K F') (hS : ∀ t : F', ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ t * b = a)
    (halg : ∀ b ∈ S, IsAlgebraic F b) (t : F') : t ∈ Submodule.span F (S : Set F') := by
  obtain ⟨a, ha, b, hb, hb0, htb⟩ := hS t
  have hsub : ((Submonoid.closure (S : Set F') : Submonoid F') : Set F') ⊆
      (Submodule.span F (S : Set F') : Set F') := by
    intro x hx
    have hx' : x ∈ S.toSubmonoid :=
      (Submonoid.closure_le (S := S.toSubmonoid)).2 (fun y hy => hy) hx
    exact Submodule.subset_span hx'
  rw [← Algebra.adjoin_eq_span_of_subset F hsub, Subalgebra.mem_toSubmodule]
  have hbinv : b⁻¹ ∈ Algebra.adjoin F (S : Set F') :=
    Algebra.adjoin_mono (Set.singleton_subset_iff.2 hb) (halg b hb).isIntegral.inv_mem_adjoin
  have ht : t = a * b⁻¹ := by rw [← htb, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  rw [ht]
  exact Subalgebra.mul_mem _ (Algebra.subset_adjoin ha) hbinv

omit [IsScalarTower K F F'] [Module.Finite F F'] in
theorem finite_of_frac (S : Subalgebra K F') (hS : ∀ t : F', ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ t * b = a)
    {n : ℕ} (g : Fin n → F') (hg : ∀ t ∈ S, ∃ w : Fin n → F, t = ∑ l, w l • g l) :
    Module.Finite F F' := by
  have hle : Submodule.span F (S : Set F') ≤ Submodule.span F (Set.range g) := by
    rw [Submodule.span_le]
    intro t ht
    obtain ⟨w, rfl⟩ := hg t ht
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  have hsub : ((Submonoid.closure (S : Set F') : Submonoid F') : Set F') ⊆
      (Submodule.span F (S : Set F') : Set F') := by
    intro x hx
    have hx' : x ∈ S.toSubmonoid :=
      (Submonoid.closure_le (S := S.toSubmonoid)).2 (fun y hy => hy) hx
    exact Submodule.subset_span hx'
  have : FiniteDimensional F (Submodule.span F (Set.range g)) :=
    FiniteDimensional.span_of_finite F (Set.finite_range g)
  have : FiniteDimensional F (Submodule.span F (S : Set F')) :=
    Submodule.finiteDimensional_of_le hle
  have halg : ∀ b ∈ S, IsAlgebraic F b := by
    intro b hb
    refine (IsIntegral.of_mem_of_fg (Algebra.adjoin F (S : Set F')) ?_ b
      (Algebra.subset_adjoin hb)).isAlgebraic
    rw [Algebra.adjoin_eq_span_of_subset F hsub]
    exact Module.Finite.iff_fg.1 inferInstance
  have htop : Submodule.span F (Set.range g) = ⊤ :=
    eq_top_iff.2 fun t _ => hle (mem_span_of_frac S hS halg t)
  exact Module.finite_def.2 (Submodule.fg_def.2 ⟨_, Set.finite_range g, htop⟩)

theorem lower {R : ι → Subalgebra K F} {γ : ι → F} {R' : ι → Subalgebra K F'} (h : Den R γ)
    (hR : ∀ i, ∀ a ∈ R i, algebraMap F F' a ∈ R' i)
    (hS : ∀ i, ∀ t : F', ∃ a ∈ R' i, ∃ b ∈ R' i, b ≠ 0 ∧ t * b = a)
    (hfin : ∀ e, Module.Finite K (piece R' (fun i => algebraMap F F' (γ i)) e)) :
    ∃ c, ∀ e, Module.Finite K (piece R γ e) → finrank F F' * finrank K (piece R γ e) ≤
      finrank K (piece R' (fun i => algebraMap F F' (γ i)) (e + c)) := by
  classical
  have b : Basis (Fin (finrank F F')) F F' := Module.finBasis F F'
  have hspan : ∀ i, ∀ t : F', t ∈ Submodule.span F (R' i : Set F') := fun i t =>
    mem_span_of_frac (R' i) (hS i) (fun x _ => (IsIntegral.of_finite F x).isAlgebraic) t
  choose n f s hfs using fun p : ι × Fin (finrank F F') =>
    Submodule.mem_span_set'.1 (hspan p.1 (b p.2))
  obtain ⟨c, q, -, hq0, hu⟩ := h.family (κ := Σ p : ι × Fin (finrank F F'), Fin (n p))
    (fun k => f k.1 k.2)
  let v : Fin (finrank F F') → F' := fun j => q • b j
  have hv : ∀ j, v j ∈ piece R' (fun i => algebraMap F F' (γ i)) c := by
    intro j
    refine mem_piece.2 fun i => ?_
    have hvj : v j * algebraMap F F' (γ i) ^ c =
        ∑ l, algebraMap F F' (q * f (i, j) l * γ i ^ c) * (s (i, j) l : F') := by
      simp only [v]
      rw [show b j = _ from (hfs (i, j)).symm, Finset.smul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Algebra.smul_def, map_mul, map_pow]
      ring
    rw [hvj]
    exact Subalgebra.sum_mem _ fun l _ =>
      (R' i).mul_mem (hR i _ (mem_piece.1 (hu ⟨(i, j), l⟩) i)) (s (i, j) l).2
  refine ⟨c, fun e hP => ?_⟩
  have := hP
  have := hfin (e + c)
  have key : ∀ x : Fin (finrank F F') → piece R γ e,
      ∑ j, (x j : F) • v j ∈ piece R' (fun i => algebraMap F F' (γ i)) (e + c) := by
    intro x
    refine mem_piece.2 fun i => ?_
    rw [Finset.sum_mul]
    refine Subalgebra.sum_mem _ fun j _ => ?_
    have hxj : (x j : F) • v j * algebraMap F F' (γ i) ^ (e + c) =
        algebraMap F F' ((x j : F) * γ i ^ e) * (v j * algebraMap F F' (γ i) ^ c) := by
      rw [Algebra.smul_def, map_mul, map_pow, pow_add]
      ring
    rw [hxj]
    exact (R' i).mul_mem (hR i _ (mem_piece.1 (x j).2 i)) (mem_piece.1 (hv j) i)
  let Φ : (Fin (finrank F F') → piece R γ e) →ₗ[K]
      piece R' (fun i => algebraMap F F' (γ i)) (e + c) :=
    { toFun := fun x => ⟨∑ j, (x j : F) • v j, key x⟩
      map_add' := fun x y => by
        apply Subtype.ext
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a x => by
        apply Subtype.ext
        simp [Finset.smul_sum, smul_assoc] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∑ j, ((x j : F) * q) • b j = 0 := by
      have := congrArg Subtype.val hx
      simpa [Φ, v, smul_smul] using this
    funext j
    have hj := (Fintype.linearIndependent_iff.1 b.linearIndependent) _ h0 j
    exact Subtype.ext (by simpa using (mul_eq_zero.1 hj).resolve_right hq0)
  calc finrank F F' * finrank K (piece R γ e)
      = finrank K (Fin (finrank F F') → piece R γ e) := by
        simp [Module.finrank_pi_fintype]
    _ ≤ _ := LinearMap.finrank_le_finrank_of_injective hinj

end Alg

theorem tendsto_of_sandwich (h h' : ℕ → ℕ) (D g c c' : ℕ) (δ : ℝ)
    (hh : Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 δ))
    (lo : ∀ e, D * h e ≤ h' (e + c)) (up : ∀ e, h' e ≤ D * h (e + c')) :
    Tendsto (fun e : ℕ => (h' e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 (D * δ)) := by
  have hr : ∀ k : ℕ, Tendsto (fun e : ℕ => (((e + k : ℕ) : ℝ) / (e : ℝ)) ^ g) atTop (𝓝 1) := by
    intro k
    have h2 := ((tendsto_natCast_div_add_atTop (k : ℝ)).inv₀ one_ne_zero).pow g
    rw [inv_one, one_pow] at h2
    refine h2.congr fun e => ?_
    rw [inv_div, Nat.cast_add]
  refine (tendsto_add_atTop_iff_nat c).1 ?_
  have hL : Tendsto (fun e : ℕ => (D : ℝ) * ((h e : ℝ) / (e : ℝ) ^ g) /
      (((e + c : ℕ) : ℝ) / (e : ℝ)) ^ g) atTop (𝓝 (D * δ)) := by
    have := (hh.const_mul (D : ℝ)).div (hr c) one_ne_zero
    rwa [div_one] at this
  have hU : Tendsto (fun e : ℕ => (D : ℝ) * ((h (e + (c + c')) : ℝ) /
      ((e + (c + c') : ℕ) : ℝ) ^ g) * ((((e + c) + c' : ℕ) : ℝ) / ((e + c : ℕ) : ℝ)) ^ g)
      atTop (𝓝 (D * δ)) := by
    have := ((hh.comp (tendsto_add_atTop_nat (c + c'))).const_mul (D : ℝ)).mul
      ((hr c').comp (tendsto_add_atTop_nat c))
    rw [mul_one] at this
    exact this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hcast : ((D * h e : ℕ) : ℝ) ≤ (h' (e + c) : ℝ) := by exact_mod_cast lo e
    push_cast at hcast ⊢
    have hc0 : (0 : ℝ) < (e : ℝ) + c := by positivity
    have heq : (D : ℝ) * ((h e : ℝ) / (e : ℝ) ^ g) / (((e : ℝ) + c) ^ g / (e : ℝ) ^ g)
        = (D : ℝ) * (h e : ℝ) / ((e : ℝ) + c) ^ g := by
      field_simp
    rw [div_pow, heq]
    gcongr
  · filter_upwards [eventually_ge_atTop 1] with e he
    have he0 : (0 : ℝ) < e := by exact_mod_cast he
    have hcast : (h' (e + c) : ℝ) ≤ ((D * h (e + c + c') : ℕ) : ℝ) := by exact_mod_cast up (e + c)
    rw [show e + (c + c') = e + c + c' from (add_assoc _ _ _).symm]
    push_cast at hcast ⊢
    have hc0 : (0 : ℝ) < (e : ℝ) + c := by positivity
    have hcc0 : (0 : ℝ) < (e : ℝ) + c + c' := by positivity
    have heq : (D : ℝ) * ((h (e + c + c') : ℝ) / ((e : ℝ) + c + c') ^ g) *
        (((e : ℝ) + c + c') ^ g / ((e : ℝ) + c) ^ g)
        = (D : ℝ) * (h (e + c + c') : ℝ) / ((e : ℝ) + c) ^ g := by
      field_simp
    rw [div_pow, heq]
    gcongr

end GlobalTheory.VolFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
open GlobalTheory.AbLaw (rs pw)

noncomputable section

namespace GlobalTheory.VolFin

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

def regAlg [Algebra K X.functionField] (p : X ⟶ Sp K)
    (halg : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn p ⊤ a))
    (U : X.Opens) (h : genericPoint X ∈ U) : Subalgebra K X.functionField :=
  { (gen U h).rangeS with
    algebraMap_mem' := fun a => ⟨constFn p U a, (gen_constFn p U h a).trans (halg a).symm⟩ }

theorem mem_regAlg [Algebra K X.functionField] {p : X ⟶ Sp K} {halg} {U : X.Opens} {h}
    {f : X.functionField} : f ∈ regAlg p halg U h ↔ ∃ a, gen U h a = f := Iff.rfl

theorem sections_power_integral_iff_affine_cover [Algebra K X.functionField] (p : X ⟶ Sp K) (halg)
    {N : LB X} (hN : N.IsLB) (j₀ : N.ι) (h₀) {κ : Type} (W : κ → X.Opens)
    (c : κ → N.ι) (hW : ∀ i, W i ≤ N.U (c i)) (hη : ∀ i, genericPoint X ∈ W i)
    (hc : ∀ x, ∃ i, x ∈ W i) (y : κ → X.functionField)
    (hy : ∀ i, tr N (c i) j₀ (hW i (hη i)) h₀ = y i) (e r : ℕ) :
    SectionsHaveFiniteDimension p (lbPow N e) r ↔ Module.Finite K (piece (fun i => regAlg p halg (W i) (hη i)) y e) ∧
      Module.finrank K (piece (fun i => regAlg p halg (W i) (hη i)) y e) = r := by
  refine lineBundle_global_sections_functionField_iff p halg (N := lbPow N e) (LB.isLB_linComb hN _ _) (fun _ => j₀)
    (Set.mem_iInter.2 fun _ => h₀) W (fun i _ => c i)
    (fun i _ hx => Set.mem_iInter.2 fun _ => hW i hx) hη hc _ (fun f => ?_) r
  refine forall_congr' fun i => ?_
  refine mem_regAlg.trans (exists_congr fun a => Eq.congr_right (congrArg (f * ·) ?_))
  exact ((tr_lbPow N e (fun _ => c i) (fun _ => j₀) _ _ (hW i (hη i)) h₀).trans
    (congrArg (· ^ e) (hy i))).symm

def constFF (p : X ⟶ Sp K) : K →+* X.functionField :=
  (gen ⊤ trivial).comp ((p.appLE ⊤ ⊤ (fun _ _ => trivial)).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)

theorem den_of_section [Algebra K Y.functionField] (p : Y ⟶ Sp K) (halg) (M : LB Y) (j₀ : M.ι) (h₀)
    {κ : Type} [Finite κ] (W : κ → Y.Opens) (c : κ → M.ι) (hW : ∀ i, W i ≤ M.U (c i))
    (hη : ∀ i, genericPoint Y ∈ W i) (haff : ∀ i, IsAffineOpen (W i)) (d : ℕ) (s : (pw M d).Sec)
    (hs : IsAffineOpen (Out.nonzeroLocus s)) (hs' : genericPoint Y ∈ Out.nonzeroLocus s) :
    Den (fun i => regAlg p halg (W i) (hη i)) (fun i => tr M (c i) j₀ (hW i (hη i)) h₀) := by
  let σ := gen _ h₀ (s.f j₀)
  have hσ : σ ≠ 0 := by
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hs'
    have hk' : genericPoint Y ∈ M.U k := Y.basicOpen_le _ hk
    have h1 := (mem_basicOpen_iff hk' (s.f k)).1 hk
    exact right_ne_zero_of_mul ((gen_sec s k j₀ hk' h₀).symm.trans_ne h1)
  let u : ∀ i, Γ(Y, W i) := fun i => rs Y (hW i) (s.f (c i))
  have hu : ∀ i, gen _ (hη i) (u i) = tr M (c i) j₀ (hW i (hη i)) h₀ ^ d * σ := fun i =>
    (gen_rs _ _ _).trans ((gen_sec s (c i) j₀ (hW i (hη i)) h₀).trans
      (congrArg (· * σ) (tr_pw M d _ _ _ _)))
  have hu0 : ∀ i, gen _ (hη i) (u i) ≠ 0 := fun i => by
    rw [hu]
    exact mul_ne_zero (pow_ne_zero _ (tr_ne_zero _ _ _ _ _)) hσ
  have hD : ∀ i, Y.basicOpen (u i) ≤ Out.nonzeroLocus s := fun i =>
    (Y.basicOpen_res (s.f (c i)) (homOfLE (hW i)).op).le.trans
      (inf_le_right.trans (le_iSup (fun k => Y.basicOpen (s.f k)) (c i)))
  have ev : ∀ a : Γ(Y, Out.nonzeroLocus s), ∀ᶠ n : ℕ in Filter.atTop, gen _ hs' a * σ ^ n ∈
      piece (fun i => regAlg p halg (W i) (hη i)) (fun i => tr M (c i) j₀ (hW i (hη i)) h₀)
        (d * n) := by
    intro a
    simp only [mem_piece]
    refine Filter.eventually_all.2 fun i => ?_
    filter_upwards [eventually_mul_pow (haff i) (hη i) (u i) (hu0 i) (hD i) hs' a] with n hn
    obtain ⟨b, hb⟩ := hn
    refine ⟨b, hb.trans ?_⟩
    rw [hu]
    ring
  intro t
  obtain ⟨a, b, hb, hab⟩ := exists_frac hs hs' t
  obtain ⟨n, hna, hnb⟩ := ((ev a).and (ev b)).exists
  refine ⟨d * n, _, hnb, mul_ne_zero hb (pow_ne_zero _ hσ), ?_⟩
  rw [← hab] at hna
  convert hna using 1
  ring

omit [IsIntegral Y] in
theorem exists_affine_cover [CompactSpace Y] {M : LB Y} (hM : M.IsLB) :
    ∃ (κ : Type) (_ : Finite κ) (W : κ → Y.Opens) (c : κ → M.ι), (∀ i, W i ≤ M.U (c i)) ∧
      (∀ i, ∃ x, x ∈ W i) ∧ (∀ i, IsAffineOpen (W i)) ∧ ∀ x, ∃ i, x ∈ W i := by
  have h : ∀ y : Y, ∃ (j : M.ι) (W : Y.Opens), IsAffineOpen W ∧ y ∈ W ∧ W ≤ M.U j := by
    intro y
    have hy : y ∈ ⨆ i, M.U i := hM.cover ▸ trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨W, hW, h1, h2⟩ := exists_isAffineOpen_mem_and_subset hj
    exact ⟨j, W, hW, h1, h2⟩
  choose c W h1 h2 h3 using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set Y))
    (fun y => (W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, h2 y⟩)
  refine ⟨t, inferInstance, fun y => W y, fun y => c y, fun y => h3 y, fun y => ⟨y, h2 y⟩,
    fun y => h1 y, fun x => ?_⟩
  obtain ⟨y, hy, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact ⟨⟨y, hy⟩, hx⟩

theorem vol_pull [CompactSpace Y] (p : Y ⟶ Sp K) (ψ : X ⟶ Y) [IsFinite ψ]
    (hψ : ψ (genericPoint X) = genericPoint Y) {D : ℕ} (hD : MapDeg ψ D) {M : LB Y} (hM : M.IsLB)
    (d : ℕ) (s : (pw M d).Sec) (hs : IsAffineOpen (Out.nonzeroLocus s))
    (hs' : genericPoint Y ∈ Out.nonzeroLocus s) {g : ℕ} {δ : ℝ} (hv : Vol p M g δ) :
    Vol (ψ ≫ p) (M.pull ψ) g (D * δ) := by
  obtain ⟨κ, _, W, c, hW, hne, haff, hc⟩ := exists_affine_cover hM
  have hη : ∀ i, genericPoint Y ∈ W i := fun i => generic_mem (hne i).choose_spec
  have hη' : ∀ i, genericPoint X ∈ ψ ⁻¹ᵁ W i := fun i => show ψ _ ∈ W i from hψ ▸ hη i
  obtain ⟨i₀, -⟩ := hc (genericPoint Y)
  letI : Algebra K Y.functionField := (constFF p).toAlgebra
  letI : Algebra K X.functionField := (constFF (ψ ≫ p)).toAlgebra
  letI : Algebra Y.functionField X.functionField := (ffMap ψ hψ).toAlgebra
  have halg : ∀ a, algebraMap K Y.functionField a = gen ⊤ trivial (constFn p ⊤ a) := fun _ => rfl
  have halg' : ∀ a, algebraMap K X.functionField a = gen ⊤ trivial (constFn (ψ ≫ p) ⊤ a) :=
    fun _ => rfl
  have hφ : ∀ a, algebraMap Y.functionField X.functionField a = ffMap ψ hψ a := fun _ => rfl
  haveI : IsScalarTower K Y.functionField X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [hφ, halg, halg', ffMap_gen ψ hψ ⊤ trivial trivial]
    congr 1
    unfold constFn
    rw [Scheme.Hom.app_eq_appLE]
    exact (congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
      (Scheme.Hom.appLE_comp_appLE ψ p ⊤ ⊤ ⊤ (fun _ _ => trivial) (fun _ _ => trivial))).symm
  let R := fun i => regAlg p halg (W i) (hη i)
  let R' := fun i => regAlg (ψ ≫ p) halg' (ψ ⁻¹ᵁ W i) (hη' i)
  let y := fun i => tr M (c i) (c i₀) (hW i (hη i)) (hW i₀ (hη i₀))
  have hden : Den R y := den_of_section p halg M (c i₀) _ W c hW hη haff d s hs hs'
  have H : ∀ e r, SectionsHaveFiniteDimension p (lbPow M e) r ↔
      Module.Finite K (piece R y e) ∧ Module.finrank K (piece R y e) = r :=
    sections_power_integral_iff_affine_cover p halg hM (c i₀) (hW i₀ (hη i₀)) W c hW hη hc y fun _ => rfl
  have hW' : ∀ i, ψ ⁻¹ᵁ W i ≤ (M.pull ψ).U (fun _ => c i) := fun i =>
    le_trans (fun _ hx => hW i hx) (AbLaw.le_pull M ψ (le_refl (M.U (c i))))
  have H' : ∀ e r, SectionsHaveFiniteDimension (ψ ≫ p) (lbPow (M.pull ψ) e) r ↔
      Module.Finite K (piece R' (fun i => algebraMap _ X.functionField (y i)) e) ∧
        Module.finrank K (piece R' (fun i => algebraMap _ X.functionField (y i)) e) = r :=
    sections_power_integral_iff_affine_cover (ψ ≫ p) halg' (N := M.pull ψ) (LB.isLB_linComb hM _ _) (fun _ => c i₀)
      (hW' i₀ (hη' i₀)) (fun i => ψ ⁻¹ᵁ W i) (fun i _ => c i) hW' hη' (fun x => hc (ψ x)) _
      fun i => tr_pull M ψ hψ _ _ _ _ (hW i (hη i)) (hW i₀ (hη i₀))
  have hR : ∀ i, ∀ a ∈ R i, algebraMap _ X.functionField a ∈ R' i := by
    rintro i _ ⟨a, rfl⟩
    exact ⟨_, (ffMap_gen ψ hψ _ _ _ a).symm⟩
  have hS : ∀ i, ∀ t : X.functionField, ∃ a ∈ R' i, ∃ b ∈ R' i, b ≠ 0 ∧ t * b = a := by
    intro i t
    obtain ⟨a, b, hb, hab⟩ := exists_frac ((haff i).preimage ψ) (hη' i) t
    exact ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hb, hab⟩
  have hG : ∀ i, ∃ (n : ℕ) (v : Fin n → X.functionField), ∀ t ∈ R' i,
      ∃ w : Fin n → Y.functionField, (∀ l, w l ∈ R i) ∧ t = ∑ l, w l • v l := by
    intro i
    letI := (ψ.app (W i)).hom.toAlgebra
    haveI : Module.Finite Γ(Y, W i) Γ(X, ψ ⁻¹ᵁ W i) := IsFinite.finite_app ψ (W i) (haff i)
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := Γ(Y, W i)) (M := Γ(X, ψ ⁻¹ᵁ W i))
    refine ⟨n, fun l => gen _ (hη' i) (v l), ?_⟩
    rintro _ ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
      (hv ▸ Submodule.mem_top : t ∈ Submodule.span Γ(Y, W i) (Set.range v))
    refine ⟨fun l => gen _ (hη i) (w l), fun l => ⟨_, rfl⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hφ, ffMap_gen ψ hψ _ _ (hη' i)]
    rfl
  haveI : Module.Finite Y.functionField X.functionField := by
    obtain ⟨n, v, hv⟩ := hG i₀
    exact finite_of_frac (R' i₀) (hS i₀) v fun t ht => (hv t ht).imp fun _ h => h.2
  have hrank : Module.finrank Y.functionField X.functionField = D := by
    haveI : Nonempty (W i₀) := ⟨⟨_, hη i₀⟩⟩
    haveI : Nonempty (ψ ⁻¹ᵁ W i₀) := ⟨⟨_, hη' i₀⟩⟩
    haveI := functionField_isFractionRing_of_isAffineOpen Y _ (haff i₀)
    haveI := functionField_isFractionRing_of_isAffineOpen X _ ((haff i₀).preimage ψ)
    letI := (ψ.app (W i₀)).hom.toAlgebra
    letI : Algebra Γ(Y, W i₀) X.functionField :=
      ((gen _ (hη' i₀)).comp (ψ.app (W i₀)).hom).toAlgebra
    haveI : IsScalarTower Γ(Y, W i₀) Γ(X, ψ ⁻¹ᵁ W i₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower Γ(Y, W i₀) Y.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => (ffMap_gen ψ hψ _ (hη i₀) (hη' i₀) a).symm
    rw [IsFractionRing.finrank_eq Γ(Y, W i₀) Y.functionField Γ(X, ψ ⁻¹ᵁ W i₀) X.functionField]
    exact Module.finrank_eq_of_rank_eq (hD _ (haff i₀) ⟨_, hη i₀⟩)
  obtain ⟨h, hh, hlim⟩ := hv
  have hfin := fun e => ((H e _).1 (hh e)).1
  have hrk := fun e => ((H e _).1 (hh e)).2
  obtain ⟨c₁, hup⟩ := upper (R' := R') hden hG hfin
  obtain ⟨c₂, hlo⟩ := lower hden hR hS fun e => (hup e).1
  refine ⟨_, fun e => (H' e _).2 ⟨(hup e).1, rfl⟩,
    tendsto_of_sandwich h _ D g c₂ c₁ δ hlim (fun e => ?_) fun e => ?_⟩
  · rw [← hrk, ← hrank]
    exact hlo e (hfin e)
  · rw [← hrk, ← hrank]
    exact (hup e).2

end GlobalTheory.VolFin

namespace GlobalTheory

theorem vol_pull_of_isFinite : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A) (D : ℕ) (M : LB P.A.left) (δ : ℝ), IsMonHom α → IsFinite α.left → MapDeg α.left D → M.IsLB → Out.RelAmple P.A M → Vol P.A.hom M P.g δ → Vol P.A.hom (M.pull α.left) P.g (D * δ) := by
  intro K _ _ P α D M δ hα hfin hD hM hamp hv
  haveI := polAV_isIntegral_of_isAlgClosed K P
  haveI := P.isAb.proper
  haveI : CompactSpace P.A.left := QuasiCompact.compactSpace_of_compactSpace P.A.hom
  have hsurj := (flat_and_surjective_of_isFinite_grpEnd K P.A α).2
  have hψ : α.left (genericPoint P.A.left) = genericPoint P.A.left := by
    have := (genericPoint_spec P.A.left).image α.left.continuous
    rw [Set.image_univ, α.left.surjective.range_eq, closure_univ] at this
    exact this.eq (genericPoint_spec _)
  obtain ⟨d, -, n, s, hcov, hs⟩ := (Unif.relAmple_iff_veryAmpleBy K P.A M hM).1 hamp
  have hx : genericPoint P.A.left ∈ ⨆ i, Out.nonzeroLocus (s i) := hcov ▸ trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have := VolFin.vol_pull P.A.hom α.left hψ hD hM d (s i) (hs i).1 hi hv
  rwa [Over.w α] at this

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsPowerGrowthVolumePullFiniteEndomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsPowerGrowthVolume_pull_finite_endomorphism : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (α : P.A ⟶ P.A) (D : ℕ) (M : LB P.A.left) (δ : ℝ), IsMonHom α → IsFinite α.left → MapDeg α.left D → M.IsLB → Out.RelAmple P.A M → Vol P.A.hom M P.g δ → Vol P.A.hom (M.pull α.left) P.g (D * δ) := by
  first | exact @GlobalTheory.vol_pull_of_isFinite | exact GlobalTheory.vol_pull_of_isFinite | (intros; apply GlobalTheory.vol_pull_of_isFinite <;> assumption)
end
