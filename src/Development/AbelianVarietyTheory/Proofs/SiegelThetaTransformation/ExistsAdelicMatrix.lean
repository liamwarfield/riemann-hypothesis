module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsIsometryModPrimePow
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory
open IsDedekindDomain GlobalTheory.SelfDualGenus
open scoped Matrix nonZeroDivisors

noncomputable section

namespace GlobalTheory.IsomModN

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_approx_int {K : Type} [Field K] [NumberField K] {n : ℕ} (hn : 0 < n)
    (c : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) :
    ∃ s : 𝓞 K, ∀ v : HeightOneSpectrum (𝓞 K), ∃ a : v.adicCompletionIntegers K,
      c v = algebraMap (𝓞 K) _ s + n • a := by
  let y : FiniteAdeleRing (𝓞 K) K :=
    ⟨fun v => (c v : v.adicCompletion K), Filter.Eventually.of_forall fun v => (c v).2⟩
  obtain ⟨s, a, ha, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat K n hn).2 y fun v => (c v).2
  refine ⟨s, fun v => ⟨⟨a v, ha v⟩, Subtype.ext ?_⟩⟩
  exact congrArg (fun t : FiniteAdeleRing (𝓞 K) K => t v) h

def vec (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) : (Fin r → E) →+ (Fin r → LocAlg v) where
  toFun x := fun i => locEmb v (x i)
  map_zero' := funext fun _ => map_zero _
  map_add' _ _ := funext fun _ => map_add _ _ _

theorem vec_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) {L : Submodule (𝓞 E) (Fin r → E)} {x : Fin r → E} (hx : x ∈ L) :
    vec v x ∈ locLattice v L := Submodule.subset_span ⟨x, hx, rfl⟩

theorem vec_smul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (c : 𝓞 E) (x : Fin r → E) :
    vec v (c • x) = locEmb v c • vec v x := funext fun _ => map_mul (locEmb v) _ _

theorem vec_smul_real (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (s : 𝓞 (maximalRealSubfield E)) (x : Fin r → E) :
    vec v (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s • x) = algebraMap (𝓞 (maximalRealSubfield E)) (v.adicCompletionIntegers (maximalRealSubfield E)) s • vec v x := by
  rw [vec_smul, locEmb_algebraMap, algebraMap_smul]

theorem exists_approx {L : Submodule (𝓞 E) (Fin r → E)} (hL : L.FG) {n : ℕ} (hn : 0 < n)
    (z : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Fin r → LocAlg v) (hz : ∀ v, z v ∈ locLattice v L) :
    ∃ b ∈ L, ∀ v, ∃ u ∈ locLattice v L, z v = vec v b + n • u := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  obtain ⟨m, t, ht⟩ := Module.Finite.exists_fin (R := ℤ) (M := L)
  have h1 : ∀ v, z v ∈ Submodule.span (v.adicCompletionIntegers (maximalRealSubfield E)) (Set.range fun i : Fin m => vec (E := E) (r := r) v (t i : Fin r → E)) := by
    intro v
    refine (Submodule.span_le.2 ?_ : locLattice v L ≤ _) (hz v)
    rintro _ ⟨x, hx, rfl⟩
    have hx' : (⟨x, hx⟩ : L) ∈ Submodule.span ℤ (Set.range t) := ht ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hx'
    have e : x = ∑ i, c i • (t i : Fin r → E) := by
      have := congrArg Subtype.val hc
      simpa using this.symm
    change vec v x ∈ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  choose c hc using fun v => (Submodule.mem_span_range_iff_exists_fun _).1 (h1 v)
  choose s hs using fun i => exists_approx_int hn (fun v => c v i)
  refine ⟨∑ i, algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) (s i) • (t i : Fin r → E),
    L.sum_mem fun i _ => L.smul_mem _ (t i).2, fun v => ?_⟩
  choose a ha using fun i => hs i v
  refine ⟨∑ i, a i • vec v (t i : Fin r → E),
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (vec_mem v (t i).2), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hc v, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ha i, vec_smul_real, add_smul, smul_assoc]

theorem exists_div {L : Submodule (𝓞 E) (Fin r → E)} (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) {n : ℕ} (hn : 0 < n)
    {x : Fin r → E} (hx : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ u ∈ locLattice v L, vec v x = n • u) :
    ∃ y ∈ L, x = n • y := by
  have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  refine ⟨(n : E)⁻¹ • x, (mem_iff_forall_mem_locLattice hL _).2 fun v => ?_, ?_⟩
  · obtain ⟨u, hu, e⟩ := hx v
    convert hu using 1
    funext i
    have := congrFun e i
    change locEmb v (x i) = n • u i at this
    change locEmb v ((n : E)⁻¹ * x i) = u i
    rw [map_mul, this, nsmul_eq_mul, ← mul_assoc, ← map_natCast (locEmb v), ← map_mul,
      inv_mul_cancel₀ hn', map_one, one_mul]
  · rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hn', one_smul]

def rel (L L' : Submodule (𝓞 E) (Fin r → E)) (γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Matrix (Fin r) (Fin r) (LocAlg v))
    (n : ℕ) : Submodule (𝓞 E) (L × L') where
  carrier := {p | ∀ v, ∃ u ∈ locLattice v L',
    γ v *ᵥ vec v (p.1 : Fin r → E) = vec v (p.2 : Fin r → E) + n • u}
  zero_mem' := fun v => ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    intro p q hp hq v
    obtain ⟨w, hw, hp⟩ := hp v
    obtain ⟨w', hw', hq⟩ := hq v
    refine ⟨w + w', add_mem hw hw', ?_⟩
    simp only [Prod.snd_add, Prod.fst_add, Submodule.coe_add, map_add (f := _), Matrix.mulVec_add, hp, hq, smul_add]
    abel
  smul_mem' := by
    intro c p hp v
    obtain ⟨w, hw, hp⟩ := hp v
    refine ⟨_, smul_mem_locLattice v (locEmb_mem_locOrder v c) hw, ?_⟩
    simp only [Prod.smul_snd, Prod.smul_fst, Submodule.coe_smul, vec_smul, Matrix.mulVec_smul, hp, smul_add]
    rw [smul_comm]

theorem exists_linear_approx {L L' : Submodule (𝓞 E) (Fin r → E)} (hL : L.FG) (hL' : L'.FG) {n : ℕ}
    (hn : 0 < n) (γ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Matrix (Fin r) (Fin r) (LocAlg v))
    (hγ : ∀ v, ∀ x ∈ locLattice v L, γ v *ᵥ x ∈ locLattice v L') :
    ∃ f : L →ₗ[𝓞 E] L', ∀ a : L, ∀ v, ∃ u ∈ locLattice v L',
      γ v *ᵥ vec v (a : Fin r → E) = vec v (f a : Fin r → E) + n • u := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  have hsurj : Function.Surjective ((LinearMap.fst (𝓞 E) L L').comp (rel L L' γ n).subtype) := by
    intro a
    obtain ⟨b, hb, h⟩ := exists_approx hL' hn (fun v => γ v *ᵥ vec v (a : Fin r → E))
      fun v => hγ v _ (vec_mem v a.2)
    exact ⟨⟨(a, ⟨b, hb⟩), h⟩, rfl⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property _ LinearMap.id hsurj
  refine ⟨(LinearMap.snd (𝓞 E) L L').comp ((rel L L' γ n).subtype.comp s), fun a v => ?_⟩
  obtain ⟨w, hw, e⟩ := (s a).2 v
  have ha : (s a).1.1 = a := LinearMap.congr_fun hs a
  rw [ha] at e
  exact ⟨w, hw, e⟩

def hermLoc (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → LocAlg v) : LocAlg v :=
  x ᵥ* G.map (locEmb v) ⬝ᵥ fun i => locConj v (y i)

section Herm

variable (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (G : Matrix (Fin r) (Fin r) E)

theorem hermLoc_vec (x y : Fin r → E) : hermLoc v G (vec v x) (vec v y) = locEmb v (herm G x y) := by
  have hdot : herm G x y = x ᵥ* G ⬝ᵥ fun i => cc (y i) := by
    simp only [herm, Matrix.vecMul, dotProduct, Finset.sum_mul]
    exact Finset.sum_comm
  rw [hdot, RingHom.map_dotProduct, hermLoc]
  congr 1
  funext i
  exact (RingHom.map_vecMul (locEmb v) G x i).symm

theorem hermLoc_add_left (x x' y : Fin r → LocAlg v) :
    hermLoc v G (x + x') y = hermLoc v G x y + hermLoc v G x' y := by
  simp only [hermLoc, Matrix.add_vecMul, add_dotProduct]

theorem hermLoc_add_right (x y y' : Fin r → LocAlg v) :
    hermLoc v G x (y + y') = hermLoc v G x y + hermLoc v G x y' := by
  simp only [hermLoc, dotProduct, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hermLoc_smul_left (c : v.adicCompletionIntegers (maximalRealSubfield E)) (x y : Fin r → LocAlg v) :
    hermLoc v G (c • x) y = c • hermLoc v G x y := by
  simp only [hermLoc, Matrix.smul_vecMul, smul_dotProduct]

theorem hermLoc_smul_right (c : v.adicCompletionIntegers (maximalRealSubfield E)) (x y : Fin r → LocAlg v) :
    hermLoc v G x (c • y) = c • hermLoc v G x y := by
  simp only [hermLoc, dotProduct, Pi.smul_apply, Algebra.smul_def, map_mul, locConj_algebraMap',
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem hermLoc_nsmul_left (n : ℕ) (x y : Fin r → LocAlg v) :
    hermLoc v G (n • x) y = n • hermLoc v G x y := by
  rw [← Nat.cast_smul_eq_nsmul (v.adicCompletionIntegers (maximalRealSubfield E)), hermLoc_smul_left, Nat.cast_smul_eq_nsmul]

theorem hermLoc_nsmul_right (n : ℕ) (x y : Fin r → LocAlg v) :
    hermLoc v G x (n • y) = n • hermLoc v G x y := by
  rw [← Nat.cast_smul_eq_nsmul (v.adicCompletionIntegers (maximalRealSubfield E)), hermLoc_smul_right, Nat.cast_smul_eq_nsmul]

theorem hermLoc_mulVec {G' : Matrix (Fin r) (Fin r) E} {γ : Matrix (Fin r) (Fin r) (LocAlg v)}
    (h : G'.map (locEmb v) = γᵀ * G.map (locEmb v) * γ.map (locConj v)) (x y : Fin r → LocAlg v) :
    hermLoc v G (γ *ᵥ x) (γ *ᵥ y) = hermLoc v G' x y := by
  have : (fun i => locConj v ((γ *ᵥ y) i)) = γ.map (locConj v) *ᵥ fun i => locConj v (y i) :=
    funext fun i => RingHom.map_mulVec (locConj v) γ y i
  rw [hermLoc, hermLoc, this, h, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem hermLoc_mem {L : Submodule (𝓞 E) (Fin r → E)} {M : Submodule (𝓞 E) (Fin 1 → E)}
    (h : ∀ x ∈ L, ∀ y ∈ L, (fun _ => herm G x y) ∈ M) {x y : Fin r → LocAlg v}
    (hx : x ∈ locLattice v L) (hy : y ∈ locLattice v L) :
    (fun _ => hermLoc v G x y) ∈ locLattice v M := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨y, hy, rfl⟩ := hy
      convert vec_mem v (h x hx y hy) using 2
      exact hermLoc_vec v G x y
    | zero =>
      convert zero_mem (locLattice v M) using 2
      simp [hermLoc]
    | add y z _ _ hy hz =>
      convert add_mem hy hz using 2
      exact hermLoc_add_right v G _ y z
    | smul c y _ hy =>
      convert Submodule.smul_mem _ c hy using 2
      exact hermLoc_smul_right v G c _ y
  | zero =>
    convert zero_mem (locLattice v M) using 2
    simp [hermLoc]
  | add x z _ _ hx hz =>
    convert add_mem hx hz using 2
    exact hermLoc_add_left v G x z y
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 2
    exact hermLoc_smul_left v G c x y

end Herm

theorem exists_isometry_mod {G G' : Matrix (Fin r) (Fin r) E} {L L' : Submodule (𝓞 E) (Fin r → E)}
    (hL : ReciprocityTheory.MultiplicativeHeights.IsLattice L) (hL' : ReciprocityTheory.MultiplicativeHeights.IsLattice L') {M : Submodule (𝓞 E) (Fin 1 → E)}
    (hM : ReciprocityTheory.MultiplicativeHeights.IsLattice M) (h : ∀ x ∈ L', ∀ y ∈ L', (fun _ => herm G' x y) ∈ M)
    (hγ : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ γ, IsLocalIsometry v G' L' G L γ) {n : ℕ} (hn : 0 < n) :
    ∃ f : L →ₗ[𝓞 E] L', ((∀ a, (∃ e, f a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f a + n • e) ∧
      ∀ a a' : L, ∃ m ∈ M, herm G' (f a) (f a') - herm G a a' = n • m 0 := by
  choose γ hγ using hγ
  obtain ⟨f, hf⟩ := exists_linear_approx hL.1 hL'.1 hn (fun v => (γ v).1) fun v x hx => ((hγ v).2 x).1 hx
  have hinv : ∀ v (x : Fin r → LocAlg v), (γ v).1 *ᵥ (((γ v)⁻¹).1 *ᵥ x) = x := fun v x => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hinv' : ∀ v (x : Fin r → LocAlg v), ((γ v)⁻¹).1 *ᵥ ((γ v).1 *ᵥ x) = x := fun v x => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hback : ∀ v, ∀ x ∈ locLattice v L', ((γ v)⁻¹).1 *ᵥ x ∈ locLattice v L := fun v x hx =>
    ((hγ v).2 _).2 (by rwa [hinv])
  refine ⟨f, ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩, fun a a' => ?_⟩
  · rintro ⟨e, he⟩
    obtain ⟨y, hy, e⟩ := exists_div hL hn (x := a) fun v => by
      obtain ⟨u, hu, eu⟩ := hf a v
      refine ⟨_, hback v _ (add_mem (vec_mem v e.2) hu), ?_⟩
      rw [← Matrix.mulVec_smul, ← hinv' v (vec v a), eu, he, Submodule.coe_smul_of_tower, map_nsmul, smul_add]
    exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  · rintro ⟨e, rfl⟩
    exact ⟨f e, map_nsmul _ _ _⟩
  · obtain ⟨b, hb, h1⟩ := exists_approx hL.1 hn (fun v => ((γ v)⁻¹).1 *ᵥ vec v (a' : Fin r → E))
      fun v => hback v _ (vec_mem v a'.2)
    obtain ⟨y, hy, e⟩ := exists_div hL' hn (x := a' - f ⟨b, hb⟩) fun v => by
      obtain ⟨u, hu, eu⟩ := hf ⟨b, hb⟩ v
      obtain ⟨w, hw, ew⟩ := h1 v
      refine ⟨_, add_mem hu (((hγ v).2 _).1 hw), ?_⟩
      rw [map_sub, ← hinv v (vec v a'), ew, Matrix.mulVec_add, eu, Matrix.mulVec_smul, smul_add]
      abel
    exact ⟨⟨b, hb⟩, ⟨y, hy⟩, Subtype.ext (sub_eq_iff_eq_add'.1 e)⟩
  · obtain ⟨m, hm, e⟩ := exists_div hM hn (x := fun _ => herm G' (f a) (f a') - herm G a a') fun v => by
      obtain ⟨u, hu, eu⟩ := hf a v
      obtain ⟨u', hu', eu'⟩ := hf a' v
      have hγa := ((hγ v).2 _).1 (vec_mem v a'.2)
      refine ⟨_, neg_mem (add_mem (hermLoc_mem v G' h (vec_mem v (f a).2) hu')
        (hermLoc_mem v G' h hu hγa)), funext fun i => ?_⟩
      change locEmb v (herm G' (f a) (f a') - herm G a a') = n • -(hermLoc v G' (vec v (f a)) u' +
        hermLoc v G' u ((γ v).1 *ᵥ vec v a'))
      rw [map_sub, ← hermLoc_vec, ← hermLoc_vec, ← hermLoc_mulVec v G' (hγ v).1, eu, hermLoc_add_left,
        hermLoc_nsmul_left]
      conv_lhs => rw [eu', hermLoc_add_right, hermLoc_nsmul_right, ← eu']
      rw [smul_neg, smul_add]
      abel
    exact ⟨m, hm, congrFun e 0⟩


omit [IsCMField E] in
theorem isLattice_ideal {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (Submodule.pi Set.univ fun _ : Fin 1 => (I : Submodule (𝓞 E) E)) := by
  refine ⟨Submodule.fg_pi fun _ => FractionalIdeal.fg_of_isNoetherianRing le_rfl I, ?_⟩
  obtain ⟨m, hm, hm0⟩ : ∃ m ∈ I, m ≠ 0 := by
    by_contra h
    push Not at h
    exact hI (FractionalIdeal.eq_zero_iff.2 h)
  refine eq_top_iff.2 fun z _ => ?_
  have : z = (z 0 / m) • fun _ : Fin 1 => m := by
    funext i
    rw [Subsingleton.elim i 0]
    simp [hm0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span fun _ _ => hm)

end GlobalTheory.IsomModN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsEventuallyCongr
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory

namespace GlobalTheory.IsoTower

theorem finite_quot_nsmul (M : Type) [AddCommGroup M] [Module.Finite ℤ M] {n : ℕ} (hn : 0 < n) :
    Finite (M ⧸ (nsmulAddMonoidHom n : M →+ M).range) := by
  have : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn, ?_⟩
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  exact ⟨y, rfl⟩

theorem exists_eventually_congr {L M : Type} [AddCommGroup L] [AddCommGroup M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (U : Ultrafilter ℕ) (g : ℕ → L →+ M) {n : ℕ} (hn : 0 < n)
    (P : ℕ → Prop) (hP : ∀ᶠ j in U, P j) :
    ∃ i, P i ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e := by
  obtain ⟨S, hS, hSf⟩ := AddGroup.fg_iff.1 (Module.Finite.iff_addGroup_fg.1 (inferInstance : Module.Finite ℤ L))
  have := hSf.to_subtype
  have := finite_quot_nsmul M hn
  let φ : ℕ → S → M ⧸ (nsmulAddMonoidHom n : M →+ M).range := fun j s => QuotientAddGroup.mk (g j s)
  obtain ⟨v, hv⟩ := Ultrafilter.eq_pure_of_finite (U.map φ)
  have hv' : ∀ᶠ j in U, φ j = v := by
    have : {v} ∈ U.map φ := by
      rw [hv]
      exact rfl
    exact this
  obtain ⟨i, hi, hPi⟩ := (hv'.and hP).exists
  refine ⟨i, hPi, hv'.mono fun j hj a => ?_⟩
  have h := AddMonoidHom.eq_of_eqOn_dense hS
    (f := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g i))
    (g := (QuotientAddGroup.mk' (nsmulAddMonoidHom n : M →+ M).range).comp (g j))
    (fun s hs => congrFun (hi.trans hj.symm) ⟨s, hs⟩)
  obtain ⟨e, he⟩ := QuotientAddGroup.eq.1 (DFunLike.congr_fun h a)
  refine ⟨e, ?_⟩
  have he' : n • e = -g i a + g j a := he
  rw [he']
  abel

end GlobalTheory.IsoTower
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Real Classical nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.OntoLat

theorem exists_tower {R L M : Type} [CommRing R] [AddCommGroup L] [AddCommGroup M] [Module R L] [Module R M]
    [Module.Finite ℤ L] [Module.Finite ℤ M] (hc : ∀ r : ℕ, 0 < r → ∀ a c : L, r • a = r • c → a = c)
    (Q : ℕ → (L →ₗ[R] M) → Prop) (hQ : ∀ n m f, Q (n * m) f → Q n f)
    (hex : ∀ n : ℕ, 0 < n → ∃ f : L →ₗ[R] M,
      ((∀ a, (∃ e, f a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f a + n • e) ∧ Q n f) :
    ∃ f : ℕ → L →ₗ[R] M, (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
      (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) ∧
      ∀ n : ℕ, 0 < n → Q n (f n) := by
  choose g hg using fun j : ℕ => hex _ j.factorial_pos
  let U : Ultrafilter ℕ := Ultrafilter.of Filter.atTop
  have hU : ∀ n, 0 < n → ∀ᶠ j : ℕ in U, n ∣ j.factorial := fun n hn =>
    Ultrafilter.of_le _ ((Filter.eventually_ge_atTop n).mono fun j hj => Nat.dvd_factorial hn hj)
  have hs : ∀ n : ℕ, ∃ i : ℕ, 0 < n →
      (n ∣ i.factorial ∧ ∀ᶠ j in U, ∀ a, ∃ e, g j a = g i a + n • e) := fun n => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
    · obtain ⟨i, hi⟩ := IsoTower.exists_eventually_congr U (fun j => (g j).toAddMonoidHom) hn _ (hU n hn)
      exact ⟨i, fun _ => hi⟩
  choose s hs using hs
  refine ⟨fun n => g (s n), fun n m hn hm a => ?_, fun n hn => ?_, fun n hn => ?_⟩
  · obtain ⟨j, h1, h2⟩ := ((hs _ (Nat.mul_pos hn hm)).2.and (hs n hn).2).exists
    obtain ⟨e1, h1⟩ := h1 a
    obtain ⟨e2, h2⟩ := h2 a
    refine ⟨e2 - m • e1, ?_⟩
    show g (s (n * m)) a = g (s n) a + _
    rw [smul_sub, ← mul_smul, ← add_sub_assoc, ← h2, h1, add_sub_cancel_right]
  · obtain ⟨r, hr⟩ := (hs n hn).1
    have hr0 : 0 < r := Nat.pos_of_mul_pos_left (hr ▸ (s n).factorial_pos)
    obtain ⟨⟨h1, h2⟩, -⟩ := hg (s n)
    rw [hr] at h1 h2
    refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
    · rintro ⟨e, he⟩
      have he' : g (s n) a = n • e := he
      obtain ⟨b, hb⟩ := (h1 (r • a)).1 ⟨e, by rw [map_nsmul, he', mul_comm, mul_smul]⟩
      exact ⟨b, hc r hr0 _ _ (by rw [hb, mul_comm, mul_smul])⟩
    · rintro ⟨e, rfl⟩
      exact ⟨_, map_nsmul _ _ _⟩
    · obtain ⟨a, e, h⟩ := h2 a'
      exact ⟨a, r • e, by rw [h, mul_smul]⟩
  · obtain ⟨r, hr⟩ := (hs n hn).1
    exact hQ n r _ (hr ▸ (hg (s n)).2)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_valueIdeal (X : Data E r) : ∃ J : FractionalIdeal (𝓞 E)⁰ E, J ≠ 0 ∧ (∀ z ∈ J, cc z ∈ J) ∧
    ∀ L : Lt E r, SelfD X L → ∀ x, x ∈ L ↔ ∀ y ∈ L, herm X.Gm x y ∈ J := by
  set ξ : E := X.κ0 / 2 with hξ
  have hξ' : ξ = X.ξ0 ∨ ξ = -X.ξ0 := X.κ0_xi.imp (fun h => by rw [hξ, h]; ring) fun h => by rw [hξ, h]; ring
  have hξ0 : ξ ≠ 0 := by
    rcases hξ' with h | h <;> rw [h]
    exacts [X.ξ0_ne, neg_ne_zero.2 X.ξ0_ne]
  have hξc : cc ξ = -ξ := by
    have := X.ξ0_im
    rcases hξ' with h | h <;> rw [h]
    · exact this
    · simp only [cc, map_neg] at this ⊢
      rw [this]
  have hI0 : FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hξ0
  have hJ : ∀ z : E, z ∈ FractionalIdeal.dual ℤ ℚ (FractionalIdeal.spanSingleton (𝓞 E)⁰ ξ) ↔
      ∀ a : 𝓞 E, ∃ k : ℤ, Algebra.trace ℚ E (-ξ * ((a : E) * z)) = k := by
    intro z
    rw [FractionalIdeal.mem_dual hI0]
    constructor
    · intro h a
      obtain ⟨k, hk⟩ := h ((-a) • ξ) ((FractionalIdeal.mem_spanSingleton _).2 ⟨-a, rfl⟩)
      refine ⟨k, ?_⟩
      rw [eq_intCast, Algebra.traceForm_apply, Algebra.smul_def, map_neg] at hk
      rw [hk]
      congr 1
      change _ = z * (-(a : E) * ξ)
      ring
    · intro h w hw
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hw
      obtain ⟨k, hk⟩ := h (-c)
      refine ⟨k, ?_⟩
      rw [eq_intCast, ← hk, Algebra.traceForm_apply, Algebra.smul_def]
      congr 1
      change -ξ * (((-c : 𝓞 E) : E) * z) = z * ((c : E) * ξ)
      push_cast
      ring
  have htr : ∀ z : E, Algebra.trace ℚ E (cc z) = Algebra.trace ℚ E z := fun z =>
    Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) z
  refine ⟨_, FractionalIdeal.dual_ne_zero ℤ ℚ hI0, fun z hz => ?_, fun L hL x => ?_⟩
  · rw [hJ] at hz ⊢
    intro a
    obtain ⟨k, hk⟩ := hz (-RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a)
    refine ⟨k, ?_⟩
    rw [← hk, ← htr]
    congr 1
    have e : ((-RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) a : 𝓞 E) : E) = -cc (a : E) := rfl
    rw [e]
    simp only [cc, map_mul, map_neg, IsCMField.complexConj_apply_apply] at hξc ⊢
    rw [hξc]
    ring
  · have hE : ∀ (a : 𝓞 E) (u v : Fin r → E),
        EF X (a • u) v = Algebra.trace ℚ E (-ξ * ((a : E) * herm X.Gm u v)) := fun a u v => by
      rw [EF_def, ← algebraMap_smul E, HermitianTraceFormVanishing.herm_smul_left]
    constructor
    · intro hx y hy
      rw [hJ]
      intro a
      rw [← hE]
      exact (hL.2 _).1 (L.smul_mem a hx) y hy
    · intro h
      refine (hL.2 x).2 fun y hy => ?_
      have := (hJ _).1 (h y hy) 1
      rwa [← hE, one_smul] at this

theorem exists_adelic_matrix [Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E)] (F : Type) [Field F]
    [NumberField F] [Algebra F E] (c : E ≃ₐ[F] E) (hcc : ∀ x, c x = cc x) (X : Data E r) {L L' : Lt E r}
    (hL : SelfD X L) (hL' : SelfD X L') :
    ∃ g : GL (Fin r) (AdLat.RA F E),
      (g : Matrix (Fin r) (Fin r) (AdLat.RA F E)).mulVec '' (AdLat.hat F (L : Set (Fin r → E))) =
        AdLat.hat F (L' : Set (Fin r → E)) ∧
      ∀ x y, AdLat.hermA c X.Gm ((g : Matrix (Fin r) (Fin r) (AdLat.RA F E)) *ᵥ x)
        ((g : Matrix (Fin r) (Fin r) (AdLat.RA F E)) *ᵥ y) = AdLat.hermA c X.Gm x y := by
  obtain ⟨J, hJ0, hJc, hJ⟩ := exists_valueIdeal X
  have h1 : ReciprocityTheory.MultiplicativeHeights.IsLattice L := ⟨hL.1, SW.TensLat.span_of_selfD X hL⟩
  have h2 : ReciprocityTheory.MultiplicativeHeights.IsLattice L' := ⟨hL'.1, SW.TensLat.span_of_selfD X hL'⟩
  have hγ := SelfDualGenus.exists_isLocalIsometry_of_modular hJ0 hJc X.Gm_herm X.Gm_herm X.Gm_det X.Gm_det h2 h1
    (hJ L' hL') (hJ L hL)
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL.1
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  haveI : Module.Finite (𝓞 E) L' := Module.Finite.iff_fg.2 hL'.1
  haveI : Module.Finite ℤ L' := Module.Finite.trans (𝓞 E) L'
  obtain ⟨f, f1, f2, f3⟩ := exists_tower (R := 𝓞 E) (L := L) (M := L')
    (fun n hn a b h => by
      have hn' : (n : E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have h' : (n : E) • (a : Fin r → E) = (n : E) • (b : Fin r → E) := by
        simpa only [Nat.cast_smul_eq_nsmul, Submodule.coe_smul_of_tower] using congrArg Subtype.val h
      exact Subtype.ext (smul_right_injective _ hn' h'))
    (fun n f => ∀ a a' : L, ∃ z ∈ J, herm X.Gm (f a) (f a') - herm X.Gm a a' = n • z)
    (fun n m f h a a' => by
      obtain ⟨z, hz, e⟩ := h a a'
      exact ⟨m • z, nsmul_mem (show z ∈ (J : Submodule (𝓞 E) E) from hz) m, by rw [e, mul_smul]⟩)
    (fun n hn => by
      obtain ⟨f, hf, hf'⟩ := IsomModN.exists_isometry_mod h1 h2 (IsomModN.isLattice_ideal hJ0)
        (fun x hx y hy i _ => (hJ L' hL' x).1 hx y hy) hγ hn
      refine ⟨f, hf, fun a a' => ?_⟩
      obtain ⟨m, hm, e⟩ := hf' a a'
      exact ⟨m 0, hm 0 trivial, e⟩)
  have hh : ∀ x y : Fin r → E, (∑ a, ∑ b, x a * X.Gm a b * c (y b)) = herm X.Gm x y := fun x y => by
    simp only [herm, hcc]
  obtain ⟨g, g1, -, g3⟩ := AdLat.exists_adelic_matrix_of_tower F E r L L' f h1.1 h1.2 h2.1 h2.2 f1 f2
  refine ⟨g, g1, g3 c X.Gm J (fun x hx y hy => ?_) fun n hn x y => ?_⟩
  · rw [hh]
    exact (hJ L' hL' x).1 hx y hy
  · obtain ⟨z, hz, e⟩ := f3 n hn x y
    exact ⟨z, hz, by rw [hh, hh, ← e, add_sub_cancel]⟩

theorem exists_mov_of_selfD {D : D7} {S T : HSp D} (C : Ctx S T) {L : Lt D.host.E T.rank} (hL : SelfD C.X L) :
    ∃ g ∈ GfC T, IsMov (fmt T g) C.X.Λ L := by
  haveI := (hostOfRecord D).unram
  obtain ⟨g, g1, g2⟩ := exists_adelic_matrix D.host.F (Member.cF D)
    (Member.latHat_eq_hat_and_gram D T).2.2.2.2.2.1 C.X (SW.Lev.selfD_of_sympl C.sympl) hL
  rw [C.m.gT] at g2
  obtain ⟨k, hk, rfl⟩ := (UnitarySplit.real_finite_split D T).2.2.2.1 g g2
  refine ⟨k, hk, fun u => ?_⟩
  have e : u ∈ hatV L ↔ u ∈ (AdLat.hat D.host.F (L : Set (Fin T.rank → D.host.E)) : Set _) := Iff.rfl
  rw [e, ← g1]
  exact ⟨fun ⟨u₀, h₀, h⟩ => ⟨u₀, h₀, h.symm⟩, fun ⟨u₀, h₀, h⟩ => ⟨u₀, h₀, h.symm⟩⟩

theorem exists_trivAt_mov : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), ∀ Lv : SW.Level C.X, ∀ L ∈ Lv.lats,
    ∃ g ∈ GfC T, TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
  intro D S T C Lv L hL
  obtain ⟨g, -, hg⟩ := exists_mov_of_selfD C hL.1
  exact ((GlobalTheory.T.self_dual_lattices_at_level D S T C).2 Lv g L hL.1.1 hg).2.2.2 hL

end GlobalTheory.Ker.OntoLat
