module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueRealLinearOfEventuallyAddModDiscrete
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsDerivAt0NotIsDerivAlong
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.LevelAllPrimes

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    ((c : 𝓞 E) + H.rt) * (c - H.rt) = ((c ^ 2 + H.d : ℕ) : 𝓞 E) := by
  push_cast
  linear_combination (-1 : 𝓞 E) * H.rt_sq

theorem _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {c : ℕ} (hc : Nat.Coprime c H.d)
    (ho : Odd (c ^ 2 + H.d)) :
    IsCoprime ((c : 𝓞 E) + H.rt) (c - H.rt) := by
  have h2 : Nat.Coprime 2 (c ^ 2 + H.d) := (Nat.coprime_two_left).2 ho
  have hc' : Nat.Coprime c (c ^ 2 + H.d) := by
    rw [sq, add_comm]
    exact (Nat.coprime_add_mul_right_right c H.d c).2 hc
  have hcop : IsCoprime ((2 * c : ℕ) : ℤ) ((c ^ 2 + H.d : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.mul_left h2 hc')
  obtain ⟨u, v, huv⟩ := hcop
  have key := congrArg (Int.cast : ℤ → 𝓞 E) huv
  push_cast at key
  refine ⟨(u : 𝓞 E) + v * (c - H.rt), u, ?_⟩
  linear_combination key - (v : 𝓞 E) * H.rt_sq

end GlobalTheory.LevelAllPrimes

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem host_bar_rt' (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.bar H.rt = -H.rt := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hconj : starRingEnd ℂ (φ (H.rt : E)) = -φ (H.rt : E) := by
    set z := φ (H.rt : E)
    have hz : z ^ 2 = -(H.d : ℂ) := by
      have := congrArg (fun x : 𝓞 E => φ (x : E)) H.rt_sq
      simpa [z] using this
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
    have hx : z.re = 0 := by
      rcases mul_eq_zero.1 (by linarith : z.re * z.im = 0) with h | h
      · exact h
      · rw [h] at hre; nlinarith
    apply Complex.ext <;> simp [hx]
  have key : ((H.bar H.rt : 𝓞 E) : E) = ((-H.rt : 𝓞 E) : E) := by
    rw [H.bar_eq]
    apply φ.injective
    simpa [IsCMField.complexEmbedding_complexConj] using hconj
  exact RingOfIntegers.coe_injective key

variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem natCast_add_rt_mem_adjoin_w0 (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (c : ℕ) :
    (c : 𝓞 E) + H.rt ∈ Algebra.adjoin ℤ {H.w0} := by
  rw [show (c : 𝓞 E) + H.rt = ((c : 𝓞 E) - 1) + 2 * H.w0 by linear_combination -H.two_weight_eq_one_add_root]
  have hw : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.self_mem_adjoin_singleton ℤ H.w0
  have h2 : (2 : 𝓞 E) ∈ Algebra.adjoin ℤ {H.w0} := by
    simpa using natCast_mem (Algebra.adjoin ℤ {H.w0}) 2
  exact add_mem (sub_mem (natCast_mem _ c) (one_mem _)) (mul_mem h2 hw)

private theorem three_le_mul_div_prime_pow_factorization {a b : ℕ} (p : ℕ) (hab : Nat.Coprime a b)
    (ha : 3 ≤ a) (hb : 3 ≤ b) : 3 ≤ a * b / p ^ (a * b).factorization p := by
  have key : ∀ {x y : ℕ}, 3 ≤ x → 0 < y → x.factorization p = 0 →
      3 ≤ x * y / p ^ (x * y).factorization p := by
    intro x y hx hy hxp
    rw [Nat.factorization_mul (by omega) hy.ne', Finsupp.add_apply, hxp, zero_add,
      Nat.mul_div_assoc x (Nat.ordProj_dvd y p)]
    have : 1 ≤ y / p ^ y.factorization p :=
      Nat.div_pos (Nat.le_of_dvd hy (Nat.ordProj_dvd y p)) (Nat.ordProj_pos y p)
    nlinarith
  by_cases hap : a.factorization p = 0
  · exact key ha (by omega) hap
  · have hbp : b.factorization p = 0 := by
      by_contra hbp
      have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.2 hap)
      have hpa : p ∣ a := Nat.dvd_of_factorization_pos hap
      have hpb : p ∣ b := Nat.dvd_of_factorization_pos hbp
      have hg := Nat.dvd_gcd hpa hpb
      rw [hab.gcd_eq_one] at hg
      exact hp.one_lt.ne' (Nat.dvd_one.1 hg)
    rw [mul_comm]
    exact key hb (by omega) hbp

theorem _root_.GlobalTheory.exists_level_goodAt_all_primes_and_idx :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (A : ℕ), 0 < A →
      ∃ l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H, l.A = A ∧ (∀ p : ℕ, p.Prime → l.GoodAt p) ∧
        ∀ p : ℕ, p.Prime → ∃ i : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Idx H p, i.l = l := by
  intro E _ _ _ H A hA
  obtain ⟨k, hk⟩ : Odd H.d := Nat.odd_iff.2 (by have := H.d_mod; omega)
  have h2d : Nat.Coprime 2 H.d := (Nat.coprime_two_left).2 ⟨k, hk⟩
  have h4d : Nat.Coprime (2 ^ 2 + H.d) H.d := by
    rw [Nat.coprime_add_self_left]
    exact Nat.Coprime.pow_left 2 h2d
  have hc1 : Nat.Coprime 2 H.d := h2d
  have hc2 : Nat.Coprime (2 * (2 ^ 2 + H.d)) H.d := Nat.Coprime.mul_left h2d h4d
  have ho1 : Odd (2 ^ 2 + H.d) := ⟨2 + k, by rw [hk]; ring⟩
  have ho2 : Odd ((2 * (2 ^ 2 + H.d)) ^ 2 + H.d) := by
    refine Even.add_odd ?_ ⟨k, hk⟩
    rw [sq]
    exact (even_two_mul _).mul_right _
  have hM : Nat.Coprime (2 ^ 2 + H.d) ((2 * (2 ^ 2 + H.d)) ^ 2 + H.d) := by
    rw [show (2 * (2 ^ 2 + H.d)) ^ 2 + H.d = H.d + (4 * (2 ^ 2 + H.d)) * (2 ^ 2 + H.d) by ring,
      Nat.coprime_add_mul_right_right]
    exact h4d
  have e1 := _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H 2
  have e2 := _root_.GlobalTheory.LevelAllPrimes.add_rt_mul_sub_rt H (2 * (2 ^ 2 + H.d))
  set M₁ := 2 ^ 2 + H.d with hM₁
  set c := 2 * M₁ with hc
  set M₂ := c ^ 2 + H.d with hM₂
  have hMcop : IsCoprime (M₁ : 𝓞 E) (M₂ : 𝓞 E) := by
    have := (Nat.isCoprime_iff_coprime.2 hM).map (Int.castRingHom (𝓞 E))
    simpa using this
  set al := ((2 : ℕ) + H.rt) * ((c : 𝓞 E) + H.rt) with hal
  have hbar : H.bar al = ((2 : ℕ) - H.rt) * ((c : 𝓞 E) - H.rt) := by
    simp only [hal, map_mul, map_add (f := _), map_natCast, host_bar_rt', sub_eq_add_neg]
  have hmem : al ∈ Algebra.adjoin ℤ {H.w0} :=
    mul_mem (natCast_add_rt_mem_adjoin_w0 H 2) (natCast_add_rt_mem_adjoin_w0 H c)
  have hprod : al * H.bar al = ((M₁ * M₂ : ℕ) : 𝓞 E) := by
    rw [hbar, hal, show ((2 : ℕ) + H.rt) * ((c : 𝓞 E) + H.rt) * (((2 : ℕ) - H.rt) * ((c : 𝓞 E) - H.rt))
      = (((2 : ℕ) + H.rt) * ((2 : ℕ) - H.rt)) * (((c : 𝓞 E) + H.rt) * ((c : 𝓞 E) - H.rt)) by ring,
      e1, e2]
    exact (Nat.cast_mul _ _).symm
  have hcop : IsCoprime al (H.bar al) := by
    rw [hbar, hal]
    refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_)
    · exact _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hc1 ho1
    · exact (hMcop.of_isCoprime_of_dvd_left (Dvd.intro _ e1)).of_isCoprime_of_dvd_right
        (Dvd.intro_left _ e2)
    · exact (hMcop.symm.of_isCoprime_of_dvd_left (Dvd.intro _ e2)).of_isCoprime_of_dvd_right
        (Dvd.intro_left _ e1)
    · exact _root_.GlobalTheory.LevelAllPrimes.isCoprime_add_rt_sub_rt H hc2 ho2
  have h3₁ : 3 ≤ M₁ := by omega
  have h3₂ : 3 ≤ M₂ := by have := Nat.zero_le (c ^ 2); have := H.d_prime.two_le; omega
  obtain ⟨l, hlM, hlA, -⟩ := (_root_.GlobalTheory.level_of_split_and_level_coeff_exist).1 E H al (M₁ * M₂) A
    hmem hprod hcop (le_trans h3₁ (Nat.le_mul_of_pos_right _ (by omega)))
    (Nat.odd_mul.2 ⟨ho1, ho2⟩) hA
  have hgood : ∀ p : ℕ, p.Prime → l.GoodAt p := by
    intro p _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.GoodAt
    rw [hlM]
    exact three_le_mul_div_prime_pow_factorization p hM h3₁ h3₂
  refine ⟨l, hlA, hgood, fun p hp => ?_⟩
  obtain ⟨cf⟩ := (_root_.GlobalTheory.level_of_split_and_level_coeff_exist).2.2 E H l
  exact ⟨{ l := l, c := cf, good := hgood p hp }, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversal
noncomputable section

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

theorem spMap_epsScaleR_comp {S : Type} [CommRing S] (c : S) :
    spMap (epsScaleR c) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  have e : (epsScaleR c).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
    ext s <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  conv_rhs => rw [← e]
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem lieBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (G' : Over (Sp S)) [GrpObj G'] (φ : G'.left ⟶ Xo.univ.t.G.left), IsGrpPullback G' Xo.univ.t.G x φ → (∀ w : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ TanBasis x (fun i => (v i).left ≫ φ) := by
  intro E _ _ _ H Dw l Xo S _ x G' _ φ hp
  let up : ∀ w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left,
      w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x → (epsR S ⟶ G') :=
    fun w h => Over.homMk (hp.1.lift w _ h) (hp.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ φ = w := fun w h => hp.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp S)} {u v : T ⟶ G'}, u.left ≫ φ = v.left ≫ φ → u = v := fun h =>
    Over.OverMorphism.ext (hp.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp S), (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ x) ⟶ Xo.univ.t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hp T))
  have e : η[G'].left ≫ φ = (1 : Over.mk x ⟶ Xo.univ.t.G).left := by
    have e₁ : (1 : 𝟙_ (Over (Sp S)) ⟶ G') = η[G'] := by rw [Hom.one_def]; simp
    rw [← e₁, one]
    exact congrArg (· ≫ (η[Xo.univ.t.G]).left) (Category.id_comp x)
  have zs : spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
      ext s; simp
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  have tan : ∀ w : epsR S ⟶ G', IsTangent w ↔ IsTanAt x (w.left ≫ φ) := fun w => by
    refine ⟨fun h => ⟨Over.w (pushPt hp.1.w w), ?_⟩, fun h => hp.1.hom_ext ?_ ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q ≫ φ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
    · refine (Category.assoc _ _ _).trans ?_
      rw [Over.w w, Over.w η[G']]
      exact zs
  have pr : ∀ {n} (u : Fin n → (epsR S ⟶ G')), (List.ofFn u).prod.left ≫ φ =
      (List.ofFn fun i => (pushPt hp.1.w (u i) : tEps x ⟶ Xo.univ.t.G)).prod.left := fun u =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hp (epsR S)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) w,
      IsLieComb c v w ↔ IsCombAt x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) := fun c v w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => pushPt hp.1.w (u i), fun i => (congrArg (· ≫ φ) (hu i)).trans (Category.assoc _ _ _), (pr u).symm⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => up (u i).left (Over.w _), fun i => hp.1.hom_ext ?_ ?_,
        inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((hu i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (u i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (spMap_epsScaleR_comp (c i)).symm
      · have : u = fun i => (pushPt hp.1.w (up (u i).left (Over.w _)) : tEps x ⟶ Xo.univ.t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (u i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEps x ⟶ Xo.univ.t.G) => (List.ofFn q).prod.left) this
  refine ⟨fun w hw => ⟨up w hw.1, hup _ _⟩, fun n v => ⟨fun hB => ⟨fun i => (tan _).1 (hB.1 i), fun w hw => ?_⟩,
    fun hB => ⟨fun i => (tan _).2 (hB.1 i), fun w hw => ?_⟩⟩⟩
  · have h := hB.2 (up w hw.1) ((tan _).2 (by rw [hup]; exact hw))
    simp only [comb, hup] at h
    exact h
  · have h := hB.2 _ ((tan _).1 hw)
    simp only [comb]
    exact h

end GlobalTheory.Frames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieBasisIffTangentBasisPullbackUniversalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieBasis_iff_tangentBasis_pullback_universal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (G' : Over (Sp S)) [GrpObj G'] (φ : G'.left ⟶ Xo.univ.t.G.left), IsGrpPullback G' Xo.univ.t.G x φ → (∀ w : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w → ∃ v : epsR S ⟶ G', v.left ≫ φ = w) ∧ ∀ (n : ℕ) (v : Fin n → (epsR S ⟶ G')), IsLieBasis v ↔ TanBasis x (fun i => (v i).left ≫ φ) := by
  first | exact @GlobalTheory.Frames.lieBasis_iff_tanBasis | exact GlobalTheory.Frames.lieBasis_iff_tanBasis | (intros; apply GlobalTheory.Frames.lieBasis_iff_tanBasis <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangular
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.PerBor

lemma inv_support {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (h : Matrix n n ℂ) (hu : IsUnit h.det) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    ∀ j j', h⁻¹ j j' ≠ 0 → t j = t j' ∧ w j ≤ w j' := by
  letI := Matrix.invertibleOfIsUnitDet h hu
  have key : ∀ ι : α → ℤ, h⁻¹.BlockTriangular (fun j => toLex (ι (t j), w j)) := by
    intro ι
    refine Matrix.blockTriangular_inv_of_blockTriangular ?_
    intro j j' hlt
    by_contra hne
    obtain ⟨h1, h2⟩ := hs j j' hne
    simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hlt
    omega
  intro j j' hne
  have h1 : ¬ _ := fun hlt => hne (key (fun a => (Fintype.equivFin α a : ℕ)) (i := j) (j := j') hlt)
  have h2 : ¬ _ := fun hlt => hne (key (fun a => -((Fintype.equivFin α a : ℕ) : ℤ)) (i := j) (j := j') hlt)
  simp only [Prod.Lex.toLex_lt_toLex, not_or, not_and, not_lt] at h1 h2
  have h3 : ((Fintype.equivFin α (t j) : ℕ)) = (Fintype.equivFin α (t j') : ℕ) := by omega
  have h4 : t j = t j' := (Fintype.equivFin α).injective (Fin.ext h3)
  exact ⟨h4, h1.2 (by rw [h4])⟩

lemma det_of_support {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') :
    h.det = ∏ j, h j j := by
  refine PerMove.det_of_triangular (fun j => toLex (Fintype.equivFin α (t j), w j)) ?_ _ fun k l hkl => ?_
  · intro k l hkl
    have h' := toLex.injective hkl
    rw [Prod.mk.injEq] at h'
    exact hinj _ _ ((Fintype.equivFin α).injective h'.1) h'.2
  · by_contra hne
    obtain ⟨h1, h2⟩ := hs k l hne
    simp only [h1, Prod.Lex.toLex_lt_toLex, lt_self_iff_false, true_and, false_or] at hkl
    omega

lemma inv_diag {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α] (t : n → α) (w : n → ℕ)
    (hinj : ∀ j j', t j = t j' → w j = w j' → j = j')
    (h : Matrix n n ℂ) (hu : IsUnit h.det) (hs : ∀ j j', h j j' ≠ 0 → t j = t j' ∧ w j ≤ w j') (a : n) :
    h⁻¹ a a = (h a a)⁻¹ := by
  have e := congrFun (congrFun (Matrix.nonsing_inv_mul h hu) a) a
  rw [Matrix.mul_apply, Finset.sum_eq_single a, Matrix.one_apply_eq] at e
  · exact eq_inv_of_mul_eq_one_left e
  · intro c _ hc
    by_contra hne
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 hne
    obtain ⟨h3, h4⟩ := inv_support t w h hu hs _ _ h1
    obtain ⟨_, h6⟩ := hs _ _ h2
    exact hc (hinj _ _ h3.symm (by omega))
  · simp

noncomputable def moveMat {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r g : ℕ} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r)
    (b : Frame Ψ r) : Matrix (Fin g) (Fin g) ℂ :=
  open Classical in
  Matrix.of fun k l => if (idx l).1 = (idx k).1 then
      (if ((idx k).2 : ℕ) < q then FD.mat b (idx k).1 (idx l).2 (idx k).2
        else (FD.mat b (idx k).1)⁻¹ (idx k).2 (idx l).2) else 0

section

variable {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r g : ℕ} (q : ℕ) (idx : Fin g ≃ Ψ × Fin r)
    {b : Frame Ψ r}

lemma moveMat_diag (hb : b ∈ Bor Ψ r) (k : Fin g) : moveMat q idx b k k =
    if ((idx k).2 : ℕ) < q then b (idx k).1 (idx k).2 (idx k).2 else (b (idx k).1 (idx k).2 (idx k).2)⁻¹ := by
  simp only [moveMat, Matrix.of_apply, if_true]
  split_ifs with hk
  · rfl
  · exact PerMove.bor_inv_diag hb _ _

lemma moveMat_support (hb : b ∈ Bor Ψ r) (k l : Fin g) (h : moveMat q idx b k l ≠ 0) :
    (idx l).1 = (idx k).1 ∧ (if ((idx k).2 : ℕ) < q then ((idx l).2 : ℕ) ≤ (idx k).2
      else ((idx k).2 : ℕ) ≤ (idx l).2) := by
  simp only [moveMat, Matrix.of_apply] at h
  by_cases hτ : (idx l).1 = (idx k).1
  · rw [if_pos hτ] at h
    refine ⟨hτ, ?_⟩
    split_ifs at h ⊢ with hk
    · by_contra hlt
      exact h (PerMove.bor_tri hb _ (show (idx k).2 < (idx l).2 by rw [Fin.lt_def]; omega))
    · by_contra hlt
      exact h (PerMove.bor_inv_tri hb _ (show (idx l).2 < (idx k).2 by rw [Fin.lt_def]; omega))
  · rw [if_neg hτ] at h
    exact absurd rfl h

lemma moveMat_mulVec (hb : b ∈ Bor Ψ r) (Gm : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (v : Fin r → E)
    (P P' : Fin g → ℂ)
    (hP : ∀ k, P k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2)
    (hP' : ∀ k, P' k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat (rmul x b) (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat (rmul x b) (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2) :
    P' = moveMat q idx b *ᵥ P := by
  funext k
  have hm : FD.mat (FD.rmul x b) (idx k).1 = FD.mat x (idx k).1 * FD.mat b (idx k).1 := rfl
  rw [hP', hm]
  simp only [moveMat, Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [← idx.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single (idx k).1]
  · simp only [Equiv.apply_symm_apply, if_true, hP]
    split_ifs with hk
    · rw [PerMove.hermC_col_mul]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · rfl
      · rw [PerMove.bor_tri hb (idx k).1 (show (idx k).2 < c by rw [Fin.lt_def]; omega),
          zero_mul, zero_mul]
    · change ((FD.mat x (idx k).1 * FD.mat b (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v)
        (idx k).2 = _
      rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs with hc
      · rw [PerMove.bor_inv_tri hb (idx k).1 (show c < (idx k).2 by rw [Fin.lt_def]; omega),
          zero_mul, zero_mul]
      · rfl
  · intro τ _ hτ
    simp [hτ]
  · simp

end

end GlobalTheory.PerBor

theorem GlobalTheory.per_bor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, ∀ b ∈ Bor (M.X k).Ψ r, ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ a, Pf (rmul x b) a = h₀ *ᵥ Pf x a) ∧ (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ ‖h₀.det‖ = ∏ j, ‖h₀ j j‖ ∧ ((∀ τ i, ‖b τ i i‖ = 1) → ‖h₀.det‖ = 1) ∧ ∀ (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : ℂ), Even n → t₀ ^ 2 * h₀.det = 1 → (∏ j, h₀⁻¹ j j ^ a ((e j).1, (e j).2)) * t₀ ^ n = bchar (laU (unfOf e F M un) a n k) b := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hG hB hN k Pf hPf x hx b hb
  obtain ⟨⟨idx, hty, hcol, hper⟩, hp0, -⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hG hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hG
  have hq : (F.Di k).q = Dw.q := hp0.symm.trans (hB.type k).1
  have hlt : ∀ j, ((idx j).2 : ℕ) < (F.Di k).q → ((e j).2 : ℕ) < (F.Di k).q := by
    intro j hj
    have h1 := hty j
    rw [if_pos hj] at h1
    have h2 := ((M.X k).cmType _).1 (idx j).1.2
    rw [← h1, (hB.type k).2, hrt] at h2
    have h3 : Dw.mult (e j).1 = Dw.q := if_neg h2
    have := (e j).2.isLt
    omega
  have hinj : ∀ j j', (e j).1 = (e j').1 → ((e j).2 : ℕ) = (e j').2 → j = j' := by
    intro j j' h1 h2
    apply e.injective
    refine Sigma.ext h1 ((Fin.heq_ext_iff (by rw [h1])).2 h2)
  have hs : ∀ j j', PerBor.moveMat (F.Di k).q idx b j j' ≠ 0 →
      (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2 := by
    intro j j' hne
    obtain ⟨h1, h2⟩ := PerBor.moveMat_support _ idx hb j j' hne
    have c1 := hcol j
    have c2 := hcol j'
    have l1 := hlt j
    have l2 := hlt j'
    have t1 := hty j
    have t2 := hty j'
    by_cases hj : ((idx j).2 : ℕ) < (F.Di k).q
    · rw [if_pos hj] at h2 c1 t1
      have hj' : ((idx j').2 : ℕ) < (F.Di k).q := by omega
      rw [if_pos hj'] at c2 t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      have := l1 hj
      have := l2 hj'
      omega
    · rw [if_neg hj] at h2 c1 t1
      have hj' : ¬ ((idx j').2 : ℕ) < (F.Di k).q := by omega
      rw [if_neg hj'] at c2 t2
      refine ⟨hbij.1 (by rw [t1, t2, h1]), ?_⟩
      omega
  have hdet := PerBor.det_of_support _ _ hinj _ hs
  have hdiag := PerBor.moveMat_diag (F.Di k).q idx hb
  have hbne : ∀ τ i, b τ i i ≠ 0 := fun τ i => PerMove.bor_diag_ne hb τ i
  have hu : IsUnit (PerBor.moveMat (F.Di k).q idx b).det := by
    rw [hdet, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.2 fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact hbne _ _
    · exact inv_ne_zero (hbne _ _)
  refine ⟨PerBor.moveMat (F.Di k).q idx b, hu, fun a => ?_, PerBor.inv_support _ _ _ hu hs,
    by rw [hdet, norm_prod], fun h1 => ?_, fun un a n t₀ hn ht => ?_⟩
  · exact PerBor.moveMat_mulVec _ idx hb (M.X k).Gm x (M.φ k a : Fin r → E) _ _
      (fun j => by rw [hPf, hper]) (fun j => by rw [hPf, hper])
  · rw [hdet, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [hdiag]
    split_ifs
    · exact h1 _ _
    · rw [norm_inv, h1, inv_one]
  · obtain ⟨m, rfl⟩ := hn
    have ht2 : t₀ ^ 2 = ∏ j, (PerBor.moveMat (F.Di k).q idx b j j)⁻¹ := by
      rw [Finset.prod_inv_distrib, ← hdet]
      exact eq_inv_of_mul_eq_one_left ht
    rw [← two_mul, pow_mul, ht2, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    unfold bchar
    refine Eq.trans ?_ (Fintype.prod_prod_type'
      (fun (τ : (M.X k).Ψ) (i : Fin r) => b τ i i ^ laU (unfOf e F M un) a (2 * m) k τ i))
    rw [← idx.prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [PerBor.inv_diag _ _ hinj _ hu hs, ← pow_add, hdiag]
    have hm' : 2 * m / 2 = m := by omega
    have hp : ((unfOf e F M un).X k).p0 = (F.Di k).q := hp0
    have c1 := hcol j
    have t1 := hty j
    have hinv := Function.leftInverse_invFun hbij.1 (e j).1
    unfold laU
    rw [hp, hm']
    by_cases hj : ((idx j).2 : ℕ) < (F.Di k).q
    · rw [if_pos hj] at c1 t1
      have := hlt j hj
      have t2 : conjEmb (idx j).1.1 = relab c σ (e j).1 := t1.symm
      rw [if_pos hj, if_neg (by omega), t2, hinv,
        show (F.Di k).q - 1 - ((idx j).2 : ℕ) = (e j).2 by omega, inv_pow, ← zpow_natCast, ← zpow_neg]
      congr 1
      push_cast
      ring
    · rw [if_neg hj] at c1 t1
      rw [if_neg hj, if_pos (by omega), ← t1, hinv,
        show ((idx j).2 : ℕ) - (F.Di k).q = (e j).2 by omega, inv_inv, ← zpow_natCast]
      congr 1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TriangularFrameMovesPeriodBlockTriangularStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangularFrame_moves_period_blockTriangular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k Pf, IsPerFr e F M k Pf → ∀ x ∈ (M.X k).dom, ∀ b ∈ Bor (M.X k).Ψ r, ∃ h₀ : Matrix (Fin g) (Fin g) ℂ, IsUnit h₀.det ∧ (∀ a, Pf (rmul x b) a = h₀ *ᵥ Pf x a) ∧ (∀ j j', h₀⁻¹ j j' ≠ 0 → (e j).1 = (e j').1 ∧ ((e j).2 : ℕ) ≤ (e j').2) ∧ ‖h₀.det‖ = ∏ j, ‖h₀ j j‖ ∧ ((∀ τ i, ‖b τ i i‖ = 1) → ‖h₀.det‖ = 1) ∧ ∀ (un : ∀ k, (M.X k).dom → FrPt Xo c (CAt σ)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (t₀ : ℂ), Even n → t₀ ^ 2 * h₀.det = 1 → (∏ j, h₀⁻¹ j j ^ a ((e j).1, (e j).2)) * t₀ ^ n = bchar (laU (unfOf e F M un) a n k) b := by
  first | exact @GlobalTheory.per_bor | exact GlobalTheory.per_bor | (intros; apply GlobalTheory.per_bor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToOfComponents
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolPullback

theorem isHolTo_of_components :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (Y Y' S S' : Scheme.{0}) (φ : Y' ⟶ Y) (p' : Y' ⟶ S') (p : Y ⟶ S) (f : S' ⟶ S) (a : V → (Sp ℂ ⟶ Y')), IsPullback φ p' p f → IsOpen B → IsHolTo B (fun b => a b ≫ φ) → IsHolTo B (fun b => a b ≫ p') → IsHolTo B a :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ H _ h₁ h₂ => GlobalTheory.HolFibre.isHolTo_of_isPullback H h₁ h₂

end GlobalTheory.HolPullback
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibres
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology

namespace GlobalTheory

namespace UniformLift

def toAddHom {V A : Type*} [AddGroup V] [Group A] (e : V → A) (he : ∀ z w, e (z + w) = e z * e w) :
    V →+ Additive A :=
  AddMonoidHom.mk' (fun z => Additive.ofMul (e z)) fun z w => by rw [he, ofMul_mul]

theorem map_zero_eq_one {V A : Type*} [AddGroup V] [Group A] (e : V → A) (he : ∀ z w, e (z + w) = e z * e w) :
    e 0 = 1 :=
  (toAddHom e he).map_zero

theorem addMonoidHom_eq_of_eventuallyEq_addGroup {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [AddGroup A]
    {e e' : V →+ A} (h : e =ᶠ[𝓝 0] e') : e = e' := by
  ext v
  have ht : Tendsto (fun j : ℕ => (2⁻¹ : ℝ) ^ j • v) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2⁻¹ : ℝ)) (by norm_num)
      (by norm_num)).smul_const v
  obtain ⟨j, hj⟩ := (ht.eventually h).exists
  have hv : v = (2 ^ j : ℕ) • (2⁻¹ : ℝ) ^ j • v := by
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp
  rw [hv, map_nsmul, map_nsmul, hj]

theorem existsUnique_linearMap_lift_of_germ {V W A : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] [AddGroup A] {ex : V →+ A} {ex' : W →+ A}
    (hker : IsDiscrete (ex'.ker : Set W)) {k : V → W} (hd : DifferentiableAt ℂ k 0) (h0 : k 0 = 0)
    (hk : ∀ᶠ z in 𝓝 0, ex' (k z) = ex z) : ∃! L : V →ₗ[ℂ] W, ∀ z, ex' (L z) = ex z := by
  have hadd : Tendsto (fun p : V × V ↦ p.1 + p.2) (𝓝 0) (𝓝 0) := by
    simpa using continuous_add.tendsto (0 : V × V)
  have hL := eventuallyEq_fderiv_of_eventually_add_mod_discrete hker hd h0 <| by
    filter_upwards [hadd.eventually hk, (continuous_fst.tendsto (0 : V × V)).eventually hk,
      (continuous_snd.tendsto (0 : V × V)).eventually hk] with p h1 h2 h3
    rw [AddMonoidHom.mem_ker, sub_sub, map_sub, map_add (f := _), h1, h2, h3, map_add (f := _), sub_self]
  have hL' : ex'.comp (fderiv ℂ k 0 : V →+ W) = ex := addMonoidHom_eq_of_eventuallyEq_addGroup <| by
    filter_upwards [hL, hk] with z h1 h2
    change ex' (fderiv ℂ k 0 z) = ex z
    rw [← h1, h2]
  have hL'' : ∀ z, ex' (fderiv ℂ k 0 z) = ex z := fun z => DFunLike.congr_fun hL' z
  refine ⟨(fderiv ℂ k 0 : V →ₗ[ℂ] W), hL'', fun L h => ?_⟩
  have := realLinear_eq_of_sub_mem_discrete hker (L := L.restrictScalars ℝ)
    (L' := (fderiv ℂ k 0 : V →ₗ[ℂ] W).restrictScalars ℝ) fun x => by
      rw [AddMonoidHom.mem_ker, map_sub]
      exact sub_eq_zero.2 ((h x).trans (hL'' x).symm)
  exact LinearMap.ext fun z => DFunLike.congr_fun this z

theorem fibPt_fst {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G) :
    fibPt G x ≫ pullback.fst _ _ = x.left := pullback.lift_fst _ _ _

theorem fibPt_snd {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} (x : Over.mk y ⟶ G) :
    fibPt G x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

theorem fibPt_injective {X : Scheme.{0}} (G : Over X) {y : Sp ℂ ⟶ X} {x x' : Over.mk y ⟶ G}
    (h : fibPt G x = fibPt G x') : x = x' :=
  Over.OverMorphism.ext (by rw [← fibPt_fst, h, fibPt_fst])

end UniformLift

open UniformLift in
theorem existsUnique_linear_lift_fibre :
    ∀ (X X' : Scheme.{0}) (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (y : Sp ℂ ⟶ X) (y' : Sp ℂ ⟶ X') (g g' : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G')) (ψ : pullback G.hom y ⟶ pullback G'.hom y') (ψp : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G')), Smooth G'.hom → (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) → IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) → ((∀ w, ∃! v : epsPt y' ⟶ G', IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) → DiscreteTopology {z // e' z = 1} → ψ ≫ pullback.snd _ _ = pullback.snd _ _ → (∀ x, fibPt G x ≫ ψ = fibPt G' (ψp x)) → ∃! h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), ∀ z, e' (h z) = ψp (e z) := by
  intro X X' G G' _ _ y y' g g' e e' ψ ψp hsm he he' hol hol' hder hdisc hψ hψp
  have hsm' : Smooth (pullback.snd G'.hom y') := inferInstance
  have hd := isDerivAt0_fibre X' G' y' g' e' _ _ _ (fun z => fibPt G' (e' z)) (IsPullback.of_hasPullback G'.hom y')
    (fun z => ⟨fibPt_fst _ _, fibPt_snd _ _⟩) hol' hder
  obtain ⟨k, k0, hka, hk⟩ := LocalLift.exists_local_lift _ (pullback.snd G'.hom y') g g'
    (fun z => fibPt G (e z) ≫ ψ) (fun z => fibPt G' (e' z)) hsm'
    (fun z => by rw [Category.assoc, hψ, fibPt_snd]) (fun z => fibPt_snd _ _)
    ((T.isHolTo_fibPt_and_comp_fibre X G y g e hol).2 _ ψ) (T.isHolTo_fibPt_and_comp_fibre X' G' y' g' e' hol').1 hd
    (by simp only [hψp, map_zero_eq_one e he, map_zero_eq_one e' he', map_one])
  exact existsUnique_linearMap_lift_of_germ
    (ex := toAddHom (fun z => ψp (e z)) fun z w => by rw [he, map_mul]) (ex' := toAddHom e' he')
    ⟨hdisc⟩ hka.differentiableAt k0 (hk.mono fun z hz => fibPt_injective G' (hz.trans (hψp _)))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueLinearLiftUniformisedFibresStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.existsUnique_linear_lift_uniformised_fibres : ∀ (X X' : Scheme.{0}) (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] (y : Sp ℂ ⟶ X) (y' : Sp ℂ ⟶ X') (g g' : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (e' : (Fin g' → ℂ) → (Over.mk y' ⟶ G')) (ψ : pullback G.hom y ⟶ pullback G'.hom y') (ψp : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G')), Smooth G'.hom → (∀ z w, e (z + w) = e z * e w) → (∀ z w, e' (z + w) = e' z * e' w) → IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => (e' z).left) → ((∀ w, ∃! v : epsPt y' ⟶ G', IsDerivAt0 (fun z => (e' z).left) w v.left) ∧ ∀ v : epsPt y' ⟶ G', spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left → ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) → DiscreteTopology {z // e' z = 1} → ψ ≫ pullback.snd _ _ = pullback.snd _ _ → (∀ x, fibPt G x ≫ ψ = fibPt G' (ψp x)) → ∃! h : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), ∀ z, e' (h z) = ψp (e z) := by
  first | exact @GlobalTheory.existsUnique_linear_lift_fibre | exact GlobalTheory.existsUnique_linear_lift_fibre | (intros; apply GlobalTheory.existsUnique_linear_lift_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriods
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriods
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem exists_framePeriods : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, ∃ Pf, IsPerFr e F M k Pf ∧ (∀ Pf', IsPerFr e F M k Pf' → Pf' = Pf) ∧ (∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)) ∧ (∀ a, DifferentiableOn ℂ (fun x => Pf x a) (M.X k).dom) ∧ ∀ P, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ x ∈ (M.X k).dom, Pf x = P := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hg hb hn k
  obtain ⟨⟨idx, hty, -, hper⟩, hp0, hr, hξ, hpos, hφ⟩ := GlobalTheory.T.cmType_letter_frame_column_dictionary E H Dw l Xo c σ g e F r M hg hb hn k
  let φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hφa : ∀ a, φ a = (M.φ k a : Fin r → E) := fun a => rfl
  obtain ⟨-, hφ'⟩ := hφ φ hφa
  have hemb : ∀ (τ : E →+* ℂ) (v w : Fin r → E), Data.emb τ (v + w) = Data.emb τ v + Data.emb τ w := by
    intro τ v w
    funext a
    simp [Data.emb]
  let Pf : Frame (M.X k).Ψ r → ((F.Di k).La →+ (Fin g → ℂ)) := fun x =>
    AddMonoidHom.mk' (fun a j => perFr (M.X k) x (φ a) (relab c σ (e j).1) (e j).2) (by
      intro a b
      funext j
      simp only [Pi.add_apply, hper, map_add (f := _), hemb]
      split_ifs
      · simp only [hermC, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
      · rw [Matrix.mulVec_add, Pi.add_apply])
  have hPf : IsPerFr e F M k Pf := fun x a j => rfl
  have hPf' : ∀ x v j, Pf x v j = if ((idx j).2 : ℕ) < (F.Di k).q then
      hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 (φ v))
      else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 (φ v)) (idx j).2 :=
    fun x v j => (hPf x v j).trans (hper x _ j)
  have hdom : (M.X k).dom = GG (M.X k).Ψ (M.X k).Gm (F.Di k).q := by rw [← hp0]
  obtain ⟨h1, h2⟩ := GlobalTheory.periods_eq_frame_periods E H Dw l Xo _ g _ F k r _ (M.X k).Gm φ (M.X k).Ψ idx Pf
    (hb.type k).2 hty hξ hpos hφ' hr hPf'
  have h3 := (GlobalTheory.per_move E H (F.Di k) r _ (M.X k).Gm φ (M.X k).Ψ (hb.type k).2 g idx _ hty hξ hpos hφ').1
    Pf hPf'
  rw [hdom]
  refine ⟨Pf, hPf, fun Pf' h' => ?_, fun x hx => (h1 x hx).1, h3, h2⟩
  funext x
  exact AddMonoidHom.ext fun a => funext fun j => (h' x a j).trans (hPf x a j).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramePeriodsStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_framePeriods_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, ∃ Pf, IsPerFr e F M k Pf ∧ (∀ Pf', IsPerFr e F M k Pf' → Pf' = Pf) ∧ (∀ x ∈ (M.X k).dom, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) (Pf x)) ∧ (∀ a, DifferentiableOn ℂ (fun x => Pf x a) (M.X k).dom) ∧ ∀ P, IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ x ∈ (M.X k).dom, Pf x = P := by
  first | exact @GlobalTheory.exists_framePeriods | exact GlobalTheory.exists_framePeriods | (intros; apply GlobalTheory.exists_framePeriods <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfIsReducedOfRangeSubset
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_lift_of_isReduced_of_range_subset {Y X Z : Scheme.{0}} [IsReduced Y] (i : Z ⟶ X)
    [IsClosedImmersion i] (a : Y ⟶ X) (h : Set.range a ⊆ Set.range i) :
    ∃ b : Y ⟶ Z, b ≫ i = a := by
  haveI : Surjective (pullback.snd i a) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd i a)
  exact ⟨inv (pullback.snd i a) ≫ pullback.fst i a, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem natCast_ne_zero_of_isUnit_of_fieldPoint {S : Scheme.{0}} {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤))) (Ω : Type) [Field Ω] (t : Sp Ω ⟶ S) : (n : Ω) ≠ 0 := by
  have h := hn.map ((Scheme.ΓSpecIso (.of Ω)).hom.hom.comp t.appTop.hom)
  rw [map_natCast] at h
  exact h.ne_zero

theorem finite_geometric_kernel_of_pow_eq_one :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (n : ℕ), IsAbelianScheme B → n.Prime → (n : k) ≠ 0 → ∀ (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ B)) (Z : Set B.left), IsClosed Z → (∀ x, x ∈ C ↔ Set.range x.left ⊆ Z) → (∀ x ∈ C, x ^ n = 1 → x = 1) → Finite C) → ∀ (S : Scheme.{0}) (G G' Ga : Over S) [GrpObj G] [GrpObj G'] [GrpObj Ga] (io : Ga ⟶ G ⊗ G') (n : ℕ), IsSemiAbelian G' → IsMonHom io → IsClosedImmersion io.left → n.Prime → IsUnit (n : Γ(S, ⊤)) → (∀ (Y : Over S) (x : Y ⟶ Ga), x ^ n = 1 → x ≫ io ≫ fst G G' = 1 → x = 1) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), Finite {x : Over.mk t ⟶ Ga // x ≫ io ≫ fst G G' = 1} := by
  intro hab S G G' Ga _ _ _ io n hG' hio hcl hp hn htors Ω _ _ t
  suffices H : Finite {x : Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t) ⟶ Ga //
      x ≫ io ≫ fst G G' = 1} by
    have e : (𝟙_ (Over (Sp Ω))).hom ≫ t = t := Category.id_comp t
    rwa [e] at H
  haveI := hG'.comm
  haveI := hG'.smooth
  haveI := hG'.quasiCompact
  have h := isGrpPullback_pullback G' t
  let T : Over S := Over.mk ((𝟙_ (Over (Sp Ω))).hom ≫ t)
  let ρ : (𝟙_ (Over (Sp Ω)) ⟶ (Over.pullback t).obj G') →* (T ⟶ G') := pushHom h _
  have hρ : ∀ y, (ρ y).left = y.left ≫ pullback.fst G'.hom t := fun y => rfl
  have hinj : Function.Injective ρ := fun y z hyz => by
    ext1
    refine pullback.hom_ext ?_ ((Over.w y).trans (Over.w z).symm)
    rw [← hρ, ← hρ, hyz]
  have hsurj : Function.Surjective ρ := fun x =>
    ⟨Over.homMk (pullback.lift x.left (𝟙_ (Over (Sp Ω))).hom (Over.w x)) (pullback.lift_snd _ _ _),
      Over.OverMorphism.ext (pullback.lift_fst _ _ _)⟩
  let s : G' ⟶ G ⊗ G' := lift 1 (𝟙 G')
  have hs₁ : ∀ y : T ⟶ G', (y ≫ s) ≫ fst G G' = 1 := fun y => by
    rw [Category.assoc, lift_fst, MonObj.comp_one]
  have hs₂ : ∀ y : T ⟶ G', (y ≫ s) ≫ snd G G' = y := fun y => by
    rw [Category.assoc, lift_snd, Category.comp_id]
  let σ : (T ⟶ G') →* (T ⟶ G ⊗ G') := MonoidHom.mk' (fun y => y ≫ s) fun y z => by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [hs₁, MonObj.mul_comp, hs₁, hs₁, _root_.mul_one]
    · rw [hs₂, MonObj.mul_comp, hs₂, hs₂]
  let κ : (T ⟶ Ga) →* (T ⟶ G ⊗ G') :=
    MonoidHom.mk' (fun x => x ≫ io) fun x y => MonObj.mul_comp x y io
  haveI : Mono io := (Over.forget S).mono_of_mono_map (inferInstanceAs (Mono io.left))
  have hκ : Function.Injective κ := fun x y hxy => (cancel_mono io).1 hxy
  let C := κ.range.comap (σ.comp ρ)
  have hC : Finite C := by
    refine finite_of_isClosed_torusExtension_of_pow_eq_one hab Ω ((Over.pullback t).obj G') n
      (inferInstanceAs (LocallyOfFiniteType (pullback.snd G'.hom t)))
      (inferInstanceAs (QuasiCompact (pullback.snd G'.hom t))) (hG'.fibres Ω t) hp
      (natCast_ne_zero_of_isUnit_of_fieldPoint hn Ω t) C
      ((pullback.fst G'.hom t ≫ s.left) ⁻¹' Set.range io.left)
      (io.left.isClosedEmbedding.isClosed_range.preimage
        (pullback.fst G'.hom t ≫ s.left).continuous) (fun y => ⟨?_, fun hy => ?_⟩) ?_
    · rintro ⟨x, hx⟩ _ ⟨p, rfl⟩
      have e : x.left ≫ io.left = y.left ≫ pullback.fst G'.hom t ≫ s.left :=
        (congrArg (fun z => z.left) hx).trans (Category.assoc _ _ _)
      exact ⟨x.left p, by rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]⟩
    · haveI : IsReduced T.left := inferInstanceAs (IsReduced (Sp Ω))
      obtain ⟨b, hb⟩ := exists_lift_of_isReduced_of_range_subset io.left (ρ y ≫ s).left (by
        rintro _ ⟨p, rfl⟩
        have e : (ρ y ≫ s).left = y.left ≫ pullback.fst G'.hom t ≫ s.left := Category.assoc _ _ _
        rw [e, Scheme.Hom.comp_apply]
        exact hy ⟨p, rfl⟩)
      exact ⟨Over.homMk b (by rw [← Over.w io, ← Category.assoc, hb, Over.w]),
        Over.OverMorphism.ext hb⟩
    · rintro y ⟨x, hx⟩ hy
      have hx1 : x = 1 := by
        refine htors T x (hκ ?_) ?_
        · rw [map_pow, hx, ← map_pow, hy, map_one, map_one]
        · rw [← Category.assoc]
          exact (congrArg (· ≫ fst G G') hx).trans (hs₁ _)
      refine hinj ?_
      rw [map_one, ← hs₂ (ρ y)]
      have e : ρ y ≫ s = 1 := hx.symm.trans (by rw [hx1, map_one])
      rw [e, MonObj.one_comp]
  choose r hr using hsurj
  have key : ∀ x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1},
      κ x.1 = σ (ρ (r (x.1 ≫ io ≫ snd G G'))) := fun x => by
    rw [hr]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · exact ((Category.assoc _ _ _).trans x.2).trans (hs₁ _).symm
    · exact (Category.assoc _ _ _).trans (hs₂ _).symm
  refine Finite.of_injective (fun x : {x : T ⟶ Ga // x ≫ io ≫ fst G G' = 1} =>
    (⟨r (x.1 ≫ io ≫ snd G G'), x.1, key x⟩ : C)) fun x y hxy => Subtype.ext (hκ ?_)
  rw [key x, key y, show r (x.1 ≫ io ≫ snd G G') = r (y.1 ≫ io ≫ snd G G') from
    congrArg Subtype.val hxy]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentEigenbasisExponential
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentEigenbasisExponential
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.LieFrame

theorem sum_single_apply {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (a : Fin (m τ) → ℂ) (i : Fin (m τ)) :
    (∑ i', a i' • (Pi.single (e.symm ⟨τ, i'⟩) 1 : Fin g → ℂ)) (e.symm ⟨τ, i⟩) = a i := by
  rw [Finset.sum_apply, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    have : e.symm ⟨τ, i⟩ ≠ e.symm ⟨τ, b⟩ := fun h =>
      hb (eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2).symm
    simp [Pi.single_eq_of_ne this]
  · simp

theorem eq_sum_single {g : ℕ} {T : Type} {m : T → ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (w : Fin g → ℂ) (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) :
    ∑ i, w (e.symm ⟨τ, i⟩) • (Pi.single (e.symm ⟨τ, i⟩) 1 : Fin g → ℂ) = w := by
  funext j
  obtain ⟨⟨τ', i⟩, rfl⟩ := e.symm.surjective j
  by_cases h : τ' = τ
  · subst h
    exact sum_single_apply e τ' (fun i => w (e.symm ⟨τ', i⟩)) i
  · have h0 : w (e.symm ⟨τ', i⟩) = 0 := by
      by_contra h0
      exact h (by simpa using hw _ h0)
    rw [h0, Finset.sum_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : e.symm ⟨τ', i⟩ ≠ e.symm ⟨τ, b⟩ := fun h' => h (Sigma.mk.inj (e.symm.injective h')).1
    simp [Pi.single_eq_of_ne this]

theorem exists_eigenbasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), (∀ τ i, IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (u τ i)) ∧ (∀ τ i, IsTanAt (S := CAt σ) (F.u k P) (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧ ∀ τ (w : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)), IsTanAt (S := CAt σ) (F.u k P) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → CAt σ, IsCombAt (S := CAt σ) (F.u k P) (u τ) a w := by
  intro E _ _ _ H Dw l Xo c σ g e F k P hP
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F k P hP
  have hu : ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), ∃ v : Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left,
      IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) v := fun τ i => (h2 _).exists
  choose u hu using hu
  refine ⟨u, hu, fun τ i => h1 _ _ (hu τ i), fun τ i => ?_, fun τ w hw hew => ?_⟩
  · refine (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ (hu τ i)).2 fun j hj => ?_
    by_cases hji : j = e.symm ⟨τ, i⟩
    · subst hji
      simp
    · exact absurd (Pi.single_eq_of_ne hji _) hj
  · obtain ⟨z, hz, huniq⟩ := h3 w hw
    have hs := (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F k P hP _ _ τ hz).1 hew
    have hc := GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ g _ F k P hP _ (u τ)
      (fun i => Pi.single (e.symm ⟨τ, i⟩) 1) (hu τ)
    refine ⟨fun i => z (e.symm ⟨τ, i⟩), (hc (fun i => z (e.symm ⟨τ, i⟩)) w).2 ?_, fun a ha => ?_⟩
    · rw [eq_sum_single e τ z hs]
      exact hz
    · have h4 := huniq _ ((hc a w).1 ha)
      funext i
      exact (sum_single_apply e τ a i).symm.trans (congrFun h4 _)

end GlobalTheory.LieFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentEigenbasisExponentialStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangent_eigenbasis_exponential : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ)), IsPeriod (F.Di k) (fun j => relab c σ (e j).1) P → ∃ u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left), (∀ τ i, IsDerivAt0 (fun z => (F.ex k P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (u τ i)) ∧ (∀ τ i, IsTanAt (S := CAt σ) (F.u k P) (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧ ∀ τ (w : (Sp (DualNumber (CAt σ)) ⟶ Xo.univ.t.G.left)), IsTanAt (S := CAt σ) (F.u k P) w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → CAt σ, IsCombAt (S := CAt σ) (F.u k P) (u τ) a w := by
  first | exact @GlobalTheory.LieFrame.exists_eigenbasis | exact GlobalTheory.LieFrame.exists_eigenbasis | (intros; apply GlobalTheory.LieFrame.exists_eigenbasis <;> assumption)
end
end
