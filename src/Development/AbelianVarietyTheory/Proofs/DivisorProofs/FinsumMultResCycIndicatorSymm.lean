module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LengthSumHeightOneDisjointDivisorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SamePolarisedDataOfIdempotentFactorUniformisatio
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliIntegralNormalLocallyNoetherian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdThetaMapOnNormalCharZeroAffine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumMultResCycIndicatorSymm
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixHt.CycLoc

theorem length_quot_equiv (R S : Type) [CommRing R] [CommRing S] (e : R ≃+* S) (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {e a}) := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  rw [← Module.length_eq_of_surjective (S := R) (R := S) (M := S ⧸ Ideal.span {e a}) e.surjective]
  exact (Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) f (by
    rw [Ideal.map_span, Set.image_singleton]; rfl)).toLinearEquiv.length_eq

theorem finite_height_one (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (a : R) (ha : a ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ a ∈ p.asIdeal}.Finite := by
  refine ((Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {a})).preimage
    (f := PrimeSpectrum.asIdeal) fun _ _ _ _ h => PrimeSpectrum.ext h).subset ?_
  rintro p ⟨hp, hap⟩
  refine ⟨⟨p.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hap⟩, fun q hq hqp => ?_⟩
  by_contra hn
  have := hq.1
  have h1 : q < p.asIdeal := lt_of_le_not_ge hqp hn
  have h0 : (⊥ : Ideal R) < q := bot_lt_iff_ne_bot.2 fun h =>
    ha (by simpa [h] using (Ideal.span_singleton_le_iff_mem _).1 hq.2)
  have e1 := Ideal.height_add_one_le_of_lt_of_isPrime h1
  have e0 := Ideal.height_add_one_le_of_lt_of_isPrime h0
  rw [hp] at e1
  have : (⊥ : Ideal R).height + 1 + 1 ≤ 1 := (add_le_add_left e0 1).trans e1
  rw [Ideal.height_bot] at this
  exact absurd this (by decide)

theorem stalk_equiv (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x p ∈ U) (hx : x ∈ U) (s : Γ(X, U)),
        e (X.presheaf.germ U _ hq s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal) (X.presheaf.germ U x hx s) := by
  let y : Spec (X.presheaf.stalk x) := p
  have := GlobalTheory.LocalRingGeneralisation.isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  refine Eq.trans ?_ h2
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

theorem specializes_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ⤳ x := (Scheme.range_fromSpecStalk (x := x)).le ⟨p, rfl⟩

theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨e, -⟩ := stalk_equiv X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

theorem mem_nonzeroLocus_iff_notMem {X : Scheme.{0}} {A : LB X} (s : A.Sec) {i : A.ι} {x : X} (hi : x ∈ A.U i)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ∈ nonzeroLocus s ↔ X.presheaf.germ _ x hi (s.f i) ∉ p.asIdeal := by
  have hzi : X.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk X x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv X x p
  rw [Cartier.mem_nonzeroLocus_iff s i hzi, Scheme.mem_basicOpen _ _ _ hzi, ← MulEquiv.isUnit_map e, he _ hzi hi,
    IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal, Ideal.mem_primeCompl_iff]

theorem ker_stalkMap_clo (X : Scheme.{0}) (z : X) (w : clo z) (p : PrimeSpectrum (X.presheaf.stalk (cloι z w)))
    (hp : X.fromSpecStalk (cloι z w) p = z) : RingHom.ker ((cloι z).stalkMap w).hom = p.asIdeal := by
  let g : PrimeSpectrum ((clo z).presheaf.stalk w) := ⟨⊥, Ideal.isPrime_bot⟩
  have hg : (clo z).fromSpecStalk w g = genericPoint (clo z) := by
    have h := coheight_fromSpecStalk (clo z) w g
    rw [show g.asIdeal.height = 0 from Ideal.height_bot, Order.coheight_eq_zero] at h
    exact ((genericPoint_specializes _).antisymm (h (show _ ≤ genericPoint (clo z) from genericPoint_specializes _))).eq.symm
  have h : X.fromSpecStalk (cloι z w) (Spec.map ((cloι z).stalkMap w) g) = cloι z ((clo z).fromSpecStalk w g) :=
    (Scheme.Hom.comp_apply _ _ _).symm.trans ((congrArg (fun f => f g)
      (Scheme.SpecMap_stalkMap_fromSpecStalk (cloι z) (x := w))).trans (Scheme.Hom.comp_apply _ _ _))
  rw [hg, cloι_genericPoint] at h
  have h' := (X.fromSpecStalk (cloι z w)).isEmbedding.injective (h.trans hp.symm)
  exact congrArg PrimeSpectrum.asIdeal h'

theorem germ_secPull {X V : Scheme.{0}} {L : LB X} (s : L.Sec) (b : V ⟶ X) (v : V) (i : L.ι) (hi : b v ∈ L.U i)
    (hv : v ∈ (L.pull b).U fun _ => i) :
    V.presheaf.germ _ v hv ((GlobalTheory.secPull s b).f fun _ => i) = b.stalkMap v (X.presheaf.germ _ _ hi (s.f i)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem coheight_one_iff (hq : IsAmb q) {z : Y} (w : clo z) (hz : Order.coheight z = 1) :
    Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2 := by
  have hB := GlobalTheory.MixHt.hasDim_basic k Y q hq
  obtain ⟨m, hm⟩ := hB.1
  obtain ⟨d, -, hd⟩ := hm (genericPoint Y)
  have hY : topologicalKrullDim Y = d := (hB.2.2.2.2.2 Y d).1 hd
  cases d with
  | zero =>
    obtain ⟨d', -, hd'⟩ := hm z
    have := GlobalTheory.T.coheight_add_pointClosureDim_eq_dim k Y q hq 0 hY z d' hd'
    rw [hz] at this
    simp at this
  | succ e => exact ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hY).2 z w hz).2

theorem germ_ne_zero {A : LB Y} {s : A.Sec} (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y} (hi : x ∈ A.U i) :
    Y.presheaf.germ _ x hi (s.f i) ≠ 0 := fun h0 =>
  fnOf_sec_ne_zero hs (gen_mem hi) ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))

variable [IsLocallyNoetherian Y]

theorem mult_eq {A : LB Y} (hA : A.IsLB) (s : A.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) {i : A.ι} {x : Y}
    (hi : x ∈ A.U i) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1) :
    (divOfSec hA s hs).mult (Y.fromSpecStalk x p) = (Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⧸ Ideal.span {(algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
        (Y.presheaf.germ _ x hi (s.f i)))})).toNat := by
  have hzi : Y.fromSpecStalk x p ∈ A.U i := (specializes_fromSpecStalk Y x p).mem_open (A.U i).isOpen hi
  obtain ⟨e, he⟩ := stalk_equiv Y x p
  rw [mult_divOfSec ((coheight_fromSpecStalk Y x p).trans hp) hzi, length_quot_equiv _ _ e, he _ hzi hi]

theorem resCyc_eq (hq : IsAmb q) {B : LB Y} (hB : B.IsLB) (t : B.Sec) {j : B.ι} {x : Y} (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (p : PrimeSpectrum (Y.presheaf.stalk x)) (hp : p.asIdeal.height = 1)
    (ht : Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) {z : Y} (hz : Y.fromSpecStalk x p = z) :
    resCyc hB t (Set.indicator {x} 1) z = (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
      ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸ Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat := by
  have hzx : z ⤳ x := hz ▸ specializes_fromSpecStalk Y x p
  have hz1 : Order.coheight z = 1 := hz ▸ (coheight_fromSpecStalk Y x p).trans hp
  have hzt : z ∈ nonzeroLocus t := hz ▸ (mem_nonzeroLocus_iff_notMem t hj p).2 ht
  obtain ⟨w, rfl⟩ : x ∈ Set.range (cloι z) :=
    hzx.mem_closed (cloι z).isClosedEmbedding.isClosed_range ⟨_, cloι_genericPoint z⟩
  have h : genericPoint (clo z) ∈ nonzeroLocus (GlobalTheory.secPull t (cloι z)) := by
    rw [GlobalTheory.nonzeroLocus_secPull]
    show cloι z (genericPoint (clo z)) ∈ nonzeroLocus t
    rwa [cloι_genericPoint]
  have hw : w ∈ (B.pull (cloι z)).U fun _ => j := Set.mem_iInter.2 fun _ => hj
  have hk := ker_stalkMap_clo Y z w p hz
  let e : (Y.presheaf.stalk (cloι z w) ⧸ p.asIdeal) ≃+* (clo z).presheaf.stalk w :=
    (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective ((cloι z).stalkMap_surjective w))
  rw [resCyc, dite_eq_left h, finsum_eq_single _ w fun w' hw' => by
    rw [Set.indicator_of_notMem (s := {cloι z w}) (a := cloι z w')
      (fun e => hw' ((cloι z).isClosedEmbedding.injective (Set.mem_singleton_iff.1 e))), mul_zero],
    Set.indicator_of_mem (Set.mem_singleton _), Pi.one_apply, mul_one,
    mult_divOfSec ((coheight_one_iff hq w hz1).2 hx) hw, germ_secPull t _ w j hj, length_quot_equiv _ _ e, Int.cast_natCast]
  rfl

theorem of_term_ne_zero (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x z : Y}
    (h : ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z ≠ 0) :
    Order.coheight x = 2 ∧ Order.coheight z = 1 ∧ z ∉ nonzeroLocus s ∧ z ⤳ x := by
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.1 h
  have h1' : (divOfSec hA s hs).mult z ≠ 0 := by exact_mod_cast h1
  have hz := CartierDiv.coheight_eq_one_of_mult_ne_zero h1'
  rw [resCyc] at h2
  split_ifs at h2 with h3
  · obtain ⟨w, hw⟩ := not_forall.1 (mt finsum_eq_zero_of_forall_eq_zero h2)
    obtain ⟨h4, h5⟩ := mul_ne_zero_iff.1 hw
    have h6 : cloι z w = x := Set.mem_singleton_iff.1 (Set.mem_of_indicator_ne_zero h5)
    have h7 := CartierDiv.coheight_eq_one_of_mult_ne_zero (Int.cast_ne_zero.1 h4)
    refine ⟨h6 ▸ (coheight_one_iff hq w hz).1 h7, hz,
      fun h => notMem_supp_divOfSec.2 h (CartierDiv.mem_supp_of_mult_ne_zero h1'), ?_⟩
    have := (genericPoint_specializes w).map (cloι z).continuous
    rwa [cloι_genericPoint, h6] at this
  · exact absurd rfl h2

theorem finsum_eq (hq : IsAmb q) {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec)
    (hs : genericPoint Y ∈ nonzeroLocus s) {x : Y} {i : A.ι} {j : B.ι} (hi : x ∈ A.U i) (hj : x ∈ B.U j)
    (hx : Order.coheight x = 2) (P : Finset (PrimeSpectrum (Y.presheaf.stalk x)))
    (hP : ∀ p, p ∈ P ↔ p.asIdeal.height = 1 ∧ Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal)
    (hb : ∀ p ∈ P, Y.presheaf.germ _ x hj (t.f j) ∉ p.asIdeal) :
    ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z =
      ((∑ p ∈ P, (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⧸ Ideal.span {(algebraMap (Y.presheaf.stalk x) (Localization.AtPrime p.asIdeal)
          (Y.presheaf.germ _ x hi (s.f i)))})).toNat * (Module.length (Y.presheaf.stalk x ⧸ p.asIdeal)
        ((Y.presheaf.stalk x ⧸ p.asIdeal) ⧸
          Ideal.span {Ideal.Quotient.mk p.asIdeal (Y.presheaf.germ _ x hj (t.f j))})).toNat : ℕ) : ℝ) := by
  classical
  let ι : PrimeSpectrum (Y.presheaf.stalk x) → Y := fun p => Y.fromSpecStalk x p
  have hι : Function.Injective ι := (Y.fromSpecStalk x).isEmbedding.injective
  rw [finsum_eq_sum_of_support_subset (s := P.image ι), Finset.sum_image fun _ _ _ _ h => hι h, Nat.cast_sum]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [resCyc_eq hq hB t hj hx p ((hP p).1 hp).1 (hb p hp) rfl, mult_eq hA s hs hi p ((hP p).1 hp).1,
      Int.cast_natCast, Nat.cast_mul]
  · intro z hz
    obtain ⟨-, h1, h2, h3⟩ := of_term_ne_zero hq hA hB s t hs hz
    obtain ⟨p, rfl⟩ := (Scheme.range_fromSpecStalk (x := x)).ge h3
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, (hP p).2 ⟨(coheight_fromSpecStalk Y x p).symm.trans h1,
      not_not.1 (mt (mem_nonzeroLocus_iff_notMem s hi p).2 h2)⟩, rfl⟩)

end GlobalTheory.MixHt.CycLoc

namespace GlobalTheory.MixHt


open CycLoc in
theorem finsum_mult_resCyc_indicator_symm : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (A B : LB Y) (hA : A.IsLB) (hB : B.IsLB) (s : A.Sec) (t : B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → ∀ x : Y, ∑ᶠ z, ((divOfSec hA s hs).mult z : ℝ) * resCyc hB t (Set.indicator {x} 1) z = ∑ᶠ z, ((divOfSec hB t ht).mult z : ℝ) * resCyc hA s (Set.indicator {x} 1) z := by
  intro k _ Y _ _ q hq A B hA hB s t hs ht hst x
  by_cases hx : Order.coheight x = 2
  swap
  · rw [finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hA hB s t hs h).1,
      finsum_eq_zero_of_forall_eq_zero fun z => not_not.1 fun h => hx (of_term_ne_zero hq hB hA t s ht h).1]
  obtain ⟨i, hi⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hA x
  obtain ⟨j, hj⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hB x
  have ha := germ_ne_zero hs hi
  have hb := germ_ne_zero ht hj
  have hP := fun p => (finite_height_one _ _ ha).mem_toFinset (a := p)
  have hQ := fun p => (finite_height_one _ _ hb).mem_toFinset (a := p)
  have key (p : PrimeSpectrum (Y.presheaf.stalk x)) (h1 : p.asIdeal.height = 1)
      (h2 : Y.presheaf.germ _ x hi (s.f i) ∈ p.asIdeal) (h3 : Y.presheaf.germ _ x hj (t.f j) ∈ p.asIdeal) : False :=
    (hst _ ((coheight_fromSpecStalk Y x p).trans h1)).elim
      (fun h => (mem_nonzeroLocus_iff_notMem s hi p).1 h h2) fun h => (mem_nonzeroLocus_iff_notMem t hj p).1 h h3
  rw [finsum_eq hq hA hB s t hs hi hj hx _ hP fun p hp => key p ((hP p).1 hp).1 ((hP p).1 hp).2,
    finsum_eq hq hB hA t s ht hj hi hx _ hQ fun p hp h => key p ((hQ p).1 hp).1 h ((hQ p).1 hp).2]
  refine congrArg _ (GlobalTheory.T.length_sum_height_one_disjoint_divisors _ ?_ _ _ ha hb _ _ hP hQ (Finset.disjoint_left.2 fun p hp hp' =>
    key p ((hP p).1 hp).1 ((hP p).1 hp).2 ((hQ p).1 hp').2))
  rw [ringKrullDim_stalk_eq_coheight, hx]
  rfl

end GlobalTheory.MixHt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalArchIntegralChernPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReDetRelation
open MvPolynomial

namespace GlobalTheory.MxDet

noncomputable def linF {ι : Type} [Fintype ι] (x : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ i, MvPolynomial.C (x i) * MvPolynomial.X i

noncomputable def iterD {ι : Type} : (m : ℕ) → (Fin m → ι) → (MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ)
  | 0, _ => LinearMap.id
  | m + 1, a => (MvPolynomial.pderiv (a 0)).toLinearMap ∘ₗ iterD m (Fin.tail a)

theorem pderiv_linF {ι : Type} [Fintype ι] (x : ι → ℝ) (j : ι) :
    MvPolynomial.pderiv j (linF x) = MvPolynomial.C (x j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [linF, map_sum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hb, hb.symm]
  · simp

theorem iterD_linF_pow {ι : Type} [Fintype ι] (x : ι → ℝ) (N : ℕ) : ∀ (m : ℕ) (a : Fin m → ι),
    iterD m a (linF x ^ N) = MvPolynomial.C ((N.descFactorial m : ℝ) * ∏ j, x (a j)) * linF x ^ (N - m)
  | 0, a => by simp [iterD]
  | m + 1, a => by
    rw [iterD, LinearMap.comp_apply, iterD_linF_pow x N m, Derivation.coeFn_coe, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_pow, pderiv_linF, Nat.descFactorial_succ, Fin.prod_univ_succ, Nat.sub_sub]
    simp only [Fin.tail, Nat.cast_mul, map_mul, map_natCast]
    ring

theorem exists_functional {ι : Type} [Fintype ι] (e : ℕ) (I : (Fin e → ι) → ℝ) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ x : ι → ℝ, T (linF x ^ e) = ∑ a : Fin e → ι, (∏ j, x (a j)) * I a := by
  refine ⟨∑ a : Fin e → ι, (I a / (e.factorial : ℝ)) • (MvPolynomial.lcoeff ℝ 0 ∘ₗ iterD e a), fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast e.factorial_ne_zero
  rw [LinearMap.smul_apply, LinearMap.comp_apply, iterD_linF_pow, Nat.sub_self, pow_zero, mul_one,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_zero_C, Nat.descFactorial_self, smul_eq_mul]
  field_simp

theorem det_comb {ι : Type} [Fintype ι] (e : ℕ) (H : ι → Matrix (Fin e) (Fin e) ℂ) (x : ι → ℝ) :
    (∑ i, (x i : ℂ) • H i).det = ∑ c : Fin e → ι, ((∏ l, x (c l) : ℝ) : ℂ) *
      ∑ σ : Equiv.Perm (Fin e), (Equiv.Perm.sign σ : ℂ) * ∏ l, H (c l) (σ l) l := by
  rw [Matrix.det_apply']
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  ring

end GlobalTheory.MxDet

theorem GlobalTheory.MxDet.re_det_relation : ∀ (ι J : Type) [Fintype ι] [Fintype J] (e : ℕ) (a : J → ℝ) (n : J → ι → ℝ), ∑ j, MvPolynomial.C (a j) * (∑ i, MvPolynomial.C (n j i) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0 → ∀ H : ι → Matrix (Fin e) (Fin e) ℂ, ∑ j, a j * (∑ i, (n j i : ℂ) • H i).det.re = 0 := by
  intro ι J _ _ e a n hrel H
  obtain ⟨T, hT⟩ := GlobalTheory.MxDet.exists_functional e fun c : Fin e → ι =>
    (∑ σ : Equiv.Perm (Fin e), (Equiv.Perm.sign σ : ℂ) * ∏ l, H (c l) (σ l) l).re
  have h := congrArg T hrel
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zero, MvPolynomial.C_mul', LinearMap.map_smul, smul_eq_mul] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have := hT (n j)
  simp only [GlobalTheory.MxDet.linF, MvPolynomial.C_mul'] at this
  rw [this, GlobalTheory.MxDet.det_comb, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Complex.re_ofReal_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalArchIntegralChernPower
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixFun

theorem exists_linear_of_rel {α V : Type} [AddCommGroup V] [Module ℝ V] (v : α → V) (f : α → ℝ)
    (h : ∀ c : α →₀ ℝ, Finsupp.linearCombination ℝ v c = 0 → Finsupp.linearCombination ℝ f c = 0) :
    ∃ Ψ : V →ₗ[ℝ] ℝ, ∀ a, Ψ (v a) = f a := by
  set A := Finsupp.linearCombination ℝ v
  set F := Finsupp.linearCombination ℝ f
  have hker : LinearMap.ker A ≤ LinearMap.ker F := fun c hc => h c hc
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (((LinearMap.ker A).liftQ F hker).comp A.quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, fun a => ?_⟩
  have e1 : v a = A (Finsupp.single a 1) := by simp [A]
  have e2 := LinearMap.congr_fun hg ⟨A (Finsupp.single a 1), LinearMap.mem_range_self _ _⟩
  rw [e1]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply] at e2
  rw [e2]
  simp [F]

end GlobalTheory.MixFun

namespace GlobalTheory.MixFun

theorem exists_functional_archInt : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (e : ℕ) (ι : Type) [Fintype ι] (L : ι → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb L n).ArchIntegrable M e hr) → ∃ Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb L n).archInt M e hr := by
  intro k _ Y _ q hq e ι _ L M r hr hint
  classical
  have := hq.finite
  haveI : Finite (k →+* ℂ) := .of_equiv _ (RingHom.equivIntAlgHom k ℂ).symm
  letI := Fintype.ofFinite (k →+* ℂ)
  refine GlobalTheory.MixFun.exists_linear_of_rel (fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ e)
    (fun n => (comb L n).archInt M e hr) ?_
  intro c hc
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
  simp only [HermLB.archInt, finsum_eq_sum_of_fintype, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [← Finset.sum_coe_sort c.support]
  refine GlobalTheory.ChernLinRel.sum_chernInt_eq_zero k Y q hq.isProjOver σ e c.support (fun j => c j)
    (fun j => comb L j) ?_ _ _ (fun j => hint j σ)
  intro ch y hy
  have key : ∀ n : ι → ℤ, ch.chernDens ((comb L n).φ σ) y = e.factorial / Real.pi ^ e *
      (Matrix.det (∑ l, ((n l : ℝ) : ℂ) • ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)).re := by
    intro n
    rw [AlgChart.chernDens, GlobalTheory.Mean4O.ReadsProj.hess_comb L n σ ch hy _ (mem_pick _ y) _ (fun l => mem_pick _ y)]
  simp only [key]
  have hrel : ∑ j : c.support, MvPolynomial.C (c j) *
      (∑ i, MvPolynomial.C ((j.1 i : ℝ)) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0 := by
    rw [← hc, ← Finset.sum_coe_sort c.support]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.C_mul']
    rfl
  have h0 := GlobalTheory.MxDet.re_det_relation ι c.support e (fun j => c j) (fun j i => (j.1 i : ℝ)) hrel
    (fun l => ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)
  simp_rw [mul_left_comm _ ((e.factorial : ℝ) / Real.pi ^ e)]
  rw [← Finset.mul_sum, h0, mul_zero]

end GlobalTheory.MixFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalArchIntegralChernPowerStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_functional_arch_integral_chern_power : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (e : ℕ) (ι : Type) [Fintype ι] (L : ι → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb L n).ArchIntegrable M e hr) → ∃ Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb L n).archInt M e hr := by
  first | exact @GlobalTheory.MixFun.exists_functional_archInt | exact GlobalTheory.MixFun.exists_functional_archInt | (intros; apply GlobalTheory.MixFun.exists_functional_archInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonal
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixAdd

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem archInt_congr {A B : HermLB q} (h : A.Isometric B) (M : HermLB q) (e : ℕ) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) : A.archInt M e hr = B.archInt M e hr := by
  simp only [HermLB.archInt, h.chernInt_eq]

theorem lin_comb {ι κ : Type} [Fintype ι] [Fintype κ] (m : κ → ι → ℤ) (n : κ → ℤ) :
    (lin fun i => ((∑ j, n j * m j i : ℤ) : ℝ)) = ∑ j, (n j : ℝ) • lin fun i => (m j i : ℝ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lin, Int.cast_sum, Int.cast_mul, map_sum, map_mul, Finset.sum_mul, smul_eq_C_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lin_add {ι : Type} [Fintype ι] (m n : ι → ℤ) :
    (lin fun i => (((m + n) i : ℤ) : ℝ)) = (lin fun i => (m i : ℝ)) + lin fun i => (n i : ℝ) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem mixArch_eq {ι : Type} [Fintype ι] {e : ℕ} (F : ι → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hΨ : ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb F n).archInt M e hr)
    (L : Fin e → HermLB q) (m : Fin e → ι → ℤ) (h : ∀ a, (comb F (m a)).Isometric (L a)) :
    mixArch L M hr = Ψ (∏ a, lin fun i => (m a i : ℝ)) := by
  have h₁ : (fun n => (comb L n).archInt M e hr) =
      fun n : Fin e → ℤ => Ψ ((∑ a, (n a : ℝ) • lin fun i => (m a i : ℝ)) ^ e) := by
    funext n
    rw [← lin_comb, hΨ]
    exact (archInt_congr ((isometric_comb_comb F m n).trans (isometric_comb_congr h n)) M e hr).symm
  rw [mixArch, h₁, FibreProj.pol_pow _ Ψ (Fintype.card_fin e), mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.2 e.factorial_ne_zero

theorem mixArch_add_diag : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ (A B : HermLB q) (L : Fin e → HermLB q),
      mixArch (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr =
        mixArch (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) M hr) ∧
    ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ N : HermLB q,
      mixArch (fun _ : Fin e => N) M hr = N.archInt M e hr := by
  intro hI k _ Y _ q hq M r hr
  classical
  refine ⟨fun e he A B L => ?_, fun e he N => ?_⟩
  · let F : Bool ⊕ Fin e → HermLB q := Sum.elim (fun b => cond b A B) L
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_linear_functional_arch_integral_chern_power k Y q hq (e + 1) _ F M r hr
      fun n => GlobalTheory.T.archIntegrable_of_projArithAmbient hI k Y q hq (e + 1) he M _ r hr
    let u : Bool ⊕ Fin e → Bool ⊕ Fin e → ℤ := fun j => Pi.single j 1
    have key (C : HermLB q) (c : Bool ⊕ Fin e → ℤ) (hc : (comb F c).Isometric C) :
        mixArch (Fin.cons C L : Fin (e + 1) → HermLB q) M hr =
          Ψ ((lin fun i => (c i : ℝ)) * ∏ a : Fin e, lin fun i => (u (Sum.inr a) i : ℝ)) := by
      rw [mixArch_eq F M hr Ψ hΨ (Fin.cons C L) (Fin.cons c fun a => u (Sum.inr a)) (fun a => by
        cases a using Fin.cases with
        | zero => exact hc
        | succ a => exact isometric_comb_single F (Sum.inr a)), Fin.prod_univ_succ]
      rfl
    have hA : (comb F (u (Sum.inl true))).Isometric A := isometric_comb_single F (Sum.inl true)
    have hB : (comb F (u (Sum.inl false))).Isometric B := isometric_comb_single F (Sum.inl false)
    rw [key A _ hA, key B _ hB, key _ _ ((isometric_comb_add F _ _).trans (hA.tens hB)), lin_add, add_mul, map_add (f := _)]
  · let F : Unit → HermLB q := fun _ => N
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_linear_functional_arch_integral_chern_power k Y q hq e _ F M r hr fun n => GlobalTheory.T.archIntegrable_of_projArithAmbient hI k Y q hq e he M _ r hr
    have hN : (comb F (Pi.single () 1)).Isometric N := isometric_comb_single F ()
    rw [mixArch_eq F M hr Ψ hΨ _ (fun _ => Pi.single () 1) fun _ => hN, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hΨ]
    exact archInt_congr hN M e hr

end GlobalTheory.MixAdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedArchIntegral_additive_and_diagonal : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ (A B : HermLB q) (L : Fin e → HermLB q), mixArch (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr = mixArch (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) M hr) ∧ ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ N : HermLB q, mixArch (fun _ : Fin e => N) M hr = N.archInt M e hr := by
  first | exact @GlobalTheory.MixAdd.mixArch_add_diag | exact GlobalTheory.MixAdd.mixArch_add_diag | (intros; apply GlobalTheory.MixAdd.mixArch_add_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPointMapOfAdjointSplitUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPointMapOfAdjointSplitUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
noncomputable section

namespace GlobalTheory.Mum.PowData

open GlobalTheory.Mum.FactorPol


set_option maxHeartbeats 1000000 in
theorem periodRel_of_adj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q inc j hinc hj iq adj qB h k L T
  have hA := hR.1
  have := hR.2
  have := U.gen_hom
  have := U₀.gen_hom
  haveI := hinc
  haveI := hj
  haveI : IsMonHom q := L.1
  obtain ⟨k', tk'⟩ := GlobalTheory.Mum.Two.unifPre_hom_character_const R _ hA D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  have un₀ := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre
  have un := GlobalTheory.Mum.Two.over₀_onTorus_unique R _ hA D D A A G G U.toUnifPre U.toUnifPre
  have kh : ∀ χ, k' (h χ) = χ := congrFun ((un₀ _).2 _ _ (iq ▸ onTorus_comp tk' L.2.2.2) onTorus_id)
  have hinj : Function.Injective h := Function.LeftInverse.injective kh
  have C := GlobalTheory.Mum.Two.coord_of_lin R _ hA D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q qB h L
  obtain ⟨c, hc, gc⟩ : ∃ c : A.A ⟶ A₀.A, IsMonHom c ∧ Gen₀ U.toUnifPre U₀.toUnifPre q c :=
    ⟨U.gen.inv ≫ (Over.pullback (jK R)).map q ≫ U₀.gen.hom, inferInstance, by simp [Gen₀]⟩
  obtain ⟨c', hc', gc'⟩ : ∃ c' : A₀.A ⟶ A.A, IsMonHom c' ∧ Gen₀ U₀.toUnifPre U.toUnifPre j c' :=
    ⟨U₀.gen.inv ≫ (Over.pullback (jK R)).map j ≫ U.gen.hom, inferInstance, by simp [Gen₀]⟩
  haveI := hc
  haveI := hc'
  obtain ⟨E, eG, eA⟩ := (GlobalTheory.UT.functorial_of_unif R _ hA D A G hG U).1 (q ≫ j) (c ≫ c') inferInstance inferInstance
    (by
      unfold Gen₀ at gc gc'
      rw [Functor.map_comp, Category.assoc, gc', ← Category.assoc, gc, Category.assoc])
  have hL := U.LG.isLB
  have hL₀ := U₀.LG.isLB

  have lamE : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) (x ≫ q ≫ j) y = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [lam_comm, ← Category.assoc, adj, lam_comm]
  have lamE' : ∀ (T' : Over (Sp R)) (x y : T' ⟶ G),
      lam (cls U.LG.L hL) x (y ≫ q ≫ j) = lam (cls U₀.LG.L hL₀) (x ≫ q) (y ≫ q) := fun T' x y => by
    rw [← Category.assoc, adj]
  have adjE : LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E.aG] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL _ _ _).trans (Eq.trans (by rw [eG, lamE, lamE']) (cls_cube_two hL _ _ _).symm))
  have H₂ : LBIso (cubeLB G₀ ![fst G G ≫ q, snd G G ≫ q] U₀.LG.L)
      (cubeLB G ![fst G G ≫ E.aG, snd G G ≫ 𝟙 G] U.LG.L) :=
    (cls_eq_iff (LB.isLB_linComb hL₀ _ _) (LB.isLB_linComb hL _ _)).1
      ((cls_cube_two hL₀ _ _ _).trans (Eq.trans (by rw [eG, Category.comp_id, lamE]) (cls_cube_two hL _ _ _).symm))
  have H₃ := GlobalTheory.Mum.Two.lbIso_cubeLB_generic R _ D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre q q E.aG (𝟙 _) c c E.aA (𝟙 _)
    gc gc E.ext (by simp [Gen₀]) H₂
  obtain ⟨Ω, _, _, _, K⟩ := GlobalTheory.Mum.Two.exists_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C hinj
  obtain ⟨φ, hφ, hhφ⟩ := GlobalTheory.Mum.Two.periods_of_key R _ hA D D₀ A A₀ G G₀ hG hG₀ U U₀ q c qB h hc gc L C E E adjE H₃
    Ω K

  have eh : (⇑E.h : D.toPre.X → D.toPre.X) = ⇑h ∘ ⇑k :=
    (un _).2 _ _ (eG ▸ (lin_of_endU E).1.2.2.2) (onTorus_comp L.2.2.2 T)
  have hφk : ∀ y, φ y = k y := fun y => hinj ((hhφ y).trans (congrFun eh y))
  have hB := D.tau_bimult
  refine ⟨fun y => ?_, fun χ => ?_⟩
  · obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have h1 := ha.1
    rw [hg'.1, (GlobalTheory.TorusExt.isIota_iota hB y).1] at h1
    rw [← hφk y]
    refine GlobalTheory.Mum.Two.Fac.pt_ext R D₀.toPre Ω _ _ ?_
    simpa only [Category.assoc] using h1
  · obtain ⟨u, hu, -⟩ := C χ
    refine ⟨u, hu, fun y z J hJ => ?_⟩
    obtain ⟨g', ha, hg'⟩ := hφ y _ (GlobalTheory.TorusExt.isIota_iota hB y)
    have e := GlobalTheory.Mum.Two.act_val_frac R D₀.toPre D.toPre qB h Ω y (φ y) _ g' (GlobalTheory.TorusExt.isIota_iota hB y) hg' ha χ u hu
      z J hJ
    rwa [hφk] at e

end GlobalTheory.Mum.PowData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPointMapOfAdjointSplitUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodPoint_map_of_adjoint_split_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (h : D₀.toPre.X →+ D.toPre.X) (k : D.toPre.X →+ D₀.toPre.X), Lin U.toUnifPre U₀.toUnifPre q qB h → OnTorus U₀.toUnifPre U.toUnifPre j k → (∀ y, D₀.toPre.c (k y) = D.toPre.c y ≫ qB) ∧ PeriodRel D.toPre D₀.toPre qB h k := by
  first | exact @GlobalTheory.Mum.PowData.periodRel_of_adj | exact GlobalTheory.Mum.PowData.periodRel_of_adj | (intros; apply GlobalTheory.Mum.PowData.periodRel_of_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointAbelianPartsOfUniformisedRetract
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointAbelianPartsOfUniformisedRetract
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData

noncomputable section

namespace GlobalTheory.Mum.PowData

theorem cls_lam_proj {S : Scheme.{0}} {H : Over S} [GrpObj H] {L : LB H.left} (hL : L.IsLB) (h : (abelian₂ H L).IsLB) :
    cls (abelian₂ H L) h = lam (cls L hL) (fst H H) (snd H H) :=
  cls_cube_two hL (fst H H) (snd H H) h

theorem lbIso_iff_lam {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {L₁ : LB H₁.left} {L₂ : LB H₂.left}
    (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (f g : H₁ ⟶ H₂) :
    LBIso (abelian₂ H₁ L₁) ((abelian₂ H₂ L₂).pull (lift (fst H₁ H₁ ≫ f) (snd H₁ H₁ ≫ g) : G2 H₁ ⟶ G2 H₂).left) ↔
      ∀ (T : Over S) (x z : T ⟶ H₁), lam (cls L₁ h₁) x z = lam (cls L₂ h₂) (x ≫ f) (z ≫ g) := by
  have hA : (abelian₂ H₁ L₁).IsLB := LB.isLB_linComb h₁ _ _
  have hB : (abelian₂ H₂ L₂).IsLB := LB.isLB_linComb h₂ _ _
  rw [← cls_eq_iff hA (pull_isLB hB _), cls_pull hB, cls_lam_proj h₁, cls_lam_proj h₂, pull_lam, lift_fst, lift_snd]
  constructor
  · intro h T x z
    have e := congrArg (pull (lift x z).left) h
    simpa only [pull_lam, lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd] using e
  · intro h
    exact h _ _ _

theorem lam_of_rosatiGen {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {M : LB B.left} (hM : M.IsLB)
    {a b : B ⟶ B} (u : LB.Gen (LB.LinComb M (rosatiφ B a b) rosatiε)) (hu : u.IsGen) {T : Over S} (x y : T ⟶ B) :
    lam (cls M hM) (x ≫ a) y = lam (cls M hM) x (y ≫ b) := by
  unfold lam
  rw [GlobalTheory.EndRosati.cls_of_rosati hM u hu x y]

end GlobalTheory.Mum.PowData

namespace GlobalTheory.Mum.PowData


set_option maxHeartbeats 1000000 in
theorem adjCls_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  intro R _ _ _ hR D D₀ A A₀ G G₀ _ _ _ _ hG hG₀ U U₀ q r inc j hq hr hinc hj hiq hjr hqj hri qB jB hqB hjB hOq hOj
  obtain ⟨hAdm, hCZ⟩ := hR
  obtain ⟨incB, hincB, hOinc⟩ := exists_abelian_hom R _ hAdm D₀ D A₀ A G₀ G U₀.toUnifPre U.toUnifPre inc hinc
  obtain ⟨rB, hrB, hOr⟩ := exists_abelian_hom R _ hAdm D D₀ A A₀ G G₀ U.toUnifPre U₀.toUnifPre r hr
  have hjrB : jB ≫ rB = 𝟙 _ :=
    (over₀_onTorus_unique R _ hAdm D₀ D₀ A₀ A₀ G₀ G₀ U₀.toUnifPre U₀.toUnifPre (j ≫ r)).1 _ _
      (FactorPol.over_comp hOj hOr) (by rw [hjr]; exact FactorPol.over_id)

  have h1 : ∀ (T : Over (Sp R)) (x z : T ⟶ G₀),
      lam (cls U₀.LG.L U₀.LG.isLB) x z = lam (cls U.LG.L U.LG.isLB) (x ≫ inc) (z ≫ j) := by
    intro T x z
    rw [hqj T (x ≫ inc) z, Category.assoc, hiq, Category.comp_id]
  have hI := GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart R hAdm D₀ D A₀ A G₀ G hG₀ hG U₀ U inc j incB jB hinc hj hincB hjB hOinc hOj
    ((lbIso_iff_lam U₀.LG.isLB U.LG.isLB inc j).2 h1)
  have h1B := (lbIso_iff_lam D₀.toPre.P.isLB D.toPre.P.isLB incB jB).1 hI

  have hadj : ∀ (T : Over (Sp R)) (x z : T ⟶ G),
      lam (cls U.LG.L U.LG.isLB) (x ≫ q ≫ inc) z = lam (cls U.LG.L U.LG.isLB) x (z ≫ r ≫ j) := by
    intro T x z
    rw [lam_comm, ← Category.assoc x, hri T z (x ≫ q), lam_comm, ← hqj T x (z ≫ r), Category.assoc]
  have hiso : LBIso (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L)
      (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L) := by
    have ha : (cubeLB G ![fst G G ≫ (q ≫ inc), snd G G] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    have hb : (cubeLB G ![fst G G, snd G G ≫ (r ≫ j)] U.LG.L).IsLB := LB.isLB_linComb U.LG.isLB _ _
    refine (cls_eq_iff ha hb).1 ?_
    rw [cls_cube_two U.LG.isLB _ _ ha, cls_cube_two U.LG.isLB _ _ hb]
    exact hadj _ _ _

  haveI : IsMonHom U.gen.hom := U.gen_hom
  have hext : ∀ a : G ⟶ G, (Over.pullback (jK R)).map a ≫ U.gen.hom =
      U.gen.hom ≫ (U.gen.inv ≫ (Over.pullback (jK R)).map a ≫ U.gen.hom) := fun a => by simp
  obtain ⟨E, hE, -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (q ≫ inc) _ inferInstance inferInstance (hext _)
  obtain ⟨E', hE', -⟩ := exists_degenerationEndomorphism_of_admissibleBase R _ hAdm D A G hG U (r ≫ j) _ inferInstance inferInstance (hext _)
  have hros := (rosatiAdjoint_and_linear_of_admissibleBase R _ hAdm D A G hG U E E' (by rw [hE, hE']; exact hiso)).2.1
  have hEB : E.aB = qB ≫ incB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E.aG).1 _ _ (lin_of_endU E).1.2.2.1
      (by rw [hE]; exact FactorPol.over_comp hOq hOinc)
  have hE'B : E'.aB = rB ≫ jB :=
    (over₀_onTorus_unique R _ hAdm D D A A G G U.toUnifPre U.toUnifPre E'.aG).1 _ _ (lin_of_endU E').1.2.2.1
      (by rw [hE']; exact FactorPol.over_comp hOr hOj)
  haveI := E.homB
  haveI := E'.homB
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.firstFiveLaws.1.globalFns D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hros
  intro T x z
  rw [h1B T (x ≫ qB) z, Category.assoc, ← hEB, lam_of_rosatiGen D.toPre.P.isLB u hu, hE'B, Category.assoc,
    reassoc_of% hjrB]

end GlobalTheory.Mum.PowData
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointAbelianPartsOfUniformisedRetractStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjoint_abelianParts_of_uniformised_retract : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D₀ : DegData R (maximalIdeal R)) (A A₀ : PolAV (Sp (FractionRing R))) (G G₀ : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G₀] [IsCommMonObj G₀], IsSemiAbelian G → IsSemiAbelian G₀ → ∀ (U : Unif (maximalIdeal R) D A G) (U₀ : Unif (maximalIdeal R) D₀ A₀ G₀), ∀ (q r : G ⟶ G₀) (inc j : G₀ ⟶ G), IsMonHom q → IsMonHom r → IsMonHom inc → IsMonHom j → inc ≫ q = 𝟙 G₀ → j ≫ r = 𝟙 G₀ → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) q j → AdjCls (cls U.LG.L U.LG.isLB) (cls U₀.LG.L U₀.LG.isLB) r inc → ∀ (qB : D.toPre.P.A ⟶ D₀.toPre.P.A) (jB : D₀.toPre.P.A ⟶ D.toPre.P.A), IsMonHom qB → IsMonHom jB → Over₀ U.toUnifPre U₀.toUnifPre q qB → Over₀ U₀.toUnifPre U.toUnifPre j jB → AdjCls (cls D.toPre.P.L D.toPre.P.isLB) (cls D₀.toPre.P.L D₀.toPre.P.isLB) qB jB := by
  first | exact @GlobalTheory.Mum.PowData.adjCls_abelianPart | exact GlobalTheory.Mum.PowData.adjCls_abelianPart | (intros; apply GlobalTheory.Mum.PowData.adjCls_abelianPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapEighthPowerSiegelModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SFamCharZeroAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegelTor

theorem sFam_charZero_affineOpen : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (U : F.X.affineOpens),
    Nontrivial Γ(F.X, U) → CharZero Γ(F.X, U) := by
  intro g n F U hU
  have hW : IsAffineOpen (U : F.X.Opens) := U.2
  have : SmoothOfRelativeDimension (g * (g + 1) / 2) F.s := F.smooth
  have : Smooth F.s := by first | exact SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s | exact F.smooth.smooth | infer_instance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hW.fromSpec ≫ F.s)
  have h₁ : φ.hom.Flat := by rw [← Flat.SpecMap_iff, hφ]; infer_instance
  letI : Algebra (cycAway n) Γ(F.X, U) := φ.hom.toAlgebra
  have : Module.Flat (cycAway n) Γ(F.X, U) := h₁
  refine charZero_of_inj_zero fun k hk => by_contra fun h0 => ?_
  have hk' : ((k : cycAway n) : ℂ) ≠ 0 := by simpa using h0
  have hne : (k : cycAway n) ≠ 0 := fun h => hk' (by rw [h]; rfl)
  have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(F.X, U)) (r := (k : cycAway n))
    (mem_nonZeroDivisors_of_ne_zero hne)).right_eq_zero_of_smul (x := 1) (by rw [Algebra.smul_def, _root_.mul_one, map_natCast]; exact hk)
  exact one_ne_zero this

end GlobalTheory.SiegelTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapEighthPowerSiegelModuli
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SiegTh

theorem exists_thMap_of_affine_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen →
    ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (s : X ⟶ Sp o) (q : X ⟶ S), Odd m → 3 ≤ m → IsUnit (m : o) → n + 1 = m ^ (4 * g) →
    IsReduced X → (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X), PolFib G L g (x ≫ q)) →
    (∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U)) →
    ∃ f : X ⟶ PSpace o n, f ≫ PSpace.str o n = s ∧ ThMap G L ρ m q f := by
  intro S G _ _ L ρ hL hρ g m n o _ X s q hmo hm3 hmu hn hred hP hA
  have hloc : ∀ x : X, ∃ (W : X.Opens) (h : W.toScheme ⟶ PSpace o n), x ∈ W ∧ h ≫ PSpace.str o n = W.ι ≫ s ∧
      ThMap G L ρ m (W.ι ≫ q) h := by
    intro x
    obtain ⟨U, hxU, h1, h2, h3, h4⟩ := hA x
    exact GlobalTheory.T.exists_nhd_thetaMap_on_normal_charZero_affine S G L ρ hL hρ g m n o X s q hmo hm3 hmu hn hP U h1 h2 h3 h4 x hxU
  choose W h hxW hs hT using hloc
  have hag : ∀ i j (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ (W i).toScheme) (y' : Sp K ⟶ (W j).toScheme),
      y ≫ (W i).ι = y' ≫ (W j).ι → y ≫ h i = y' ≫ h j := by
    intro i j K _ _ y y' e
    have hPK := hP K (y ≫ (W i).ι)
    obtain ⟨⟨θ, hθ⟩, -⟩ := gen_of_polFib S G L hL g K _ hPK
    have hmK : (m : K) ≠ 0 := by
      have := hmu.map (Spec.preimage (y ≫ (W i).ι ≫ s)).hom
      rw [map_natCast] at this
      exact this.ne_zero
    obtain ⟨pt, c, hc⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m (n + 1) K _ θ hmo hmK hn hPK
    have hH : HasTh G L ρ m ((y ≫ (W i).ι) ≫ q) c := ⟨θ, pt, hθ, hc⟩
    have h1 := hT i K y c (by rw [Category.assoc] at hH; exact hH)
    have h2 := hT j K y' c (by rw [e, Category.assoc] at hH; exact hH)
    refine CrdUniq.eq_of_pCrd ?_ h1 h2
    rw [Category.assoc, Category.assoc, hs, hs, ← Category.assoc, e, Category.assoc]
  have hcov : (⨆ x, W x) = ⊤ :=
    eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxW x⟩
  obtain ⟨f, hf, hfi⟩ := GlobalTheory.ThetaGlue.glue_geom o n X s X W h hcov hs hag
  refine ⟨f, hf, fun K _ x c hH => ?_⟩
  let z : X := x.base (IsLocalRing.closedPoint K)
  have hr : Set.range x.base ⊆ Set.range (W z).ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim p (IsLocalRing.closedPoint K)]
    exact hxW z
  let x' : Sp K ⟶ (W z).toScheme := IsOpenImmersion.lift (W z).ι x hr
  have hx : x' ≫ (W z).ι = x := IsOpenImmersion.lift_fac _ _ _
  have h1 := hT z K x' c (by rw [← Category.assoc, hx]; exact hH)
  rw [← hx, Category.assoc, hfi]
  exact h1

theorem exists_thAt : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ), P.g = 8 * g → GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) → rig.IsGen → Odd m → 3 ≤ m → IsUnit (m : cycAway n) → ∃ (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f := by
  intro g n hg hn hno F W hW P rig m hPg hSh hrig hmo hm3 hmu
  obtain ⟨hI, hN, hLN⟩ := GlobalTheory.T.siegelModuli_integral_normal_locallyNoetherian g n hg hn hno F
  letI := P.isAb.comm
  have hpos : 0 < m ^ (4 * (8 * g)) := pow_pos (by omega) _
  have hA : ∀ x : F.X, ∃ U : F.X.affineOpens, x ∈ (U : F.X.Opens) ∧ IsDomain Γ(F.X, U) ∧ IsNoetherianRing Γ(F.X, U) ∧
      IsIntegrallyClosed Γ(F.X, U) ∧ CharZero Γ(F.X, U) := fun x => by
    obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp F.X.isBasis_affineOpens)
      (show x ∈ (⊤ : F.X.Opens) from trivial)
    have hne : (U : F.X.Opens) ≠ ⊥ := fun h => by simp [h] at hxU
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.affineOpen_ring_isDomain_noetherian_integrallyClosed F.X hI hN hLN ⟨U, hU⟩ hne
    exact ⟨⟨U, hU⟩, hxU, h1, h2, h3, GlobalTheory.SiegelTor.sFam_charZero_affineOpen g n F ⟨U, hU⟩ inferInstance⟩
  obtain ⟨f, hf, hT⟩ := exists_thMap_of_affine_cover F.X P.A P.L rig P.isLB hrig P.g m (m ^ (4 * (8 * g)) - 1) (cycAway n) F.X F.s (𝟙 F.X)
    hmo hm3 hmu (by rw [hPg]; omega) inferInstance (fun R _ x => by simpa using GlobalTheory.UMin.FibExist.polFib_of_point F.X P R x) hA
  exact ⟨_, f, hPg, hSh, hrig, hmo, hm3, hmu, by omega, hf, hT, hW⟩

end GlobalTheory.SiegTh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapEighthPowerSiegelModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaMap_eighthPower_siegelModuli : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m : ℕ), P.g = 8 * g → GlobalTheory.Poinc.SharpOver F W P (𝟙 F.X) → rig.IsGen → Odd m → 3 ≤ m → IsUnit (m : cycAway n) → ∃ (N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f := by
  first | exact @GlobalTheory.SiegTh.exists_thAt | exact GlobalTheory.SiegTh.exists_thAt | (intros; apply GlobalTheory.SiegTh.exists_thAt <;> assumption)
end
end
