module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftExistsOfQuotientLevel
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD TjE KSOKE)
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R}
  {gb : GBase D.toG R'} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R'} {N N₀ c : ℕ}

private theorem qcast {o' : GObj gb N s'} {o : Obj b N₀ s} {f g : S' ⟶ S} (e : f = g) (n : QMap o' o f c) :
    ∃ n' : QMap o' o g c, n'.φ = n.φ := by
  subst e
  exact ⟨n, rfl⟩

private theorem qobj' (hObj : QObj) (β : R →+* R') (hm : Match b gb β) (hN : N = N₀ * c) (h0 : 0 < N) (hc : N₀.Coprime q)
    (o : GObj gb N s') {s₀ : S' ⟶ Sp R} (e : s₀ = s' ≫ spMap β) : ∃ o₀ : Obj b N₀ s₀, Nonempty (QMap o o₀ (𝟙 S') c) := by
  subst e
  exact hObj q D R R' b gb β hm N N₀ c hN h0 hc S' s' o

private theorem sec_hom {X : Scheme.{0}} {A : Over X} (e : 𝟙_ (Over X) ⟶ A) : e.left ≫ A.hom = 𝟙 X := by
  simpa using Over.w e

private theorem sec_lift {X Y : Scheme.{0}} {A : Over X} {B : Over Y} {f : X ⟶ Y} {φ : A.left ⟶ B.left}
    (hc : IsPullback φ A.hom B.hom f) (e : 𝟙_ (Over Y) ⟶ B) : ∃ l : 𝟙_ (Over X) ⟶ A, l.left ≫ φ = f ≫ e.left := by
  refine ⟨Over.homMk (hc.lift (f ≫ e.left) (𝟙 X) (by simp [sec_hom e])) (by simp), ?_⟩
  simp

end SlopeTestRemainingChoices

theorem UpperTheory.hecke_lift_exists_of_quotient_level :
    NumEx → QObj → QComp → QUniq → QLev → TjIsog → TrEta → CongCRT → LiftEx := by
  intro hNumEx hQObj hQComp hQUniq hQLev hTjIsog hTrEta hCRT p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N t c a hN't hNum C' C u hu W
  obtain ⟨hNc, hGen⟩ := hNum
  have hN'c : (N' : ℕ) = S.N₀ * (c * t) := by rw [hN't, hNc, _root_.mul_assoc]
  have h3 : 3 ≤ S.N₀ := S.std.three
  have hcq : S.N₀.Coprime q := S.std.cop
  have hNpos : 0 < (N : ℕ) := by have := N.2.1; omega
  have hN'pos : 0 < (N' : ℕ) := by have := N'.2.1; omega
  have e0 : (C'.j ≫ S.π) ≫ S.M.s = (T.M N').s ≫ spMap (algebraMap (Ow w) E) := by
    rw [Category.assoc, S.ov, C'.ov]
  obtain ⟨o₁, ⟨n₁⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hN'c hN'pos hcq (T.M N').univ e0
  obtain ⟨o₂, ⟨n₂⟩⟩ := qobj' hQObj (algebraMap (Ow w) E) S.mat hNc hNpos hcq W.o e0
  obtain ⟨ψ₀, hψ₀, hiso, htj⟩ := hTjIsog p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev i h hTj hInt u hu N' N (c * t) c
    hN'c hNc W _ o₁ o₂ n₁ n₂
  obtain ⟨x1q, hx1q⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ S.Y.univ S.M.univ C'.j S.π).1 C'.m S.mπ
  obtain ⟨x1c, hx1c⟩ := qcast (show C'.j ≫ S.π = 𝟙 _ ≫ (C'.j ≫ S.π) by simp) x1q
  obtain ⟨x1, hx1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ S.M.univ (𝟙 _) (C'.j ≫ S.π)).2.2.1
    inferInstance n₁ x1c
  have hunit : IsUnit ((q : ℕ) : Γ((T.M N').X, ⊤)) := by
    have hqE : IsUnit (q : E) := (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero).isUnit
    simpa using hqE.map (((T.M N').s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of E)).inv.hom)
  obtain ⟨y₀, ⟨hy₀, m₀, m₁, hm01⟩, -⟩ := Tj.univ _ (C'.j ≫ S.π) o₁ o₂ x1 ψ₀ hunit hiso htj
  obtain ⟨y, hys, hyg⟩ : ∃ y, y ≫ Lj.s = C'.j ∧ y ≫ Lj.g = y₀ :=
    ⟨_, Lj.pb.lift_fst _ _ hy₀.symm, Lj.pb.lift_snd _ _ hy₀.symm⟩
  obtain ⟨n'c, hn'c⟩ := qcast hys.symm C'.m
  obtain ⟨mm, hmm⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o S.Y.univ y Lj.s).2.1 n'c Lj.ms
  obtain ⟨q1, hq1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ Tj.o' (𝟙 _) y₀).1 n₂ m₁
  obtain ⟨q1c, hq1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) q1
  obtain ⟨q2, hq2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' Tj.o' y Lj.g).2.1 q1c Lj.m'
  obtain ⟨q3, hq3⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o Lj.o' S.Y.univ y Lj.t).1 q2 Lj.mt
  obtain ⟨qC, hqC⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N).univ S.Y.univ S.Y.univ C.j (𝟙 _)).2.2.2
    _ _ W.o W.π W.φ C.m
  obtain ⟨A1, hA1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ Lj.o Tj.o y Lj.g).1 mm Lj.m₀
  obtain ⟨B1, hB1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ (T.M N').univ o₁ Tj.o (𝟙 _) y₀).1 n₁ m₀
  obtain ⟨B1c, hB1c⟩ := qcast (show 𝟙 _ ≫ y₀ = y ≫ Lj.g by rw [hyg, Category.id_comp]) B1
  have I1 : mm.φ ≫ Lj.m₀.φ = n₁.φ ≫ m₀.φ := by
    rw [← hA1, ← hB1, ← hB1c]
    exact hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ A1 B1c
  have I2 : mm.φ ≫ Lj.ψ.left = W.ψ.left ≫ q2.φ := by
    apply Lj.m'.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← Lj.sq, reassoc_of% I1, hm01, reassoc_of% hψ₀, ← hq2, hq1c, hq1]
    · simp only [Category.assoc, Over.w, mm.cart.1.w, q2.cart.1.w]
      rw [← Category.assoc (Over.Hom.left W.ψ), Over.w]
  have hIu : Integ L u := integ_of_mem ((hLev u).mp hu).1
  have hCu : CongId L S.𝔞 u := by
    have h1 := ((hLev u).mp hu).2
    rw [S.lev] at h1
    exact ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).1.mp h1).2
  have hCh : CongId L S.𝔞 h := hTj.other S.𝔞 S.sup S.upow
  have hx : ∀ y' : D.La, ∃ v ∈ LaHat D, (L.actG (h * u)) (inAf D ((algebraMap (𝓞 D.F) D.O) a • y')) =
      inAf D ((algebraMap (𝓞 D.F) D.O) a • y') + (N : ℕ) • v := by
    intro y'
    obtain ⟨v₁, hv₁, e₁⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow h hInt).2 a N hNpos N.2.2 hGen).mp hCh y'
    obtain ⟨v₂, hv₂, e₂⟩ := ((hCRT p D G L q r S.N₀ S.𝔞 hcq S.upow u hIu).2 a N hNpos N.2.2 hGen).mp hCu y'
    refine ⟨v₁ + L.actG h v₂, add_mem hv₁ (hInt v₂ hv₂), ?_⟩
    rw [map_mul, Module.End.mul_apply, e₂, map_add (f := _), map_nsmul, e₁, smul_add, add_assoc]
  have I4 : ∀ y' : D.La, ∀ l' : 𝟙_ (Over Lj.Z) ⟶ Lj.o.A, l'.left ≫ Lj.ms.φ = Lj.s ≫ (S.Y.lv y').left →
      ((T.M N').univ.eta (t • ((algebraMap (𝓞 D.F) D.O) a • y'))).left ≫ mm.φ = y ≫ l'.left := by
    intro y' l' hl'
    have hsm : (algebraMap (𝓞 D.F) D.O (↑t * a)) • y' = t • ((algebraMap (𝓞 D.F) D.O) a • y') := by
      rw [map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul]
    apply Lj.ms.cart.1.hom_ext
    · simp only [Category.assoc]
      rw [← hmm, hn'c, hl', reassoc_of% hys, ← C'.lv, hsm]
    · simp only [Category.assoc]
      rw [mm.cart.1.w, reassoc_of% (sec_hom _), sec_hom l']
      simp
  have I3 : ∀ y' : D.La, (W.o.eta ((algebraMap (𝓞 D.F) D.O) a • y')).left ≫ q3.φ =
      (y ≫ Lj.t) ≫ (S.Y.lv y').left := by
    intro y'
    obtain ⟨l', hl'⟩ := sec_lift Lj.ms.cart.1 (S.Y.lv y')
    have hTE := hTrEta p D G L E gb (h * u) _ _ N' N (T.M N').univ W.o W.ψ W.trans N t 1 hN't
      (_root_.mul_one _).symm _ _ (hx y')
    rw [one_smul] at hTE
    have hlv := Lj.lev y' l' hl'
    rw [Over.comp_left, Category.assoc] at hlv
    rw [← hTE, Over.comp_left, hq3]
    simp only [Category.assoc]
    rw [← reassoc_of% I2, reassoc_of% (I4 y' l' hl'), hlv]
  obtain ⟨l, hlev, hl⟩ := hQLev q _ _ _ _ _ _ _ _ a S.𝔞 hNpos hGen _ _ _ W.o o₂ n₂
  obtain ⟨f₀, -, huniq⟩ := S.Y.rep _ _ o₂ l hlev
  obtain ⟨q3c, hq3c⟩ := qcast (show y ≫ Lj.t = 𝟙 _ ≫ (y ≫ Lj.t) by simp) q3
  obtain ⟨μ2, hμ2⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (y ≫ Lj.t)).2.2.1
    inferInstance n₂ q3c
  obtain ⟨qCc, hqCc⟩ := qcast (show W.π ≫ C.j = 𝟙 _ ≫ (W.π ≫ C.j) by simp) qC
  obtain ⟨μ1, hμ1⟩ := (hQComp q _ _ _ _ _ _ _ _ _ _ _ _ _ _ W.o o₂ S.Y.univ (𝟙 _) (W.π ≫ C.j)).2.2.1
    inferInstance n₂ qCc
  have base2 : (y ≫ Lj.t) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    simp only [Category.assoc]
    rw [← S.ov, reassoc_of% Lj.tπ, ← Tj.st, reassoc_of% hyg, reassoc_of% hy₀]
  have base1 : (W.π ≫ C.j) ≫ S.Y.s = (C'.j ≫ S.π) ≫ S.M.s := by
    rw [e0, Category.assoc, C.ov, reassoc_of% W.ov]
  have eq2 := huniq _ ⟨base2, μ2, fun y' => by
    rw [← hl y', Category.assoc, ← hμ2, hq3c, I3 y']⟩
  have eq1 := huniq _ ⟨base1, μ1, fun y' => by
    rw [← hl y', Category.assoc, ← hμ1, hqCc, hqC, ← Category.assoc]
    erw [W.φ.eta]
    rw [Category.assoc, C.lv, Category.assoc]⟩
  have yt : y ≫ Lj.t = W.π ≫ C.j := eq2.trans eq1.symm
  obtain ⟨q3y, hq3y⟩ := qcast yt q3
  refine ⟨⟨y, hys, yt, mm, ?_, ?_⟩⟩
  · rw [← hmm, hn'c]
  · rw [reassoc_of% I2, ← hq3, ← hqC, ← hq3y, hQUniq q _ _ _ _ _ _ _ _ h3 hcq _ _ _ _ _ _ _ q3y qC]
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.BaseExtensionHolds
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CardPow
theorem UpperTheory.Reformulated.B.Qi54.card_pow :
    ∀ {E : Type} [inst : Field E] [NumberField E]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)) (q : ℕ),
    Nat.Prime q →
      (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal →
        ∃ (f : ℕ), Nat.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) = q ^ f := by
  intro E _ _ w q hq hmem
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  letI : Field (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Ideal.Quotient.field w.asIdeal
  letI : Fintype (NumberField.RingOfIntegers E ⧸ w.asIdeal) := Fintype.ofFinite _
  have h0 : (q : NumberField.RingOfIntegers E ⧸ w.asIdeal) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rwa [map_natCast] at this
  haveI : CharP (NumberField.RingOfIntegers E ⧸ w.asIdeal) q :=
    (CharP.charP_iff_prime_eq_zero (p := q) (hp := hq)).mpr h0
  obtain ⟨n, -, hn⟩ := FiniteField.card (NumberField.RingOfIntegers E ⧸ w.asIdeal) q
  exact ⟨n, by rw [Nat.card_eq_fintype_card, hn]⟩
end

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory

private theorem card_quot_of {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Surjective f) (I : Ideal A) (h : ∀ a, a ∈ I ↔ f a = 0) :
    Nat.card (A ⧸ I) = Nat.card B := by
  have hk : I = RingHom.ker f := by
    ext a
    rw [RingHom.mem_ker]
    exact h a
  exact Nat.card_congr ((Ideal.quotEquivOfEq hk).trans (RingHom.quotientKerEquivOfSurjective hf)).toEquiv

section Local

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

private def iota : 𝓞 E →+* Gal.Int.Geo.Ow w :=
  (algebraMap (𝓞 E) E).codRestrict (w.valuation E).valuationSubring
    (fun a => by
      rw [Valuation.mem_valuationSubring_iff]
      exact w.valuation_le_one a)

private theorem iota_mem_max (a : 𝓞 E) :
    iota w a ∈ IsLocalRing.maximalIdeal (Gal.Int.Geo.Ow w) ↔ a ∈ w.asIdeal := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.valuationSubring.integers (w.valuation E)).isUnit_iff_valuation_eq_one,
    ← w.valuation_lt_one_iff_mem (K := E) a]
  exact ⟨fun h => lt_of_le_of_ne (w.valuation_le_one a) h, ne_of_lt⟩

private theorem res_surj :
    Function.Surjective ((IsLocalRing.residue (Gal.Int.Geo.Ow w)).comp (iota w)) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  have hx : (x : E) ∈ w.valuationSubringAtPrime E := by
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    exact x.2
  haveI : IsLocalization w.asIdeal.primeCompl (w.valuationSubringAtPrime E) :=
    Localization.subalgebra.isLocalization_ofField E w.asIdeal.primeCompl
      w.asIdeal.primeCompl_le_nonZeroDivisors
  obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj w.asIdeal.primeCompl
    (⟨x, hx⟩ : w.valuationSubringAtPrime E)
  have hxs : x * iota w (s : 𝓞 E) = iota w a :=
    Subtype.ext (congrArg (fun z : w.valuationSubringAtPrime E => (z : E)) h)
  obtain ⟨c, i, hi, hc⟩ := w.isMaximal.exists_inv s.2
  refine ⟨a * c, ?_⟩
  rw [RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  have hc' : iota w c * iota w (s : 𝓞 E) + iota w i = 1 := by
    rw [← map_mul, ← map_add (f := _), hc, map_one]
  have e1 : iota w (a * c) - x = -(x * iota w i) := by
    rw [map_mul, ← hxs]
    linear_combination x * hc'
  rw [e1]
  exact neg_mem (Ideal.mul_mem_left _ _ ((iota_mem_max w i).2 hi))

private theorem card_res :
    Nat.card (IsLocalRing.ResidueField (Gal.Int.Geo.Ow w)) = Nat.card (𝓞 E ⧸ w.asIdeal) :=
  (card_quot_of _ (res_surj w) w.asIdeal (fun a => by
    rw [RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, iota_mem_max])).symm

private theorem card_pow (q : ℕ) (hq : q.Prime) (h : (q : 𝓞 E) ∈ w.asIdeal) :
    ∃ f : ℕ, Nat.card (𝓞 E ⧸ w.asIdeal) = q ^ f :=
  by apply _root_.UpperTheory.Reformulated.B.Qi54.card_pow <;> assumption

end Local

theorem baseExtension_holds : Gal.Int.Geo.BaseEx := by
  intro q _ D ha hm E _ _ e gb hstd w 𝔴 r hpl hu N₀ h3 hcop
  haveI : Subsingleton (Fin D.a) := by
    rw [ha]
    infer_instance
  have hq : q.Prime := Fact.out
  let j : 𝓞 D.F ≃+* 𝓞 E := NumberField.RingOfIntegers.mapRingEquiv e
  have hj : ∀ c : 𝓞 D.F, ((j c : 𝓞 E) : E) = e (c : D.F) := fun c => rfl
  have hpl' : ∀ c : 𝓞 D.F, c ∈ 𝔴 ↔ j c ∈ w.asIdeal := fun c => hpl c (j c) (hj c)
  have hqm : (q : 𝓞 E) ∈ w.asIdeal := by
    have h := (hpl' (q : 𝓞 D.F)).1 (hu (ES.p_mem_uIdeal D r))
    rwa [map_natCast] at h
  obtain ⟨f, hf⟩ := card_pow w q hq hqm
  have hnw : Ideal.absNorm w.asIdeal = q ^ f := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hf]
  have hroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    linear_combination D.ω * D.tr_eq - D.nm_eq
  let t : 𝓞 D.F →+* Gal.Int.Geo.Ow w := (iota w).comp j.toRingHom
  have hunit : ∀ k : ℕ, k.Coprime q → IsUnit (k : Gal.Int.Geo.Ow w) := by
    intro k hk
    have hkw : (k : 𝓞 E) ∉ w.asIdeal := by
      intro hmem
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hk
      have h1 : (u : 𝓞 E) * (k : 𝓞 E) + (v : 𝓞 E) * (q : 𝓞 E) = 1 := by
        exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) huv
      refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← h1]
      exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hqm)
    by_contra hn
    refine hkw ((iota_mem_max w _).1 ?_)
    rw [map_natCast]
    exact (IsLocalRing.mem_maximalIdeal _).2 hn
  let b : Base D (Gal.Int.Geo.Ow w) :=
    { unit := hunit
      ρ := t D.ω
      ρ_root := by
        have h := congrArg t hroot
        simpa only [map_add (f := _), map_sub, map_mul, map_pow, map_intCast, map_zero] using h
      t := fun _ => t
      t_ω := fun _ => rfl
      comax := fun i j h => absurd (Subsingleton.elim i j) h
      apart := fun i j h => absurd (Subsingleton.elim i j) h }
  refine ⟨f, b, ⟨?_, ?_⟩, ?_, hqm, hnw⟩
  · exact hstd.1
  · exact fun i => RingHom.ext fun c => hstd.2 i c
  · have hsurj : Function.Surjective ((Ideal.Quotient.mk w.asIdeal).comp j.toRingHom) :=
      Ideal.Quotient.mk_surjective.comp j.surjective
    refine
      { pmem := ?_
        card := by rw [card_res, hf]
        three := h3
        cop := hcop
        m1 := hm
        a1 := ha
        ule := hu
        norm := ?_
        tw := fun i x hx => (iota_mem_max w _).2 ((hpl' x).1 hx) }
    · rw [← map_natCast (iota w)]
      exact (iota_mem_max w _).2 hqm
    · rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
        card_quot_of _ hsurj 𝔴 (fun a => by
          rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
          exact hpl' a), hf]

end UpperTheory
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeLiftSeparatedOfLatticeCongruence
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open scoped TensorProduct

section Cart

variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private theorem one_left_cart (hp : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    have e := Over.w (1 : T ⟶ G')
    simp only [Over.mk_hom, Category.assoc, hp.1.w]
    rw [← Category.assoc, e])
  have h := hp.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at h
  have h2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext h
  have h3 : x₀ = 1 := by simpa using h2
  exact congrArg (fun g => g.left) h3

private theorem kill_iff (hp : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') :
    x = 1 ↔ x.left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  constructor
  · rintro rfl
    exact one_left_cart hp T
  · intro h
    apply Over.OverMorphism.ext
    apply hp.1.hom_ext
    · rw [h, one_left_cart hp T]
    · rw [Over.w x, Over.w (1 : T ⟶ G')]

end Cart

private theorem one_left_congr {X Y : Scheme.{0}} {G : Over Y} [GrpObj G] {g g' : X ⟶ Y} (e : g = g') :
    (1 : Over.mk g ⟶ G).left = (1 : Over.mk g' ⟶ G).left := by
  subst e; rfl

private theorem kill_transfer {X Y : Scheme.{0}} {A B : Over Y} [GrpObj B] {g g' : X ⟶ Y} (e : g = g')
    (b : Over.mk g ⟶ A) (b' : Over.mk g' ⟶ A) (hl : b.left = b'.left) (ψ : A ⟶ B) :
    b ≫ ψ = 1 ↔ b' ≫ ψ = 1 := by
  subst e
  obtain rfl : b = b' := Over.OverMorphism.ext hl
  rfl

private theorem unit_left {X Y : Scheme.{0}} (e : Y ⟶ X) : (toUnit (Over.mk e)).left = e := by
  simpa using Over.w (toUnit (Over.mk e))

private theorem kill_chain {X' Z EX X P : Scheme.{0}} {A' Wo : Over X'} {o o' : Over Z} {U : Over EX} {B : Over X}
    [GrpObj o'] [GrpObj U] [GrpObj B] [GrpObj Wo]
    {y : X' ⟶ Z} {tt : Z ⟶ EX} {π : X' ⟶ X} {j : X ⟶ EX} {mφ : A'.left ⟶ o.left} {ψ₀ : o ⟶ o'}
    {mt : o'.left ⟶ U.left} {ψW : A' ⟶ Wo} {φ : Wo.left ⟶ B.left} {cm : B.left ⟶ U.left}
    (h1 : IsGrpPullback o' U tt mt) (h2 : IsGrpPullback Wo B π φ) (h3 : IsGrpPullback B U j cm)
    (hyt : y ≫ tt = π ≫ j) (hmt : mφ ≫ ψ₀.left ≫ mt = ψW.left ≫ φ ≫ cm)
    (e : P ⟶ X') (a : Over.mk e ⟶ A') (b : Over.mk (e ≫ y) ⟶ o) (hb : b.left = a.left ≫ mφ) :
    b ≫ ψ₀ = 1 ↔ a ≫ ψW = 1 := by
  have L : (b ≫ ψ₀).left ≫ mt = (a ≫ ψW).left ≫ φ ≫ cm := by
    simp only [Over.comp_left, Category.assoc, hb]
    rw [hmt]
  have E : (Over.mk (e ≫ y)).hom ≫ tt = (Over.mk e).hom ≫ π ≫ j := by
    simp only [Over.mk_hom, Category.assoc, hyt]
  rw [kill_iff h1, kill_iff (h2.comp h3), L, one_left_congr E]

section Grp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G}

private theorem back_mul {h g : G.GAf} {m M : ℕ} (hb : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h v' = m • v)
    (hd : m ∣ M) (hg : g ∈ L.KN 1) : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * g) v' = M • v := by
  obtain ⟨d, rfl⟩ := hd
  intro v hv
  obtain ⟨v', hv', e⟩ := hb (d • v) (nsmul_mem hv d)
  refine ⟨L.actG g⁻¹ v', integ_of_mem (inv_mem hg) _ hv', ?_⟩
  have e1 : L.actG (h * g) (L.actG g⁻¹ v') = L.actG h v' := by
    rw [← Module.End.mul_apply, ← map_mul, _root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one]
  rw [e1, e, mul_smul]

private theorem mod_iff {g g' : G.GAf} {M : ℕ} {x' : D.La} {x : D.La} {w : AfP p ⊗[ℚ] VQ D} (hg : Integ L g)
    (hw : w ∈ LaHat D) (hgg : L.actG (g * g') (inAf D x) = L.actG g (inAf D x' + M • w)) :
    (∃ v ∈ LaHat D, L.actG g (inAf D x') = M • v) ↔ ∃ v ∈ LaHat D, L.actG (g * g') (inAf D x) = M • v := by
  rw [hgg, map_add (f := _), map_nsmul]
  constructor
  · rintro ⟨v, hv, e⟩
    exact ⟨v + L.actG g w, add_mem hv (hg w hw), by rw [e, smul_add]⟩
  · rintro ⟨v, hv, e⟩
    refine ⟨v - L.actG g w, sub_mem hv (hg w hw), ?_⟩
    rw [smul_sub, ← e, add_sub_cancel_right]

end Grp

theorem UpperTheory.hecke_lift_separated_of_lattice_congruence :
    NumEx → BaseInv → TrEta → TrEtaPt → CongCRT → GrpLat → GrpCong → LiftSep := by
  intro hNum hBI hTr hPt hCRT hLat hCong p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hi hTj hInt Tj Lj N' N
    t c a hN hNumN C' C hdvd u₁ hu₁ u₂ hu₂ v₁ hv₁ v₂ hv₂ W₁ W₂ V₁ V₂ l₁ l₂ Ω _ _ z hz
  have hpos : 0 < N'.1 := by have := N'.2.1; omega
  have hKN : ∀ {g}, g ∈ K₀ → g ∈ L.KN 1 := fun hg => ((hLev _).1 hg).1
  have hNum' : S.Num N'.1 (c * t) (t * a) := by
    rw [hN]
    exact (hNum p D E gb w q r 𝔴 𝔫 S N.1 (by have := N.2.1; omega)).2 c a t hNumN

  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : S.Cl (T.M N').univ (c * t * 1) (((1 : ℕ) : 𝓞 D.F) * (t * a)), C₂.m.φ = C'.m.φ := by
    have : ∀ (c₁ : ℕ) (a₁ : 𝓞 D.F), c₁ = c * t * 1 → a₁ = ((1 : ℕ) : 𝓞 D.F) * (t * a) → ∀ C₁ : S.Cl (T.M N').univ c₁ a₁,
        ∃ C₂ : S.Cl (T.M N').univ (c * t * 1) (((1 : ℕ) : 𝓞 D.F) * (t * a)), C₂.m.φ = C₁.m.φ := by
      rintro _ _ rfl rfl C₁
      exact ⟨C₁, rfl⟩
    exact this _ _ (by simp) (by simp) C'
  have step : ∀ (u v : G.GAf), u ∈ K₀ → v ∈ K₀ → ∀ (W : Wit T (h * u) N' N) (V : Wit T v N' N') (l : Lift S T Lj W C' C) (x : D.La),
      ∃ b : Over.mk ((z ≫ V.π) ≫ l.y) ⟶ Lj.o.A, b.left ≫ Lj.ms.φ = z ≫ ((T.M N').univ.eta x).left ≫ C'.m.φ ∧
        (b ≫ Lj.ψ = 1 ↔ ∃ v' ∈ LaHat D, L.actG (h * u * v) (inAf D x) = N'.1 • v') := by
    intro u v hu hv W V l x
    obtain ⟨x', w', hw', e⟩ := GlobalTheory.T.latticeCompletion_eq_latticeVector_add_nsmul p D N'.1 hpos N'.2.2 (L.actG v (inAf D x))
      (integ_of_mem (hKN hv) _ (AddSubgroup.subset_closure ⟨1, x, fun v => by simp, rfl⟩))
    have hinv := (hBI p D G L E gb w q r 𝔴 𝔫 S k T K₀ hLev N' N' 1 (c * t) (t * a) (by simp) hNum' C₂ C' v hv V).2
    rw [hC₂] at hinv
    have htr := hTr p D G L E gb v (T.M N').X (T.M N').s N' N' (T.M N').univ V.o V.ψ V.trans N'.1 1 1 (by simp) (by simp) x x'
      ⟨w', hw', e⟩
    simp only [one_smul] at htr
    have hugInt : Integ L (h * u) := hInt.mul (integ_of_mem (hKN hu))
    let a₀ : Over.mk (z ≫ V.π) ⟶ (T.M N').univ.A := toUnit _ ≫ (T.M N').univ.eta x'
    have ha₀ : a₀.left = (z ≫ V.π) ≫ ((T.M N').univ.eta x').left := by
      simp only [a₀, Over.comp_left, unit_left]
    let b : Over.mk ((z ≫ V.π) ≫ l.y) ⟶ Lj.o.A := Over.homMk (a₀.left ≫ l.m.φ) (by
      have e1 := l.m.cart.1.w
      have e2 := Over.w a₀
      simp only [Over.mk_hom, Category.assoc] at e2 ⊢
      rw [e1, ← Category.assoc, e2, Category.assoc])
    refine ⟨b, ?_, ?_⟩
    · have e3 := V.φ.eta x'
      have e4 := congrArg (fun g => g.left) htr
      simp only [Over.comp_left] at e4
      show (a₀.left ≫ l.m.φ) ≫ Lj.ms.φ = _
      rw [Category.assoc, l.ms, ha₀, Category.assoc, Category.assoc, ← Category.assoc V.π, ← e3, ← e4]
      simp only [Category.assoc, hinv]
    · have hc := kill_chain (ψ₀ := Lj.ψ) (ψW := W.ψ) Lj.mt.cart W.φ.cart C.m.cart l.yt l.mt (z ≫ V.π) a₀ b rfl
      rw [hc]
      have := (hPt p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans Ω (z ≫ V.π) x').1
      rw [show a₀ ≫ W.ψ = _ from Category.assoc _ _ _, this]
      exact mod_iff hugInt hw' (by rw [map_mul, Module.End.mul_apply, e])
  have key : ∀ x : D.La, (∃ v ∈ LaHat D, L.actG (h * u₁ * v₁) (inAf D x) = N'.1 • v) ↔
      ∃ v ∈ LaHat D, L.actG (h * u₂ * v₂) (inAf D x) = N'.1 • v := by
    intro x
    obtain ⟨b₁, e₁, k₁⟩ := step u₁ v₁ hu₁ hv₁ W₁ V₁ l₁ x
    obtain ⟨b₂, e₂, k₂⟩ := step u₂ v₂ hu₂ hv₂ W₂ V₂ l₂ x
    have hy : (z ≫ V₁.π) ≫ l₁.y = (z ≫ V₂.π) ≫ l₂.y := by
      simpa only [Category.assoc] using hz
    have hl : b₁.left = b₂.left := by
      apply Lj.ms.cart.1.hom_ext
      · rw [e₁, e₂]
      · rw [Over.w b₁, Over.w b₂]
        exact hy
    rw [← k₁, ← k₂]
    exact kill_transfer hy b₁ b₂ hl Lj.ψ
  have hI₁ : Integ L (h * u₁ * v₁) := (hInt.mul (integ_of_mem (hKN hu₁))).mul (integ_of_mem (hKN hv₁))
  have hI₂ : Integ L (h * u₂ * v₂) := (hInt.mul (integ_of_mem (hKN hu₂))).mul (integ_of_mem (hKN hv₂))
  have hB₁ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u₁ * v₁) v' = N'.1 • v := by
    rw [_root_.mul_assoc]
    exact back_mul hTj.back hdvd (mul_mem (hKN hu₁) (hKN hv₁))
  have hB₂ : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u₂ * v₂) v' = N'.1 • v := by
    rw [_root_.mul_assoc]
    exact back_mul hTj.back hdvd (mul_mem (hKN hu₂) (hKN hv₂))
  have hlat := hLat p D G L N'.1 hpos N'.2.2 (h * u₁ * v₁) (h * u₂ * v₂) hI₁ hI₂ hB₁ hB₂ key
  have hcg : CongId L 𝔫 h := by
    rw [S.lev]
    exact (hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow h hInt).1.2 ⟨hTj.away _ S.std.cop, hTj.other _ S.sup S.upow⟩
  have heq : h * (u₁ * v₁ * (u₂ * v₂)⁻¹) * h⁻¹ = h * u₁ * v₁ * (h * u₂ * v₂)⁻¹ := by group
  exact hCong p D G L 𝔫 K₀ hLev h _ hInt hcg (mul_mem (mul_mem hu₁ hv₁) (inv_mem (mul_mem hu₂ hv₂))) (heq ▸ hlat)
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.HeckeCorrespondenceIsogenyOfTraceCrt
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct
open GlobalTheory.CechPic
open UpperTheory.Gal.Int.Geo

section Over

variable {X : Scheme.{0}} {U V A B : Over X} [GrpObj U] [GrpObj V] [GrpObj A] [GrpObj B]

private theorem cartIso {φ : A.left ⟶ B.left} (h : IsGrpPullback A B (𝟙 X) φ) :
    ∃ e : A ≅ B, e.hom.left = φ ∧ IsMonHom e.hom := by
  haveI : IsIso φ := h.1.isIso_fst_of_isIso
  have hw : φ ≫ B.hom = A.hom := by simpa using h.1.w
  have he : (Over.isoMk (asIso φ) hw).hom.left = φ := rfl
  refine ⟨Over.isoMk (asIso φ) hw, rfl, ?_⟩
  apply GlobalTheory.GrpPullPow.isMonHom_of_mul_pts
  intro T x y
  apply Over.OverMorphism.ext
  let j : Over.mk (T.hom ≫ 𝟙 X) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key := h.2 T x y (j ≫ x ≫ (Over.isoMk (asIso φ) hw).hom) (j ≫ y ≫ (Over.isoMk (asIso φ) hw).hom)
    (by simp [j, he]) (by simp [j, he])
  rw [← MonObj.comp_mul] at key
  simpa [j, he] using key.symm

private theorem quasiInv (e₁ : U ≅ A) (e₂ : V ≅ B) [IsMonHom e₁.hom] (ψ : U ⟶ V) (ψ' : V ⟶ U) (n : ℕ)
    (h : ψ ≫ ψ' = 𝟙 U ^ n) : (e₁.inv ≫ ψ ≫ e₂.hom) ≫ e₂.inv ≫ ψ' ≫ e₁.hom = 𝟙 A ^ n := by
  have h2 : (e₁.inv ≫ ψ ≫ e₂.hom) ≫ e₂.inv ≫ ψ' ≫ e₁.hom = e₁.inv ≫ (ψ ≫ ψ') ≫ e₁.hom := by simp
  rw [h2, h, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Iso.inv_hom_id]

private theorem kerIff (e₁ : U ≅ A) (e₂ : V ≅ B) [IsMonHom e₂.hom] (ψ : U ⟶ V) {T : Over X} (g : T ⟶ U) :
    (g ≫ e₁.hom) ≫ e₁.inv ≫ ψ ≫ e₂.hom = 1 ↔ g ≫ ψ = 1 := by
  have e : (g ≫ e₁.hom) ≫ e₁.inv ≫ ψ ≫ e₂.hom = (g ≫ ψ) ≫ e₂.hom := by simp
  rw [e]
  refine ⟨fun h => ?_, fun h => by rw [h, one_comp]⟩
  have := congrArg (· ≫ e₂.inv) h
  simpa [one_comp] using this

end Over

private theorem isoEqOne {X : Scheme.{0}} {A B : Over X} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] {T : Over X} (y : T ⟶ A) :
    y ≫ e.hom = 1 ↔ y = 1 := by
  constructor
  · intro h
    have h' : y = (y ≫ e.hom) ≫ e.inv := by simp
    rw [h', h, MonObj.one_comp]
  · rintro rfl
    exact MonObj.one_comp _

section Pol

variable {X : Scheme.{0}} {U V A B : Over X} [GrpObj U] [IsCommMonObj U] [GrpObj V] [IsCommMonObj V]
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

private theorem square_id : Hecke.sq2 (𝟙 B) = 𝟙 (G2 B).left := by
  unfold Hecke.sq2
  simp

private theorem isIso_sq (e : A ≅ B) {φ₂ : (G2 A).left ⟶ (G2 B).left} (h : Geo.Tor.IsSquare e.hom.left φ₂) :
    IsIso φ₂ := by
  have hsq : Geo.Tor.IsSquare (𝟙 A.left) (𝟙 (G2 A).left) := by
    constructor <;> simp
  have key := ES.PIsogExt.isSquare_square_compatible_homs hsq h (ψ₀ := 𝟙 A) (ψ := e.hom) (by simp)
  rw [square_id, Category.id_comp, Category.id_comp] at key
  rw [← key]
  refine ⟨⟨Hecke.sq2 e.inv, ?_, ?_⟩⟩
  · rw [← Hecke.Comp.grpSchemeSquareProductMap_comp, e.hom_inv_id, square_id]
  · rw [← Hecke.Comp.grpSchemeSquareProductMap_comp, e.inv_hom_id, square_id]

private theorem polMove {PU : LB (G2 U).left} {PV : LB (G2 V).left} {PA : LB (G2 A).left} {PB : LB (G2 B).left}
    (hU : PU.IsLB) (hV : PV.IsLB) (hA : PA.IsLB) (hB : PB.IsLB) (e₁ : U ≅ A) (e₂ : V ≅ B) (ψ : U ⟶ V) (χ : A ⟶ B)
    (he : e₁.hom.left ≫ χ.left = ψ.left ≫ e₂.hom.left) {φ₁ : (G2 U).left ⟶ (G2 A).left} {φ₂ : (G2 V).left ⟶ (G2 B).left}
    (s₁ : Geo.Tor.IsSquare e₁.hom.left φ₁) (s₂ : Geo.Tor.IsSquare e₂.hom.left φ₂)
    (l₁ : LBIso PU (PA.pull φ₁)) (l₂ : LBIso PV (PB.pull φ₂)) (c : ℕ)
    (l : LBIso (Hecke.lbPow PU c) (PV.pull (Hecke.sq2 ψ))) :
    LBIso (Hecke.lbPow PA c) (PB.pull (Hecke.sq2 χ)) := by
  haveI : IsIso φ₁ := isIso_sq e₁ s₁
  have key : φ₁ ≫ Hecke.sq2 χ = Hecke.sq2 ψ ≫ φ₂ := ES.PIsogExt.isSquare_square_compatible_homs s₁ s₂ he
  have hPAc : (Hecke.lbPow PA c).IsLB := LB.isLB_linComb hA _ _
  have hPUc : (Hecke.lbPow PU c).IsLB := LB.isLB_linComb hU _ _
  have hPBχ : (PB.pull (Hecke.sq2 χ)).IsLB := pull_isLB hB _
  rw [← cls_eq_iff hPAc hPBχ]
  have inj : ∀ x y : Pic (G2 A).left, pull φ₁ x = pull φ₁ y → x = y := by
    intro x y hxy
    have hh := congrArg (pull (inv φ₁)) hxy
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at hh
  have h1 : cls PU hU = pull φ₁ (cls PA hA) := by
    rw [← cls_pull hA φ₁ (pull_isLB hA φ₁)]
    exact (cls_eq_iff _ _).2 l₁
  have h2 : cls PV hV = pull φ₂ (cls PB hB) := by
    rw [← cls_pull hB φ₂ (pull_isLB hB φ₂)]
    exact (cls_eq_iff _ _).2 l₂
  have h3 : cls (Hecke.lbPow PU c) hPUc = cls (PV.pull (Hecke.sq2 ψ)) (pull_isLB hV _) := (cls_eq_iff _ _).2 l
  rw [Hecke.Comp.cls_lbPow' hU c hPUc, cls_pull hV] at h3
  apply inj
  rw [Hecke.Comp.cls_lbPow' hA c hPAc, cls_pull hB _ hPBχ, map_nsmul, ← h1, h3, h2, ← pull_comp,
    ← pull_comp, key]

end Pol

private theorem intMul {p : ℕ} [Fact p.Prime] {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

private theorem numEq {p : ℕ} [Fact p.Prime] {c₀ M : ℕ} (hc : c₀.Coprime p) (hM : M.Coprime p) {t t' t₁ t₁' m₀ t₂ : AfP p}
    (ht : IsIntAf t) (ht' : IsIntAf t') (htt : t * t' = 1) (i1 : IsIntAf t₁) (i1' : IsIntAf t₁') (e1 : t₁ * t₁' = 1)
    (im₀ : IsIntAf m₀) (i2 : IsIntAf t₂) (e2 : m₀ * t₂ = 1) (e : (M : AfP p) * t₁ * m₀ = c₀ * t)
    (H : ∀ (c c' : ℕ) (t t' : AfP p), c.Coprime p → c'.Coprime p → IsIntAf t → IsIntAf t' → t * t' = 1 → (c : AfP p) = c' * t → c = c') :
    c₀ = M := by
  refine H c₀ M (t₁ * m₀ * t') (t₁' * t₂ * t) hc hM (intMul (intMul i1 im₀) ht') (intMul (intMul i1' i2) ht) ?_ ?_
  · calc t₁ * m₀ * t' * (t₁' * t₂ * t) = (t₁ * t₁') * (m₀ * t₂) * (t * t') := by ring
      _ = 1 := by rw [e1, e2, htt]; ring
  · calc (c₀ : AfP p) = c₀ * t * t' := by rw [_root_.mul_assoc, htt, _root_.mul_one]
      _ = M * (t₁ * m₀ * t') := by rw [← e]; ring

theorem UpperTheory.heckeCorrespondence_isogeny_of_trace_crt :
    TrEta → TrBack → TrTj → MultUnit → CongCRT → TjIsog := by
  intro hTE hTB hTT hMU hCRT
  intro p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hTj hIh u hu N' N c' c hN' hN W s₀ o₁ o₂ n₁ n₂
  obtain ⟨hu1, huC⟩ := (hLev u).1 hu
  have hIu : Integ L u := integ_of_mem hu1
  rw [S.lev] at huC
  have huN₀ : L.CongOne S.N₀ u := ((hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hIu).1.1 huC).1
  have hhN₀ : L.CongOne S.N₀ h := hTj.away S.N₀ S.std.cop
  have hhu : L.CongOne S.N₀ (h * u) := Link.CongOne.mul L hhN₀ huN₀
  obtain ⟨e₁, he₁, hm₁⟩ := cartIso n₁.cart
  obtain ⟨e₂, he₂, hm₂⟩ := cartIso n₂.cart
  haveI := hm₁
  haveI := hm₂
  haveI : IsMonHom W.ψ := W.trans.1
  have hM : Ideal.absNorm 𝔴 ^ i = q ^ (S.f * i) := by
    rw [S.std.norm, pow_mul]
  have hqp : q.Coprime p := (Nat.coprime_primes (Fact.out) (Fact.out)).2 S.atq.ne
  have hMcop : (q ^ (S.f * i)).Coprime p := Nat.Coprime.pow_left _ hqp
  have hsq : n₁.φ ≫ Over.Hom.left (e₁.inv ≫ W.ψ ≫ e₂.hom) = Over.Hom.left W.ψ ≫ n₂.φ := by
    rw [← he₁, ← he₂]
    simp only [Over.comp_left]
    rw [← Category.assoc, ← Over.comp_left, e₁.hom_inv_id]
    simp
  have a1 : ∀ d : D.O, (T.M N').univ.act.act d ≫ e₁.hom = e₁.hom ≫ o₁.act.act d := by
    intro d
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he₁]
    exact n₁.act d
  have a1' : ∀ d : D.O, o₁.act.act d ≫ e₁.inv = e₁.inv ≫ (T.M N').univ.act.act d := by
    intro d
    rw [Iso.comp_inv_eq, Category.assoc, a1, Iso.inv_hom_id_assoc]
  have a2 : ∀ d : D.O, W.o.act.act d ≫ e₂.hom = e₂.hom ≫ o₂.act.act d := by
    intro d
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he₂]
    exact n₂.act d
  refine ⟨e₁.inv ≫ W.ψ ≫ e₂.hom, hsq, ?_, ?_⟩
  · refine ⟨⟨S.f * i, rfl⟩, inferInstance, ?_, ?_, ?_, ?_⟩
    · intro d
      rw [reassoc_of% (a1' d), reassoc_of% (W.trans.2.1 d), a2]
      simp only [Category.assoc]
    · intro x
      have b1' : (T.M N').univ.eta (c' • x) ≫ e₁.hom = o₁.eta x := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, he₁]
        simpa using n₁.eta x
      have b1 : o₁.eta x ≫ e₁.inv = (T.M N').univ.eta (c' • x) := by
        rw [Iso.comp_inv_eq]
        exact b1'.symm
      have b2 : W.o.eta (c • x) ≫ e₂.hom = o₂.eta x := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, he₂]
        simpa using n₂.eta x
      have b3 : (T.M N').univ.eta (c' • x) ≫ W.ψ = W.o.eta (c • x) :=
        hTE p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans S.N₀ c' c hN' hN
          x x (hhu _ (inAf_mem D x))
      rw [reassoc_of% b1, reassoc_of% b3, b2]
    · obtain ⟨c₀, hc₀, ⟨hl⟩, t, t', ht, ht', htt, hmul⟩ := W.trans.2.2.2.1
      obtain ⟨t₁, t₁', i1, i1', e1, hh⟩ := hTj.mult
      obtain ⟨t₂, im₀, i2, e2⟩ := (hMU p D G L).1 u hu1
      have hc : c₀ = q ^ (S.f * i) := by
        refine numEq hc₀ hMcop ht ht' htt i1 i1' e1 im₀ i2 e2 ?_ (hMU p D G L).2
        rw [← hmul, ← hM]
        push_cast at hh ⊢
        rw [← hh]
        simp [Units.val_mul]
      rw [← hc]
      refine ⟨polMove (T.M N').univ.isLB W.o.isLB o₁.isLB o₂.isLB e₁ e₂ W.ψ (e₁.inv ≫ W.ψ ≫ e₂.hom) ?_
        (by rw [he₁]; exact n₁.sq) (by rw [he₂]; exact n₂.sq) n₁.pol n₂.pol c₀ hl⟩
      rw [he₁, he₂]
      exact hsq
    · have hback : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, (L.actG (h * u)) v' = (q ^ (S.f * i)) • v := by
        intro v hv
        obtain ⟨v'', hv'', hvv⟩ := hTj.back v hv
        have hui : L.CongOne 1 u⁻¹ := hu1.2
        obtain ⟨w₁, hw₁, hw⟩ := hui v'' hv''
        refine ⟨L.actG u⁻¹ v'', ?_, ?_⟩
        · rw [hw, one_smul]
          exact add_mem hv'' hw₁
        · rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (L.actG u), ← map_mul, mul_inv_cancel,
            map_one, Module.End.one_apply, hvv, hM]
      obtain ⟨ψ', hψ', h1, h2⟩ := hTB p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ
        W.trans _ hMcop hback
      haveI := hψ'
      exact ⟨e₂.inv ≫ ψ' ≫ e₁.hom, inferInstance, quasiInv e₁ e₂ W.ψ ψ' _ h1, quasiInv e₂ e₁ ψ' W.ψ _ h2⟩
  · intro kk _ _ _ x
    obtain ⟨hT1, hT2⟩ := hTT p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans q r 𝔴
      i h u S.atq hTj hIh hu1 rfl kk x
    have hk : ∀ (g : Over.mk x ⟶ o₁.A) (d : D.O), g ≫ o₁.act.act d = 1 ↔ (g ≫ e₁.inv) ≫ (T.M N').univ.act.act d = 1 := by
      intro g d
      rw [Category.assoc, ← a1' d, ← Category.assoc]
      haveI : IsMonHom e₁.symm.hom := (inferInstance : IsMonHom e₁.inv)
      exact (isoEqOne e₁.symm (g ≫ o₁.act.act d)).symm
    have hker : ∀ g : Over.mk x ⟶ o₁.A, g ≫ (e₁.inv ≫ W.ψ ≫ e₂.hom) = 1 ↔ (g ≫ e₁.inv) ≫ W.ψ = 1 := by
      intro g
      have := kerIff e₁ e₂ W.ψ (g ≫ e₁.inv)
      simpa using this
    refine ⟨?_, ?_⟩
    · intro g hg ⟨e, he⟩ a ha
      rw [hk]
      refine hT1 (g ≫ e₁.inv) ((hker g).1 hg) ⟨e, fun y hy => (hk g _).1 (he y hy)⟩ a ha
    · rw [S.std.m1, _root_.one_mul, ← hT2]
      refine Nat.card_congr (Equiv.subtypeEquiv
        ⟨fun g => g ≫ e₁.inv, fun g => g ≫ e₁.hom, fun g => by simp, fun g => by simp⟩ ?_)
      intro g
      refine and_congr (hker g) ?_
      exact forall₂_congr fun a _ => hk g _
end
end
