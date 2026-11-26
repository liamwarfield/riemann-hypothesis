module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffNormBoundedRingLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueJet
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterOnPoints
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCharacter

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FamGerm GlobalTheory.KernelNoTorsion

theorem ringAct_natCast {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Λ : Type} [Ring Λ]
    (ρ : RingAct A Λ) (n : ℕ) : ρ.act n = (𝟙 A) ^ n := by
  induction n with
  | zero =>
    have h : ρ.act 0 = ρ.act 0 * ρ.act 0 := by
      have := ρ.map_add 0 0
      rwa [add_zero] at this
    rw [Nat.cast_zero, pow_zero]
    exact left_eq_mul.mp h
  | succ n ih =>
    rw [Nat.cast_succ, ρ.map_add, ih, ρ.map_one, pow_succ]
    rfl

abbrev Admissible {V O : Type} [CommRing V] [IsLocalRing V] [CommRing O] (f : V →+* O) (A : Type) [CommRing A]
    [Algebra O A] : Prop :=
  (Module.Finite O A ∧ Module.Free O A) ∨ ∃ n : ℕ, ∀ a ∈ maximalIdeal V ^ n, algebraMap O A (f a) = 0

theorem dualBC_inr {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (s : O) :
    dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr s) = TrivSqZeroExt.inr (algebraMap O R s) :=
  TrivSqZeroExt.lift_apply_inr _ _ _ _ _ s

theorem fst_comp_dualBC {O R : Type} [CommRing O] [CommRing R] [Algebra O R] :
    (TrivSqZeroExt.fstHom O R R).comp (dualBC (Algebra.ofId O R)) =
      (Algebra.ofId O R).comp (TrivSqZeroExt.fstHom O O O) := by
  apply DualNumber.algHom_ext
  show (dualBC (Algebra.ofId O R) (TrivSqZeroExt.inr 1)).fst =
    algebraMap O R (TrivSqZeroExt.inr 1 : DualNumber O).fst
  rw [dualBC_inr, TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_inr, map_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

theorem dAct_eq_map {R O F Λ : Type} [CommRing R] [CommRing O] [CommRing F] [CommRing Λ] [StarRing Λ] [Algebra R F]
    [Algebra O F] (f : R →+* O) (hf : ∀ r, algebraMap O F (f r) = algebraMap R F r) {d : ℕ}
    (B : Geo.Tor.Germ.FB R d Λ) (a : Λ) :
    TB.dAct F B a = ((TB.dLin (B.A.act a)).map f).map (algebraMap O F) := by
  ext i k
  simp [TB.dAct, TB.dLin, Geo.Tor.Germ.FB.actK, hf]

end GlobalTheory.TorsionCharacter
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualNumberValueToJet
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.JetSer
namespace GlobalTheory.JetSer

theorem toJet_one_eq {O κ : Type} [CommRing O] [Fintype κ] (u : MvPowerSeries κ O) :
    toJet 1 u = Ideal.Quotient.mk _ (MvPolynomial.C (constantCoeff u) +
      ∑ q, MvPolynomial.C (coeff (Finsupp.single q 1) u) * MvPolynomial.X q) := by
  classical
  refine (toJet_eq_mk_iff 1 u _).2 fun a ha => ?_
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_C, MvPolynomial.coeff_X]
  by_cases h0 : Finsupp.degree a = 0
  · rw [Finsupp.degree_eq_zero_iff] at h0
    subst h0
    simp [Finsupp.single_eq_zero]
  · have h1 : a ∈ {d : κ →₀ ℕ | Finsupp.degree d = 1} := by
      show Finsupp.degree a = 1
      omega
    rw [← Finsupp.range_single_one] at h1
    obtain ⟨q, rfl⟩ := h1
    rw [if_neg (Finsupp.single_ne_zero.2 one_ne_zero).symm, zero_add, Finset.sum_eq_single q]
    · simp
    · intro b _ hb
      rw [if_neg, mul_zero]
      rwa [Finsupp.single_left_inj one_ne_zero]
    · simp

theorem constantCoeff_dof {R O : Type} [CommRing R] [CommRing O] (f : R →+* O) {d : ℕ}
    (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) :
    constantCoeff (Dof (G.mapF f) e u) =
      ∑ j, e j * coeff (Finsupp.single ((0 : Fin 1), j) 1) u := by
  have h : ∀ i j : Fin d, constantCoeff (ev (n := 1) ![pt O d 0, 0]
      (MvPowerSeries.pderiv (R := O) ((1 : Fin 2), i) (G.mapF f j))) = if j = i then 1 else 0 := by
    intro i j
    rw [← coeff_zero_eq_constantCoeff_apply, ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.coeff_ev_zero_right,
      Finsupp.embDomain_zero, coeff_pderiv, FGLaw.mapF, coeff_map, zero_add, SymbolOne.coeff_law]
    split_ifs <;> simp
  unfold Dof
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, h, constantCoeff_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem dualNumber_value_toJet : ∀ (R O : Type) [CommRing R] [CommRing O] (f : R →+* O) (d : ℕ) (G : FGLaw R d) (e : Fin d → O) (u : PS O 1 d) (S : Type) [CommRing S] [Algebra O S] (ψ : JetR O (Fin 1 × Fin d) 1 →ₐ[O] DualNumber S), (∀ q, ψ (zR 1 q) = TrivSqZeroExt.inr (algebraMap O S (e q.2))) → ψ (toJet 1 u) = TrivSqZeroExt.inl (algebraMap O S (MvPowerSeries.constantCoeff u)) + TrivSqZeroExt.inr (algebraMap O S (MvPowerSeries.constantCoeff (Dof (G.mapF f) e u))) := by
  intro R O _ _ f d G e u S _ _ ψ hψ
  have hC : ∀ c : O, ψ (Ideal.Quotient.mk _ (MvPolynomial.C c)) = TrivSqZeroExt.inl (algebraMap O S c) :=
    fun c => ψ.commutes c
  have hX : ∀ q, ψ (Ideal.Quotient.mk _ (MvPolynomial.X q)) =
      TrivSqZeroExt.inr (algebraMap O S (e q.2)) := hψ
  rw [toJet_one_eq, constantCoeff_dof]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, map_mul, hC, hX, Fintype.sum_prod_type, Fin.sum_univ_one]
  congr 1
  ext
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, mul_comm]
    simp only [Algebra.smul_def]

end GlobalTheory.JetSer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FiniteAugmentedConnectedPartLocalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MonicEqProd
namespace GlobalTheory.MonicSeparableProduct

open Polynomial

theorem monic_eq_prod {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) :
    ∀ (n : ℕ) (f : W[X]), f.Monic → f.natDegree = n →
      ∃ M : Multiset W, f = (M.map (fun r => X - C r)).prod := by
  intro n
  induction n with
  | zero =>
    intro f hf h0
    exact ⟨0, by simpa using (hf.natDegree_eq_zero).1 h0⟩
  | succ n ih =>
    intro f hf hn
    have hinj : Function.Injective (algebraMap W F) := Subtype.val_injective
    have hdeg : f.degree ≠ 0 := by
      rw [degree_eq_natDegree hf.ne_zero, hn]
      exact_mod_cast Nat.succ_ne_zero n
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective (algebraMap W F) hinj f hdeg
    have hint : IsIntegral W x := ⟨f, hf, hx⟩
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
    have hroot : f.IsRoot r := by
      apply hinj
      rw [map_zero, ← hx, ← hr, eval₂_at_apply]
    have hfac := mul_divByMonic_eq_iff_isRoot.2 hroot
    have hq : (f /ₘ (X - C r)).Monic := by
      apply Monic.of_mul_monic_left (monic_X_sub_C r)
      rw [hfac]; exact hf
    have hqd : (f /ₘ (X - C r)).natDegree = n := by
      rw [natDegree_divByMonic f (monic_X_sub_C r), hn, natDegree_X_sub_C]
      simp
    obtain ⟨M, hM⟩ := ih _ hq hqd
    refine ⟨r ::ₘ M, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hM, hfac]

theorem exists_sep {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W)
    (hp : ∀ a : W, ¬IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p})
    (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W)
    (t : A) (ht : aug t = 0) :
    ∃ s b : A, IsUnit (aug s) ∧ s = b * s ^ 2 ∧
      ∀ P : Ideal A, P.IsPrime → algebraMap W A p ∈ P → s ∉ P → t ∈ P := by
  classical
  obtain ⟨f, hf, hft⟩ : IsIntegral W t := Algebra.IsIntegral.isIntegral t
  obtain ⟨M, hM⟩ := monic_eq_prod W _ f hf rfl
  have h0 : (M.map (fun r => t - algebraMap W A r)).prod = 0 := by
    have : aeval t f = 0 := hft
    rw [hM, map_multiset_prod, Multiset.map_map] at this
    simpa using this
  set s : A := ((M.filter (fun r => IsUnit r)).map (fun r => t - algebraMap W A r)).prod with hs
  set g : A := ((M.filter (fun r => ¬ IsUnit r)).map (fun r => t - algebraMap W A r)).prod with hg
  have hsg : s * g = 0 := by
    rw [hs, hg, ← Multiset.prod_add, ← Multiset.map_add (f := _), Multiset.filter_add_not, h0]
  have hcop : IsCoprime s g := by
    rw [hs]
    refine Multiset.prod_induction (fun x => IsCoprime x g) _
      (fun a b ha hb => ha.mul_left hb) isCoprime_one_left ?_
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hru : IsUnit r := (Multiset.mem_filter.1 hr).2
    rw [hg]
    refine Multiset.prod_induction (fun y => IsCoprime (t - algebraMap W A r) y) _
      (fun a b ha hb => ha.mul_right hb) isCoprime_one_right ?_
    intro y hy
    obtain ⟨r', hr', rfl⟩ := Multiset.mem_map.1 hy
    have hru' : ¬ IsUnit r' := (Multiset.mem_filter.1 hr').2
    have hd : IsUnit (r - r') := by
      by_contra hnu
      have h1 : r - r' ∈ IsLocalRing.maximalIdeal W := hnu
      have h2 : r' ∈ IsLocalRing.maximalIdeal W := hru'
      have h3 : r ∈ IsLocalRing.maximalIdeal W := by
        simpa using add_mem h1 h2
      exact h3 hru
    obtain ⟨u, hu⟩ := hd.exists_left_inv
    refine ⟨-algebraMap W A u, algebraMap W A u, ?_⟩
    have := congrArg (algebraMap W A) hu
    rw [map_mul, map_sub, map_one] at this
    linear_combination this
  obtain ⟨b, a, hab⟩ := hcop
  refine ⟨s, b, ?_, ?_, ?_⟩
  · rw [hs, map_multiset_prod]
    refine Multiset.prod_induction IsUnit _ (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro x hx
    rw [Multiset.map_map] at hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
    have hru : IsUnit r := (Multiset.mem_filter.1 hr).2
    have : aug (t - algebraMap W A r) = -r := by
      rw [map_sub, ht, AlgHom.commutes]; simp
    show IsUnit (aug (t - algebraMap W A r))
    rw [this]; exact hru.neg
  · linear_combination (-s) * hab + a * hsg
  · intro P hP hpP hsP
    have hgP : g ∈ P := by
      have : s * g ∈ P := by rw [hsg]; exact P.zero_mem
      exact (hP.mem_or_mem this).resolve_left hsP
    rw [hg] at hgP
    obtain ⟨y, hy, hyP⟩ := (hP.multiset_prod_mem_iff_exists_mem _).1 hgP
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨n, hn⟩ := hp r (Multiset.mem_filter.1 hr).2
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hn
    have : algebraMap W A r ^ n ∈ P := by
      rw [← map_pow, ← hc, map_mul]
      exact P.mul_mem_left _ hpP
    have h2 := hP.mem_of_pow_mem n this
    simpa using add_mem hyP h2

theorem main : ∀ (F : Type) [inst : Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : ↥W), (∀ (a : ↥W), ¬IsUnit a → ∃ (n : ℕ), a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [inst_2 : CommRing A] [inst_3 : Algebra (↥W) A] [Module.Finite (↥W) A] (aug : A →ₐ[↥W] ↥W), ∃ (s : A), Function.Surjective (⇑(Algebra.algebraMap A (Localization.Away s)) : A → Localization.Away s) ∧ (∃ (m : ℕ), Ideal.map (Algebra.algebraMap A (Localization.Away s)) (RingHom.ker aug) ^ m ≤ Ideal.span {(Algebra.algebraMap (↥W) (Localization.Away s) : ↥W → Localization.Away s) p}) ∧ ∀ (R : Type) [inst_5 : CommRing R] [inst_6 : Algebra (↥W) R] (w : A →ₐ[↥W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent ((w : A → R) t)) → IsUnit ((w : A → R) s) := by
  intro F _ _ W p hp A _ _ _ aug
  classical
  obtain ⟨S, hS⟩ : (⊤ : Submodule W A).FG := Module.Finite.fg_top
  let τ : A → A := fun a => a - algebraMap W A (aug a)
  have hτ : ∀ a, aug (τ a) = 0 := by
    intro a
    simp only [τ]
    rw [map_sub, AlgHom.commutes]; simp
  choose σ β h1 h2 h3 using fun a => exists_sep W p hp A aug (τ a) (hτ a)
  have hker : RingHom.ker aug = Ideal.span ((S.image τ : Finset A) : Set A) := by
    apply le_antisymm
    · intro x hx
      have key : ∀ y ∈ Submodule.span W (S : Set A),
          τ y ∈ Ideal.span ((S.image τ : Finset A) : Set A) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          apply Ideal.subset_span
          simp only [Finset.coe_image]
          exact ⟨y, hy, rfl⟩
        | zero => simp [τ]
        | add y z _ _ hy hz =>
          have : τ (y + z) = τ y + τ z := by simp only [τ, map_add (f := _)]; ring
          rw [this]; exact add_mem hy hz
        | smul c y _ hy =>
          have : τ (c • y) = algebraMap W A c * τ y := by
            simp only [τ]
            rw [map_smul, smul_eq_mul, map_mul, Algebra.smul_def]; ring
          rw [this]; exact Ideal.mul_mem_left _ _ hy
      have := key x (by rw [hS]; trivial)
      have hx0 : aug x = 0 := hx
      simpa [τ, hx0] using this
    · rw [Ideal.span_le]
      intro x hx
      simp only [Finset.coe_image] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact hτ y
  set s : A := ∏ a ∈ S, σ a with hs
  have hsu : IsUnit (aug s) := by
    rw [hs, map_prod]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun a _ => h1 a)
  have hsb : s = (∏ a ∈ S, β a) * s ^ 2 := by
    rw [hs, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun a _ => h2 a)
  set b : A := ∏ a ∈ S, β a with hb
  have hLu : IsUnit (algebraMap A (Localization.Away s) s) := IsLocalization.Away.algebraMap_isUnit s
  refine ⟨s, ?_, ?_, ?_⟩
  · have hinv : algebraMap A (Localization.Away s) s * algebraMap A (Localization.Away s) b = 1 := by
      apply hLu.mul_left_cancel
      have := congrArg (algebraMap A (Localization.Away s)) hsb
      rw [map_mul, map_pow] at this
      linear_combination -this
    intro z
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s z
    refine ⟨a * b ^ n, ?_⟩
    rw [map_mul, map_pow, ← ha, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
  · apply Ideal.exists_pow_le_of_le_radical_of_fg
    · rw [hker, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [Finset.coe_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rw [Ideal.radical_eq_sInf]
      refine Ideal.mem_sInf.2 ?_
      rintro P ⟨hle, hP⟩
      refine h3 y (P.comap (algebraMap A (Localization.Away s))) inferInstance ?_ ?_
      · rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
        exact hle (Ideal.mem_span_singleton_self _)
      · intro hmem
        have hsm : s ∈ P.comap (algebraMap A (Localization.Away s)) :=
          Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem σ hy) hmem
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hsm hLu)
    · apply Ideal.FG.map
      rw [hker]
      exact ⟨_, rfl⟩
  · intro R _ _ w hw
    have hn := hw (τ s) (hτ s)
    have hu : IsUnit (algebraMap W R (aug s)) := hsu.map _
    have : w s = algebraMap W R (aug s) + w (τ s) := by
      simp only [τ]
      rw [map_sub, AlgHom.commutes]; ring
    rw [this]
    exact hn.isUnit_add_left_of_commute hu (Commute.all _ _)

end GlobalTheory.MonicSeparableProduct
end

open Polynomial

namespace GlobalTheory

theorem finite_augmented_connected_part_localisation :
    ∀ (F : Type) [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W), (∀ a : W, ¬ IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p}) → ∀ (A : Type) [CommRing A] [Algebra W A] [Module.Finite W A] (aug : A →ₐ[W] W), ∃ s : A, Function.Surjective (algebraMap A (Localization.Away s)) ∧ (∃ m : ℕ, ((RingHom.ker aug).map (algebraMap A (Localization.Away s))) ^ m ≤ Ideal.span {algebraMap W (Localization.Away s) p}) ∧ ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) → IsUnit (w s) := by
  first
  | exact @_root_.GlobalTheory.MonicSeparableProduct.main
  | exact _root_.GlobalTheory.MonicSeparableProduct.main
  | (apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MonicSeparableProduct.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MonicSeparableProduct.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MonicSeparableProduct.main ..)

end GlobalTheory
end

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SeriesCharacter

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FamGerm GlobalTheory.KernelNoTorsion GlobalTheory.TorsionCharacter
open GlobalTheory.SeriesValue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev Dof)

theorem exists_character_of_rel {N M F : Type} [CommGroup N] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : N →* M) (hΦ : Function.Injective Φ) (Rel : N → F → Prop) (h1 : Rel 1 1)
    (hmul : ∀ g g' c c', Rel g c → Rel g' c' → Rel (g * g') (c * c'))
    (huniq : ∀ g c c', Rel g c → Rel g c' → c = c') {p : ℕ} (hp : p ≠ 0) :
    ∃ κ : M →* Fˣ, ∀ g c, g ^ p = 1 → Rel g c → (κ (Φ g) : F) = c := by
  have hpow : ∀ g c (n : ℕ), Rel g c → Rel (g ^ n) (c ^ n) := fun g c n h => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h
  let H : Subgroup N :=
    { carrier := {g | g ^ p = 1 ∧ ∃ c, Rel g c}
      mul_mem' := by
        rintro a b ⟨ha, c, hc⟩ ⟨hb, c', hc'⟩
        exact ⟨by rw [mul_pow, ha, hb, _root_.mul_one], _, hmul _ _ _ _ hc hc'⟩
      one_mem' := ⟨one_pow _, 1, h1⟩
      inv_mem' := by
        rintro a ⟨ha, c, hc⟩
        have : a⁻¹ = a ^ (p - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hp), ha]
        exact ⟨by rw [inv_pow, ha, inv_one], _, this ▸ hpow _ _ _ hc⟩ }
  choose c hc using fun h : H => h.2.2
  have hc0 : ∀ h, c h ≠ 0 := fun h h0 => by
    have := hpow _ _ p (hc h)
    rw [h.2.1, h0, zero_pow hp] at this
    exact zero_ne_one (huniq _ _ _ this h1)
  let χ : H →* Fˣ := MonoidHom.mk' (fun h => Units.mk0 (c h) (hc0 h)) fun a b =>
    Units.ext (huniq _ _ _ (hc (a * b)) (hmul _ _ _ _ (hc a) (hc b)))
  obtain ⟨κ, hκ⟩ := exists_extend_character (Φ.comp H.subtype) (hΦ.comp Subtype.val_injective) χ
  refine ⟨κ, fun g k hg hk => ?_⟩
  rw [show κ (Φ g) = χ ⟨g, hg, k, hk⟩ from hκ ⟨g, hg, k, hk⟩]
  exact huniq _ _ _ (hc ⟨g, hg, k, hk⟩) hk

theorem ptMap_injective {O A R : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [Algebra O R]
    {φ ψ : A →ₐ[O] R} (h : ptMap φ = ptMap ψ) : φ = ψ := by
  have := congrArg CommRingCat.Hom.hom (Spec.map_injective (congrArg (·.left) h))
  exact AlgHom.ext fun a => RingHom.congr_fun this a

theorem fnVal_spec_top {A R : Type} [CommRing A] [CommRing R] (θ : A →+* R) (k : A) :
    JetSer.fnVal (Spec.map (CommRingCat.ofHom θ)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom k) = θ k := by
  have h := (ChartBaseChange.fnVal_spec θ (𝟙 _) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom k) le_rfl).2
  rw [Category.comp_id] at h
  rw [h, JetSer.fnVal, dite_eq_left (show ⊤ ≤ (𝟙 (Spec (CommRingCat.of A))) ⁻¹ᵁ ⊤ from le_rfl)]
  congr 1
  have e : (𝟙 (Spec (CommRingCat.of A)) : _ ⟶ _).appLE ⊤ ⊤ le_rfl = 𝟙 _ :=
    (Scheme.Hom.app_eq_appLE (𝟙 (Spec (CommRingCat.of A))) (U := ⊤)).symm.trans (Scheme.Hom.id_app _)
  erw [e]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply k

theorem exists_connected_part {F : Type} [Field F] [IsAlgClosed F] (W : ValuationSubring F) (p : W)
    (hp : ∀ a : W, ¬ IsUnit a → ∃ n : ℕ, a ^ n ∈ Ideal.span {p}) (Gt : Over (Spec (CommRingCat.of W))) [GrpObj Gt]
    [IsCommMonObj Gt] (N : ℕ) [IsFinite (torsion Gt N).hom] [Flat (torsion Gt N).hom]
    (hred : IsReduced (specO W F ⊗ torsion Gt N).left) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra W A) (X : specO W A ⟶ torsion Gt N) (aug : A →ₐ[W] W) (I : Ideal A)
      (m : ℕ), Module.Finite W A ∧ Module.Free W A ∧ IsReduced (specO W F ⊗ specO W A).left ∧
      ptMap aug ≫ X ≫ torsion.ι Gt N = 1 ∧
      Ideal.Quotient.mk I = (algebraMap W (A ⧸ I)).comp aug.toRingHom ∧ I ^ m ≤ Ideal.span {algebraMap W A p} ∧
      ∀ (R : Type) [CommRing R] [Algebra W R] (w : specO W (DualNumber R) ⟶ torsion Gt N),
        ptMap (TrivSqZeroExt.fstHom W R R) ≫ w ≫ torsion.ι Gt N = 1 → ∃ ψ : A →ₐ[W] DualNumber R, w = ptMap ψ ≫ X := by
  obtain ⟨A, _, _, hfin, hfree, ⟨i⟩⟩ := exists_finite_free (torsion Gt N)
  obtain ⟨aug, haug⟩ := exists_ptMap (torsionLift (1 : specO W W ⟶ Gt) (one_pow N) ≫ i.inv)
  have haug' : ptMap aug ≫ i.hom ≫ torsion.ι Gt N = 1 := by
    rw [← haug, Category.assoc, Iso.inv_hom_id_assoc, torsionLift_ι]
  obtain ⟨s, hs, ⟨m, hm⟩, hu⟩ := GlobalTheory.finite_augmented_connected_part_localisation F W p hp A aug
  let loc := IsScalarTower.toAlgHom W A (Localization.Away s)
  have lift : ∀ (R : Type) [CommRing R] [Algebra W R] (w : A →ₐ[W] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) →
      ∃ w' : Localization.Away s →ₐ[W] R, w'.comp loc = w := fun R _ _ w hw =>
    ⟨IsLocalization.Away.liftAlgHom s (hu R w hw), AlgHom.ext fun a => IsLocalization.Away.lift_eq s (hu R w hw) a⟩
  obtain ⟨aug', h'⟩ := lift W aug fun t ht => by rw [show aug t = 0 from ht]; exact IsNilpotent.zero
  have : Module.Finite W (Localization.Away s) := Module.Finite.of_surjective loc.toLinearMap hs
  have : Module.Flat A (Localization.Away s) := IsLocalization.flat _ (Submonoid.powers s)
  have : Module.Flat W (Localization.Away s) := Module.Flat.trans W A _
  refine ⟨Localization.Away s, inferInstance, inferInstance, ptMap loc ≫ i.hom, aug', _, m, inferInstance,
    Module.free_of_flat_of_isLocalRing, ?_, ?_, ?_, hm, fun R _ _ w hw => ?_⟩
  · have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i.hom))
    have : IsOpenImmersion (ptMap loc).left :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))))
    have : IsOpenImmersion (ptMap loc ≫ i.hom).left := by rw [Over.comp_left]; infer_instance
    have : IsOpenImmersion (specO W F ◁ (ptMap loc ≫ i.hom)).left := by
      rw [Over.whiskerLeft_left]
      exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance this (by simp) (Over.w _).symm
    exact isReduced_of_isOpenImmersion (specO W F ◁ (ptMap loc ≫ i.hom)).left
  · rw [Category.assoc, ← Category.assoc (ptMap aug'), TangentPow.ptMap_comp_ptMap, h', haug']
  · refine RingHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := hs b
    show _ = Ideal.Quotient.mk _ (algebraMap W _ (aug'.comp loc a))
    rw [h', Ideal.Quotient.eq, IsScalarTower.algebraMap_apply W A, ← map_sub]
    refine Ideal.mem_map_of_mem _ ?_
    show aug _ = 0
    rw [map_sub, AlgHom.commutes]
    exact sub_self _
  · obtain ⟨ψ, hψ⟩ := exists_ptMap (w ≫ i.inv)
    have e : (TrivSqZeroExt.fstHom W R R).comp ψ = (Algebra.ofId W R).comp aug := by
      apply ptMap_injective
      rw [← cancel_mono i.hom]
      apply torsion_hom_ext
      rw [← TangentPow.ptMap_comp_ptMap, ← TangentPow.ptMap_comp_ptMap, ← hψ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hw, haug', MonObj.comp_one]
    obtain ⟨ψ', hψ'⟩ := lift _ ψ fun t ht => by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst, show (ψ t).fst = 0 from
        (AlgHom.congr_fun e t).trans (by rw [AlgHom.comp_apply, show aug t = 0 from ht, map_zero])]
      exact IsNilpotent.zero
    refine ⟨ψ', ?_⟩
    rw [← Category.assoc, TangentPow.ptMap_comp_ptMap, hψ', ← hψ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem hasVal_of_ringHom {V O A : Type} [CommRing V] [CommRing O] [Algebra V O] [CommRing A] [Algebra O A]
    {G : Over (Spec (CommRingCat.of V))} {d m : ℕ} (x : JetSer.Fam G (Fin d)) (u : PS O 1 d)
    (g : specV (algebraMap V O) A ⟶ G) (φ : Chart.JetR V (Fin d) m →+* A)
    (hg : g.left = Spec.map (CommRingCat.ofHom φ) ≫ (x m).left) (ψ : Chart.JetR O (Fin 1 × Fin d) m →ₐ[O] A)
    (hψ : ∀ q, ψ (Chart.zR m q) = φ (Chart.zR m q.2)) : HasVal x u g.left (ψ (JetSer.toJet m u)) := by
  refine ⟨m, fun j => φ (Chart.zR m j), ψ, hψ, ?_, rfl⟩
  have w := Over.w g
  rw [hg, Category.assoc, Over.w (x m)] at w
  change Spec.map _ ≫ Spec.map _ = Spec.map _ at w
  rw [← Spec.map_comp] at w
  have w' := congrArg CommRingCat.Hom.hom (Spec.map_injective w)
  have : φ = ψ.toRingHom.comp (jetIn V d O m).toRingHom := by
    refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) fun j => ?_)
    · refine (RingHom.congr_fun w' r).trans ?_
      show _ = ψ (jetIn V d O m (algebraMap V _ r))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply V O, AlgHom.commutes]
      rfl
    · show _ = ψ (jetIn V d O m (Chart.zR m j))
      rw [jetIn_zR, hψ]
      rfl
  rw [hg, this]

theorem dualBC_comp_dualScale_zero {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (s : O)
    (hs : algebraMap O R s = 0) :
    (dualBC (Algebra.ofId O R)).comp (dualScale s) =
      (Algebra.ofId O (DualNumber R)).comp (TrivSqZeroExt.fstHom O O O) := by
  apply DualNumber.algHom_ext
  show dualBC _ (TrivSqZeroExt.map _ (TrivSqZeroExt.inr 1)) =
    algebraMap O (DualNumber R) (TrivSqZeroExt.inr 1 : DualNumber O).fst
  rw [TrivSqZeroExt.map_inr, dualBC_inr, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
    _root_.mul_one, hs, TrivSqZeroExt.fst_inr, map_zero, TrivSqZeroExt.inr_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (y : Pt1 E H V F)

theorem charAt_of_series (a a' b b' : 𝓞 E) (p : ℕ) (hp0 : p ≠ 0) (haa : a' * a = (p : 𝓞 E)) (hbb : b * a + b' * a' = 1)
    (hcomp : IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v))
    (hnil : ∀ c : TWO.Ov y.v, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ Ideal.span {(p : TWO.Ov y.v)})
    (Gt : Over (Spec (CommRingCat.of (TWO.Ov y.v)))) [GrpObj Gt] [IsCommMonObj Gt] (ρ : RingAct Gt (𝓞 E))
    (J : ∀ (A : Type) [CommRing A] [Algebra (TWO.Ov y.v) A], Admissible (TWO.fO y.v y.hϖ y.hv) A →
      (specO (TWO.Ov y.v) A ⟶ Gt) → (specV (TWO.fO y.v y.hϖ y.hv) A ⟶ y.t.G))
    (hnat : ∀ (A A' : Type) [CommRing A] [Algebra (TWO.Ov y.v) A] [CommRing A'] [Algebra (TWO.Ov y.v) A']
      (hA : Admissible (TWO.fO y.v y.hϖ y.hv) A) (hA' : Admissible (TWO.fO y.v y.hϖ y.hv) A')
      (φ : A →ₐ[TWO.Ov y.v] A') (x : specO (TWO.Ov y.v) A ⟶ Gt),
      (J A' hA' (ptMap φ ≫ x)).left = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (J A hA x).left)
    (hJ : ∀ (A : Type) [CommRing A] [Algebra (TWO.Ov y.v) A] (hA : Admissible (TWO.fO y.v y.hϖ y.hv) A),
      (∀ x x', J A hA (x * x') = J A hA x * J A hA x') ∧
      (∀ x (a : 𝓞 E), J A hA (x ≫ ρ.act a) = J A hA x ≫ y.t.act.act a))
    [IsFinite (torsion Gt p).hom] [Flat (torsion Gt p).hom]
    (hred : IsReduced (specO (TWO.Ov y.v) F ⊗ torsion Gt p).left)
    (hn : ∃ n : ℕ, ∀ b ∈ maximalIdeal V ^ n, TWO.fO y.v y.hϖ y.hv b ∈ Ideal.span {(p : TWO.Ov y.v)})
    {Λ : Type} (e : Λ → Fin y.d → TWO.Ov y.v) (et : Λ → LieG Gt)
    (hD : Admissible (TWO.fO y.v y.hϖ y.hv) (DualNumber (TWO.Ov y.v)))
    (het : ∀ l, ∃ φ : Chart.JetR V (Fin y.d) 1 →+* DualNumber (TWO.Ov y.v),
      (∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (e l i)) ∧
        (J _ hD (et l).1).left = Spec.map (CommRingCat.ofHom φ) ≫ (y.x 1).left)
    (hfix : ∀ l, ∃ s : TWO.Ov y.v, s ∈ Ideal.span {(p : TWO.Ov y.v)} ∧
      (et l).1 ≫ ρ.act a = ptMap (dualScale s) ≫ (et l).1)
    (L : Germ.FGLaw V y.d) (hL : JetSer.IsLawOf y.x L.F) (u : PS (TWO.Ov y.v) 1 y.d)
    (hu1 : MvPowerSeries.constantCoeff u = 1)
    (hu : ev (n := 2) ![L.mapF (TWO.fO y.v y.hϖ y.hv)] u =
      ev (n := 2) ![Germ.pt _ y.d 0] u * ev (n := 2) ![Germ.pt _ y.d 1] u) :
    y.CharAt a p e fun l => MvPowerSeries.constantCoeff (Dof (L.mapF (TWO.fO y.v y.hϖ y.hv)) (e l) u) := by
  let _ := H.starRing
  let _ : Algebra V (TWO.Ov y.v) := (TWO.fO y.v y.hϖ y.hv).toAlgebra
  obtain ⟨A, _, _, X₀, aug, I, m, hfin, hfree, hAred, haug, hI, hIm, hlift⟩ :=
    exists_connected_part (TWO.Ov y.v) p hnil Gt p hred
  have hA : Admissible (TWO.fO y.v y.hϖ y.hv) A := Or.inl ⟨hfin, hfree⟩
  have hO : Admissible (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v) := Or.inl ⟨inferInstance, inferInstance⟩
  have := ρ.hom (b' * a')
  have := ρ.hom a'
  have := ρ.hom b'
  have := ρ.hom b
  have := y.P.U.gen_hom
  have gpG : IsGrpPullback y.P.A.A y.t.G (jK V) (y.P.U.gen.inv.left ≫ pullback.fst y.t.G.hom (jK V)) := by
    have : IsMonHom y.P.U.gen.symm.hom := by show IsMonHom y.P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso y.P.U.gen.symm).comp (isGrpPullback_pullback y.t.G (jK V))).congr
      (Category.id_comp _) rfl
  let T : Over (Spec (CommRingCat.of V)) := Over.mk ((TFK (R := V) F).hom ≫ jK V)
  let r : T ⟶ specV (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v) :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap (TWO.Ov y.v) F))) (by
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl)
  have hsep := y.t.semi.separated
  have hcomp' : IsAdicComplete (Ideal.span {algebraMap (TWO.Ov y.v) (TWO.Ov y.v) p}) (TWO.Ov y.v) := hcomp
  obtain ⟨κ', hκ'⟩ := exists_character_of_rel (F := F)
    (MonoidHom.mk' (fun w : specV (TWO.fO y.v y.hϖ y.hv) (TWO.Ov y.v) ⟶ y.t.G => r ≫ w)
      fun w w' => MonObj.comp_mul _ _ _)
    (fun w w' h => Over.OverMorphism.ext (TWO.lift_unique y.v y.hϖ y.hv y.t.G.hom _ _
      (Over.w w) (Over.w w') (congrArg (·.left) h)))
    (fun g c => ∃ k : TWO.Ov y.v, LimVal y.x u (p : TWO.Ov y.v) g.left k ∧ c = (k : F))
    ⟨1, limVal_one y.hx hu1, rfl⟩
    (by
      rintro g g' _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
      exact ⟨k * k', LimVal.mul y.hx hL hu hk hk', rfl⟩)
    (by
      rintro g _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
      rw [hk.unique y.hx hk']) hp0
  let X : specO (TWO.Ov y.v) A ⟶ Gt := X₀ ≫ torsion.ι Gt p ≫ ρ.act (b' * a')
  have J1 : ∀ (B : Type) [CommRing B] [Algebra (TWO.Ov y.v) B] (hB), J B hB 1 = 1 := fun B _ _ hB => by
    have := (hJ B hB).1 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.mp this
  have h2 : X ≫ ρ.act a = 1 := by
    simp only [X, Category.assoc]
    rw [← ρ.map_mul, show a * (b' * a') = b' * (p : 𝓞 E) by rw [← haa]; ring, ρ.map_mul, ringAct_natCast,
      ← Category.assoc (torsion.ι _ _), MonObj.comp_pow, Category.comp_id, torsionι_pow, MonObj.one_comp,
      MonObj.comp_one]
  have h3 : J A hA X ^ p = 1 := by
    have h4 : X ^ p = 1 := by
      rw [← Category.comp_id X, ← MonObj.comp_pow, ← ringAct_natCast ρ, ← haa, ρ.map_mul, ← Category.assoc, h2,
        MonObj.one_comp]
    have := map_pow (MonoidHom.mk' (J A hA) (hJ A hA).1) X p
    rw [h4, map_one] at this
    exact this.symm
  have hAc : IsAdicComplete (Ideal.span {algebraMap (TWO.Ov y.v) A p}) A := by
    have := FlatComplete.isAdicComplete_of_finite_flat _ _ hcomp A
    rwa [Ideal.map_span, Set.image_singleton] at this
  obtain ⟨k, hk⟩ := exists_limVal y.hx u (p : TWO.Ov y.v) I hIm (J A hA X) (by
    have e1 : res V aug ≫ J A hA X = res V aug ≫ 1 := by
      rw [MonObj.comp_one, ← J1 _ hO]
      apply Over.OverMorphism.ext
      refine (hnat A _ hA hO aug X).symm.trans ?_
      simp only [X]
      rw [← Category.assoc X₀, ← Category.assoc, haug, MonObj.one_comp]
    have e2 : Spec.map (CommRingCat.ofHom aug.toRingHom) ≫ (J A hA X).left =
      Spec.map (CommRingCat.ofHom aug.toRingHom) ≫ (1 : specV (TWO.fO y.v y.hϖ y.hv) A ⟶ y.t.G).left :=
      congrArg (·.left) e1
    rw [hI, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, e2])
  refine ⟨fun z => κ' (pushHom gpG (TFK (R := V) F) z), specO (TWO.Ov y.v) A, (J A hA X).left,
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom k,
    fun z z' _ _ => by beta_reduce; rw [map_mul, map_mul], ?_, ?_, hAred, ?_, ?_, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hfin)
  · exact (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  · rw [Over.w (J A hA X)]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  · rw [← Over.comp_left, ← Over.comp_left, ← (hJ A hA).2, h2, J1, MonObj.comp_one]
  · intro c z hz
    obtain ⟨φ, rfl⟩ := exists_ptMap c
    obtain ⟨ψ, rfl⟩ := exists_algHom_valuationSubring _ φ
    have e1 : pushHom gpG (TFK (R := V) F) z = r ≫ (res V ψ ≫ J A hA X) := by
      apply Over.OverMorphism.ext
      refine Eq.trans (Category.assoc _ _ _).symm (hz.trans ?_)
      rw [← TangentPow.ptMap_comp_ptMap]
      exact Category.assoc _ _ _
    beta_reduce
    rw [e1]
    refine (fnVal_spec_top _ k).trans (hκ' (res V ψ ≫ J A hA X) _ ?_ ⟨ψ k, hk.map ψ, rfl⟩).symm
    rw [← MonObj.comp_pow]
    exact (congrArg _ h3).trans (MonObj.comp_one _)
  · intro l
    obtain ⟨φ, hφ, hφ'⟩ := het l
    obtain ⟨s, hs, hs'⟩ := hfix l
    let R := TWO.Ov y.v ⧸ Ideal.span {(p : TWO.Ov y.v)}
    have hpR : (p : R) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk _)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    have hR : Admissible (TWO.fO y.v y.hϖ y.hv) (DualNumber R) := Or.inr (hn.imp fun n h b hb => by
      rw [IsScalarTower.algebraMap_apply (TWO.Ov y.v) R (DualNumber R)]
      rw [show algebraMap (TWO.Ov y.v) R (TWO.fO y.v y.hϖ y.hv b) = 0 from
        Ideal.Quotient.eq_zero_iff_mem.2 (h b hb), map_zero])
    let β := dualBC (Algebra.ofId (TWO.Ov y.v) R)
    have htan : ptMap (TrivSqZeroExt.fstHom (TWO.Ov y.v) R R) ≫ ptMap β ≫ (et l).1 = 1 := by
      rw [← Category.assoc, TangentPow.ptMap_comp_ptMap, fst_comp_dualBC, ← TangentPow.ptMap_comp_ptMap,
        Category.assoc, (et l).2]
      exact MonObj.comp_one _
    obtain ⟨w, hw, -⟩ := (TangentPow.pow_eq_scale_and_existsUnique_torsion _ Gt R p (ptMap β ≫ (et l).1) htan).2 hpR
    have e0 : (ptMap β ≫ (et l).1) ≫ ρ.act a = 1 := by
      rw [Category.assoc, hs', ← Category.assoc, TangentPow.ptMap_comp_ptMap,
        dualBC_comp_dualScale_zero s (Ideal.Quotient.eq_zero_iff_mem.2 hs), ← TangentPow.ptMap_comp_ptMap,
        Category.assoc, (et l).2]
      exact MonObj.comp_one _
    have e1 : (ptMap β ≫ (et l).1) ≫ ρ.act (b' * a') = ptMap β ≫ (et l).1 := by
      have h := congrArg (fun c => (ptMap β ≫ (et l).1) ≫ ρ.act c) hbb
      have hadd : ρ.act (b * a + b' * a') = ρ.act (b * a) * ρ.act (b' * a') := ρ.map_add _ _
      rw [hadd, ρ.map_one, Category.comp_id, MonObj.comp_mul, ρ.map_mul b a, ← Category.assoc, e0,
        MonObj.one_comp, _root_.one_mul] at h
      exact h
    obtain ⟨ψ, hψ⟩ := hlift R w (by rw [hw, htan])
    have e3 : ptMap ψ ≫ X = ptMap β ≫ (et l).1 := by
      rw [← e1, ← hw, hψ]
      simp only [X, Category.assoc]
    have e4 := hnat A _ hA hR ψ X
    have e5 : (J _ hR (ptMap β ≫ (et l).1)).left =
        Spec.map (CommRingCat.ofHom (β.toRingHom.comp φ)) ≫ (y.x 1).left := by
      rw [hnat _ _ hD hR, hφ', ← Category.assoc, ← Spec.map_comp]
      rfl
    have e6 : ∀ i, β (φ (Chart.zR 1 i)) = TrivSqZeroExt.inr (algebraMap _ R (e l i)) := fun i => by
      rw [hφ, dualBC_inr]
    rw [e3] at e4
    refine ⟨ptMap ψ, β.toRingHom.comp φ, e6, e4.symm.trans e5, (fnVal_spec_top _ k).trans ?_⟩
    let θ : Chart.JetR (TWO.Ov y.v) (Fin 1 × Fin y.d) 1 →ₐ[TWO.Ov y.v] DualNumber (TWO.Ov y.v) :=
      Chart.jetLift _ (RingHom.ker (Chart.fstD (TWO.Ov y.v))) Chart.kerD_sq
        (fun q => TrivSqZeroExt.inr (e l q.2)) (fun q => TrivSqZeroExt.fst_inr _ (e l q.2))
    have hθ : ∀ q, (β.comp θ) (Chart.zR 1 q) = TrivSqZeroExt.inr (algebraMap _ R (e l q.2)) := fun q => by
      have h0 : θ (Chart.zR 1 q) = TrivSqZeroExt.inr (e l q.2) :=
        Chart.jetLift_zR (RingHom.ker (Chart.fstD (TWO.Ov y.v))) Chart.kerD_sq _
          (fun q : Fin 1 × Fin y.d => TrivSqZeroExt.fst_inr _ (e l q.2)) q
      exact (congrArg β h0).trans (dualBC_inr _)
    have v1 := hasVal_of_ringHom y.x u (J _ hR (ptMap β ≫ (et l).1)) _ e5 (β.comp θ)
      fun q => (hθ q).trans (e6 q.2).symm
    have v2 := hk (DualNumber R) ψ (by
      rw [IsScalarTower.algebraMap_apply (TWO.Ov y.v) R (DualNumber R), map_natCast, hpR, map_zero]
      exact IsNilpotent.zero)
    rw [← e4] at v2
    refine (v2.unique y.hx v1).trans ?_
    rw [GlobalTheory.JetSer.dualNumber_value_toJet V _ (TWO.fO y.v y.hϖ y.hv) y.d L (e l) u R _ hθ, hu1, map_one]
    rfl


open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB in
theorem charAt_of_multiplicative_series : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (p : ℕ), p.Prime → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (Λ : Type) (e : Λ → Fin y.d → TWO.Ov y.v) (α : Λ → TWO.Ov y.v), (∀ l, α l ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ l, (dAct F y.B a).mulVec (fun i => (e l i : F)) = (α l : F) • fun i => (e l i : F)) → ∀ u : PS F 1 y.d, (∀ mo, 0 ≤ y.v (MvPowerSeries.coeff mo u)) → MvPowerSeries.constantCoeff u = 1 → ev (n := 2) ![y.B.FK F] u = ev (n := 2) ![pt F y.d 0] u * ev (n := 2) ![pt F y.d 1] u → ∀ yy : Λ → TWO.Ov y.v, (∀ l, (yy l : F) = MvPowerSeries.constantCoeff (Dof (y.B.FK F) (fun i => (e l i : F)) u)) → y.CharAt a p e yy := by
  intro hL _ hL4 _ p hpp E _ _ _ H V _ _ _ F _ _ _ _ _ _ y
  let _ := H.starRing
  intro hcomp hp a ha ⟨b, b', hbb⟩ Λ e α hα heig u hu hu1 humul yy hyy
  have := y.complete
  have hJ : JetSer.JetAlgSt := JetSer.jetAlg
  have hD : JetSer.DLinSt := (GlobalTheory.JetMap.mapSt_and_dLinSt hJ (JetSer.repSt_of_jetAlgSt hJ)).2
  have hpF : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hp0 : (p : TWO.Ov y.v) ≠ 0 := fun h => hpF (by simpa using congrArg Subtype.val h)
  let f := TWO.fO y.v y.hϖ y.hv
  have hloc : IsLocalHom f := TWO.isLocalHom_fO _ _ _
  have hf : ∀ r, algebraMap (TWO.Ov y.v) F (f r) = algebraMap V F r := fun r =>
    (IsScalarTower.algebraMap_apply V (FractionRing V) F r).symm
  have hϖ0 : f y.ϖ ≠ 0 := fun h => by
    have h1 := hf y.ϖ
    rw [h, map_zero, IsScalarTower.algebraMap_apply V (FractionRing V) F, eq_comm, map_eq_zero,
      FaithfulSMul.algebraMap_eq_zero_iff] at h1
    exact y.hϖ.ne_zero h1
  have hϖu : ¬ IsUnit (f y.ϖ) := fun h => y.hϖ.not_isUnit (hloc.map_nonunit _ h)
  have hmap : (maximalIdeal V).map f = Ideal.span {f y.ϖ} := by
    rw [y.hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  obtain ⟨n₁, hn₁⟩ := exists_pow_mem_span y.v _ _ hϖu hp0
  obtain ⟨n₂, hn₂⟩ := exists_pow_mem_span y.v _ _ hp hϖ0
  have hle₁ : (maximalIdeal V).map f ^ n₁ ≤ Ideal.span {(p : TWO.Ov y.v)} := by
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn₁
  have hle₂ : Ideal.span {(p : TWO.Ov y.v)} ^ n₂ ≤ (maximalIdeal V).map f := by
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn₂
  obtain ⟨Ex, B, hB, hB', Gt, _, _, ρ, J, hGt, hfin, hnat, hJJ⟩ := GlobalTheory.T.torusExtension_over_completeLocal_dvr hL hL4 E H V y.t y.P (TWO.Ov y.v) f hloc
    (isAdicComplete_of_pow_le hle₂ hle₁)
    (fun b hb => by rw [hmap]; exact exists_pow_mem_span y.v _ _ hb hϖ0)
  have hp1 : 1 ≤ p := hpp.one_le
  obtain ⟨hZ₁, hZ₂⟩ := isFinite_flat_torsion_of_isGt _ Ex Gt hGt _ hp1 (hfin _ hp1).1 (hfin _ hp1).2
  have hred := isReduced_torsion_geometric_fibre (TWO.Ov y.v) F Gt p hpF hZ₁
  have hDn : Admissible f (DualNumber (TWO.Ov y.v)) := Or.inl
    ⟨inferInstanceAs (Module.Finite _ (TWO.Ov y.v × TWO.Ov y.v)),
      inferInstanceAs (Module.Free _ (TWO.Ov y.v × TWO.Ov y.v))⟩
  obtain ⟨co, tv, -, -, htv, hact⟩ := exists_lie_coordinates hJ hD f y.t.G y.x y.hx Gt (J _ hDn)
    (hJJ _ hDn).1 (hJJ _ hDn).2.2.1 (fun φ w => hnat _ _ hDn hDn φ w) (fun g hg => by
      refine (hJJ _ hDn).2.2.2.2 (RingHom.ker (Chart.fstD (TWO.Ov y.v))) g
        ⟨1 + 1, by rw [Chart.kerD_sq, Ideal.zero_eq_bot]⟩ ?_
      have e1 : Ideal.Quotient.mk (RingHom.ker (Chart.fstD (TWO.Ov y.v))) =
          ((Ideal.Quotient.mk (RingHom.ker (Chart.fstD (TWO.Ov y.v)))).comp (algebraMap (TWO.Ov y.v) _)).comp
            (Chart.fstD (TWO.Ov y.v)).toRingHom := RingHom.ext fun z => Ideal.Quotient.eq.2 (by
        show Chart.fstD _ (z - algebraMap _ _ (Chart.fstD _ z)) = 0
        rw [map_sub, AlgHom.commutes]
        exact sub_self _)
      rw [e1, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, hg])
  have heig' : ∀ l, (tv (e l)).1 ≫ ρ.act a = ptMap (dualScale (α l)) ≫ (tv (e l)).1 := fun l => by
    have := y.t.act.hom a
    refine hact (y.t.act.act a) (ρ.act a) _ (y.hB.map a) (fun w => (hJJ _ hDn).2.1 w a) _ _ ?_
    funext i
    have h1 := congrFun (heig l) i
    rw [dAct_eq_map f hf] at h1
    apply Subtype.val_injective
    exact (RingHom.map_mulVec (algebraMap (TWO.Ov y.v) F) _ _ i).trans h1
  let u₀ : PS (TWO.Ov y.v) 1 y.d := fun mo => ⟨MvPowerSeries.coeff mo u, hu mo⟩
  have hu₀ : MvPowerSeries.map (algebraMap (TWO.Ov y.v) F) u₀ = u := by
    ext mo
    rfl
  have hFK : (fun i => MvPowerSeries.map (algebraMap (TWO.Ov y.v) F) (y.B.G.mapF f i)) = y.B.FK F := by
    funext i
    ext mo
    exact hf _
  have hyy' : yy = fun l => MvPowerSeries.constantCoeff (Dof (y.B.G.mapF f) (e l) u₀) := by
    funext l
    apply Subtype.val_injective
    rw [hyy, ← hu₀, ← hFK]
    have := congrArg MvPowerSeries.constantCoeff
      (InvDerMap.map_Dof (algebraMap (TWO.Ov y.v) F) (y.B.G.mapF f) (e l) u₀)
    rw [MvPowerSeries.constantCoeff_map] at this
    exact this.symm
  rw [hyy']
  refine charAt_of_series y a (star a) b b' p hpp.ne_zero (by rw [← ha, mul_comm]) hbb hcomp
    (fun c hc => exists_pow_mem_span y.v _ _ hc hp0) Gt ρ J hnat
    (fun A _ _ hA => ⟨(hJJ A hA).1, (hJJ A hA).2.1⟩) hred
    ⟨n₁, fun z hz => hle₁ (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hz)⟩ e (fun l => tv (e l)) hDn
    (fun l => htv (e l)) (fun l => ⟨α l, hα l, heig' l⟩) y.B.G y.hB.law u₀ (Subtype.ext hu1) ?_
  have hinj : Function.Injective (MvPowerSeries.map (σ := Fin 2 × Fin y.d) (algebraMap (TWO.Ov y.v) F)) :=
    fun g g' h => by
      ext mo
      exact congrArg (MvPowerSeries.coeff mo) h
  have hpt : ∀ i : Fin 2, JetSer.IntTrans.mP (algebraMap (TWO.Ov y.v) F) (pt _ y.d i) = pt F y.d i := fun i =>
    funext fun j => MvPowerSeries.map_X _ _
  apply hinj
  rw [map_mul, JetSer.IntTrans.map_ev1 _ (WickVanishing.gp_pt 0), JetSer.IntTrans.map_ev1 _ (WickVanishing.gp_pt 1),
    JetSer.IntTrans.map_ev1 _ (fun i => by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map f _) = 0
      rw [MvPowerSeries.constantCoeff_map, y.B.G.const, map_zero]), hpt, hpt, hu₀, ← humul, ← hFK]
  rfl

end GlobalTheory.SeriesCharacter
