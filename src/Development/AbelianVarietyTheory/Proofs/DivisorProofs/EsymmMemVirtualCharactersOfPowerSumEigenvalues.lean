module

public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEQuotientMapSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.EsymmVirt

theorem esymm_zero' (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

theorem esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + C a * X : ℂ[X])).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul]
    cases n with
    | zero => simp [ih, esymm_zero']
    | succ n => rw [coeff_X_mul, ih, ih, esymm_cons_succ]

theorem esymm_add (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

theorem esymm_eq_of_psum_eq (s t : Multiset ℂ)
    (h : ∀ j : ℕ, 0 < j → (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) (n : ℕ) :
    s.esymm n = t.esymm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [esymm_zero', esymm_zero']
    have h1 := GlobalTheory.multiset_newton_psum s n hn
    have h2 := GlobalTheory.multiset_newton_psum t n hn
    have h3 : ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * s.esymm i * (s.map (· ^ (n - i))).sum
        = ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * t.esymm i * (t.map (· ^ (n - i))).sum := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ioo] at hi
      rw [ih i hi.2, h (n - i) (by omega)]
    have h4 : ((-1) ^ (n + 1) * (n : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hn.ne')
    apply mul_left_cancel₀ h4
    linear_combination h2 - h1 + h n hn + h3

variable {G : Type} [Group G] [Finite G]

theorem one_mem_virt : (fun _ : G => (1 : ℂ)) ∈ Virt ℂ ℂ G := by
  simpa using (virt_mul_comap_conj_ind_linear G).2.2.2.2 1

theorem esymm_add_mem_virt {A B : G → Multiset ℂ}
    (hA : ∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G)
    (hB : ∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) (s : ℕ) :
    (fun g => (A g + B g).esymm s) ∈ Virt ℂ ℂ G := by
  have : (fun g => (A g + B g).esymm s) = ∑ i ∈ Finset.range (s + 1),
      (fun g => (A g).esymm i) * (fun g => (B g).esymm (s - i)) := by
    funext g
    simp [esymm_add, Finset.sum_apply]
  rw [this]
  exact sum_mem fun i _ => (virt_mul_comap_conj_ind_linear G).1 _ (hA _) _ (hB _)

theorem exists_multisets {φ : G → ℂ} (hφ : φ ∈ Virt ℂ ℂ G) :
    ∃ A B : G → Multiset ℂ, (∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G) ∧
      (∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) ∧
      ∀ g j, 0 < j → φ (g ^ j) + ((B g).map (· ^ j)).sum = ((A g).map (· ^ j)).sum := by
  have h0 : ∀ s, (fun _ : G => (0 : Multiset ℂ).esymm s) ∈ Virt ℂ ℂ G := by
    intro s
    cases s with
    | zero => simpa only [esymm_zero'] using one_mem_virt
    | succ s =>
      have : (fun _ : G => (0 : Multiset ℂ).esymm (s + 1)) = 0 := by
        funext g
        simp [Multiset.esymm, Multiset.powersetCard_zero_right]
      rw [this]
      exact zero_mem _
  induction hφ using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨n, ρ, hρ⟩ := (matrixChar_iff_isChar G a).2 ha
    refine ⟨fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots, fun _ => 0,
      fun s => isChar_mem_virt_complex (isChar_esymm_roots_charpoly G n s ρ), h0, fun g j _ => ?_⟩
    rw [hρ, map_pow, Units.val_pow_eq_pow_val, Matrix.trace_eq_sum_roots_charpoly,
      GlobalTheory.CharpolyPow.roots_charpoly_pow]
    simp
  | zero => exact ⟨fun _ => 0, fun _ => 0, h0, h0, fun g j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    obtain ⟨A', B', hA', hB', h'⟩ := hy
    refine ⟨fun g => A g + A' g, fun g => B g + B' g, esymm_add_mem_virt hA hA',
      esymm_add_mem_virt hB hB', fun g j hj => ?_⟩
    simp only [Pi.add_apply, Multiset.map_add (f := _), Multiset.sum_add]
    linear_combination h g j hj + h' g j hj
  | neg x _ hx =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    refine ⟨B, A, hB, hA, fun g j hj => ?_⟩
    simp only [Pi.neg_apply]
    linear_combination - h g j hj

theorem esymm_mem_virt : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ),
    φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) →
    ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  intro G _ _ φ x hφ hx s
  obtain ⟨A, B, hA, hB, h⟩ := exists_multisets hφ
  have he : ∀ g n, (x g + B g).esymm n = (A g).esymm n := fun g n =>
    esymm_eq_of_psum_eq _ _ (fun j hj => by
      rw [Multiset.map_add (f := _), Multiset.sum_add, ← hx g j hj, h g j hj]) n
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    have : (fun g => (x g).esymm s) = (fun g => (A g).esymm s) - ∑ i ∈ Finset.range s,
        (fun g => (x g).esymm i) * (fun g => (B g).esymm (s - i)) := by
      funext g
      have := he g s
      rw [esymm_add, Finset.sum_range_succ, Nat.sub_self, esymm_zero', mul_one] at this
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply]
      linear_combination this
    rw [this]
    exact sub_mem (hA s) (sum_mem fun i hi =>
      (virt_mul_comap_conj_ind_linear G).1 _ (ih i (Finset.mem_range.1 hi)) _ (hB _))

end GlobalTheory.EsymmVirt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvaluesStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.esymm_mem_virtualCharacters_of_powerSum_eigenvalues : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ), φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) → ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  first | exact @GlobalTheory.EsymmVirt.esymm_mem_virt | exact GlobalTheory.EsymmVirt.esymm_mem_virt | (intros; apply GlobalTheory.EsymmVirt.esymm_mem_virt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChart
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChart
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecGlue.CombEx

theorem chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hV (isAffineOpen_top (Sp S)) hx.ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  have e : CommRingCat.ofHom (chartHom V x hx) = x.appLE V ⊤ hx.ge ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom := rfl
  show Spec.map (CommRingCat.ofHom (chartHom V x hx)) ≫ hV.fromSpec = x
  rw [e, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem top_of_comp {A B Y : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ Y) (V : Y.Opens) (h : g ⁻¹ᵁ V = ⊤) :
    (f ≫ g) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun x _ => h.ge (show f x ∈ (⊤ : B.Opens) from trivial)

theorem fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ :=
  top_le_iff.1 fun _ _ => hV.range_fromSpec.subset ⟨_, rfl⟩

theorem chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by
  subst e; rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map (CommRingCat.ofHom (g.comp f)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]; rfl

theorem chartHom_fromSpec {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) (hc : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap χ ≫ hV.fromSpec) hc = χ := by
  have e := chart_rebuild hV (spMap χ ≫ hV.fromSpec) hc
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

theorem chartHom_spMap_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S S' : Type} [CommRing S]
    [CommRing S'] (g : S →+* S') (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ x) ⁻¹ᵁ V = ⊤) :
    chartHom V (spMap g ≫ x) h' = g.comp (chartHom V x hx) := by
  have e : spMap (chartHom V (spMap g ≫ x) h') ≫ hV.fromSpec =
      spMap (g.comp (chartHom V x hx)) ≫ hV.fromSpec := by
    rw [chart_rebuild, spMap_comp', Category.assoc, chart_rebuild]
  rw [cancel_mono] at e
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)

end GlobalTheory.SecGlue.CombEx

namespace GlobalTheory.SecGlue.CombEx

theorem mul_eq_zero_of_sq {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {s t : S} (hs : q s = 0) (ht : q t = 0) : s * t = 0 := by
  have h : s * t ∈ RingHom.ker q ^ 2 := by
    rw [sq]; exact Ideal.mul_mem_mul (RingHom.mem_ker.2 hs) (RingHom.mem_ker.2 ht)
  rw [hsq] at h
  exact (Submodule.mem_bot S).1 h

def combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T) (hsq : RingHom.ker q ^ 2 = ⊥)
    {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S) (hq : ∀ i, q.comp (ψ i) = q.comp φ) :
    A →+* S where
  toFun x := φ x + ∑ i, a i * (ψ i x - φ x)
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [map_add (f := _), mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  map_mul' x y := by
    have hd : ∀ i z, q (ψ i z - φ z) = 0 := fun i z => by
      rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
    have hD : ∀ z, q (∑ i, a i * (ψ i z - φ z)) = 0 := fun z => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, hd, mul_zero, Finset.sum_const_zero]
    have e1 : ∀ i, ψ i (x * y) - φ (x * y) = φ x * (ψ i y - φ y) + (ψ i x - φ x) * φ y := fun i => by
      have := mul_eq_zero_of_sq q hsq (hd i x) (hd i y)
      rw [map_mul, map_mul]; linear_combination this
    have e2 := mul_eq_zero_of_sq q hsq (hD x) (hD y)
    have s : ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
        φ x * ∑ i, a i * (ψ i y - φ y) + φ y * ∑ i, a i * (ψ i x - φ x) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [e1 i]; ring
    show φ (x * y) + ∑ i, a i * (ψ i (x * y) - φ (x * y)) =
      (φ x + ∑ i, a i * (ψ i x - φ x)) * (φ y + ∑ i, a i * (ψ i y - φ y))
    linear_combination s + map_mul φ x y - e2

theorem combHom_apply {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (x : A) :
    combHom q hsq φ ψ a hq x = φ x + ∑ i, a i * (ψ i x - φ x) := rfl

theorem comp_combHom {A S T : Type} [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) : q.comp (combHom q hsq φ ψ a hq) = q.comp φ := by
  ext x
  have hd : ∀ i, q (ψ i x - φ x) = 0 := fun i => by
    rw [map_sub, ← RingHom.comp_apply, hq i, RingHom.comp_apply, sub_self]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [RingHom.comp_apply, combHom_apply, map_add (f := _), map_sum, map_mul, hd, mul_zero,
    Finset.sum_const_zero, add_zero]

theorem combHom_comp_eq {R A S T : Type} [CommRing R] [CommRing A] [CommRing S] [CommRing T] (q : S →+* T)
    (hsq : RingHom.ker q ^ 2 = ⊥) {ι : Type} [Fintype ι] (φ : A →+* S) (ψ : ι → (A →+* S)) (a : ι → S)
    (hq : ∀ i, q.comp (ψ i) = q.comp φ) (θ : R →+* A) (hθ : ∀ i, (ψ i).comp θ = φ.comp θ) :
    (combHom q hsq φ ψ a hq).comp θ = φ.comp θ := by
  ext r
  have h : ∀ i, ψ i (θ r) = φ (θ r) := fun i => RingHom.congr_fun (hθ i) r
  simp only [RingHom.comp_apply, combHom_apply, h, sub_self, mul_zero, Finset.sum_const_zero, add_zero]

theorem exists_comb : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  intro Y V hV S T _ _ q hqs hsq ι _ u w a hu hw
  have hwV : ∀ i, w i ⁻¹ᵁ V = ⊤ := fun i => (GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero S T q hqs hsq Y (w i) u (hw i) V).trans hu
  have hq : ∀ i, q.comp (chartHom V (w i) (hwV i)) = q.comp (chartHom V u hu) := fun i => by
    rw [← chartHom_spMap_comp hV q (w i) (hwV i) (top_of_comp _ _ V (hwV i)),
      ← chartHom_spMap_comp hV q u hu (top_of_comp _ _ V hu)]
    exact chartHom_congr V (hw i) _ _
  let χ := combHom q hsq (chartHom V u hu) (fun i => chartHom V (w i) (hwV i)) a hq
  have hc := fromSpec_comp_top hV χ
  refine ⟨spMap χ ≫ hV.fromSpec, ⟨hu, hc, hwV, fun x => ?_⟩, ?_, ?_⟩
  · rw [chartHom_fromSpec hV χ hc]; rfl
  · calc spMap q ≫ spMap χ ≫ hV.fromSpec = spMap (q.comp χ) ≫ hV.fromSpec := by
          rw [spMap_comp', Category.assoc]
      _ = spMap (q.comp (chartHom V u hu)) ≫ hV.fromSpec := by rw [comp_combHom]
      _ = spMap q ≫ u := by rw [spMap_comp', Category.assoc, chart_rebuild]
  · intro R' _ p hp
    let θ : CommRingCat.of R' ⟶ Γ(Y, V) := Spec.preimage (hV.fromSpec ≫ p)
    have key : ∀ (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤), x ≫ p = spMap ((chartHom V x hx).comp θ.hom) := by
      intro x hx
      calc x ≫ p = spMap (chartHom V x hx) ≫ hV.fromSpec ≫ p := by rw [← Category.assoc, chart_rebuild]
        _ = spMap (chartHom V x hx) ≫ Spec.map θ := by rw [Spec.map_preimage]
        _ = spMap ((chartHom V x hx).comp θ.hom) := by
          show _ = Spec.map (CommRingCat.ofHom _)
          rw [show CommRingCat.ofHom ((chartHom V x hx).comp θ.hom) = θ ≫ CommRingCat.ofHom (chartHom V x hx)
            from rfl, Spec.map_comp]
    have hθ : ∀ i, (chartHom V (w i) (hwV i)).comp θ.hom = (chartHom V u hu).comp θ.hom := fun i => by
      have e := (key (w i) (hwV i)).symm.trans ((hp i).trans (key u hu))
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    rw [key _ hc, key u hu, chartHom_fromSpec hV χ hc]
    exact congrArg spMap (combHom_comp_eq q hsq _ _ a hq θ.hom hθ)

end GlobalTheory.SecGlue.CombEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineCombinationSquareZeroLiftsChartStatement
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineCombination_squareZero_lifts_chart : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by
  first | exact @GlobalTheory.SecGlue.CombEx.exists_comb | exact GlobalTheory.SecGlue.CombEx.exists_comb | (intros; apply GlobalTheory.SecGlue.CombEx.exists_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionMatrixGramOperatorNormLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionMatrixGramOperatorNormLe
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

theorem gnorm_one_eq (v : Fin g → ℂ) : gnorm 1 v = √(∑ a, ‖v a‖ ^ 2) := by
  rw [gnorm, form_eq_sum]
  congr 1
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ofReal_re]

theorem opNorm_one_le_of_entry (M : Matrix (Fin g) (Fin g) ℂ) {E : ℝ} (hE : 0 ≤ E)
    (h : ∀ j k, ‖M j k‖ ≤ E) : opNorm 1 1 M ≤ g * E := by
  refine opNorm_le_of_bound (by positivity) fun v => ?_
  rw [gnorm_one_eq, gnorm_one_eq]
  set S := ∑ a, ‖v a‖ ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrw : (g : ℝ) * E * √S = √(((g : ℝ) * E) ^ 2 * S) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  rw [hrw]
  apply Real.sqrt_le_sqrt
  have hrow : ∀ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ E ^ 2 * (g * S) := fun j => by
    have h1 : ‖(M *ᵥ v) j‖ ≤ E * ∑ k, ‖v k‖ := by
      rw [Finset.mul_sum]
      simp only [mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (h j k) (norm_nonneg _)
    have h2 : (∑ k, ‖v k‖) ^ 2 ≤ g * S := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => ‖v k‖)
      simpa [hS] using this
    calc ‖(M *ᵥ v) j‖ ^ 2 ≤ (E * ∑ k, ‖v k‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = E ^ 2 * (∑ k, ‖v k‖) ^ 2 := by ring
      _ ≤ E ^ 2 * (g * S) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ j, ‖(M *ᵥ v) j‖ ^ 2 ≤ ∑ _j : Fin g, E ^ 2 * (g * S) := Finset.sum_le_sum fun j _ => hrow j
    _ = ((g : ℝ) * E) ^ 2 * S := by simp; ring

theorem inv_entry_le (Y : Matrix (Fin g) (Fin g) ℝ) {c : ℝ} (hc : 0 < c)
    (hY : ∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) : IsUnit Y.det ∧ ∀ j k, |Y⁻¹ j k| ≤ 1 / c := by
  have hdet : IsUnit Y.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨x, hx, hx0⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    have h1 := hY x
    rw [hx0, dotProduct_zero] at h1
    have h2 : x ⬝ᵥ x ≤ 0 := by nlinarith [show 0 ≤ x ⬝ᵥ x from Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)]
    apply hx
    funext i
    have h3 : ∀ i ∈ Finset.univ, 0 ≤ x i * x i := fun i _ => mul_self_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg h3).1 (le_antisymm h2 (Finset.sum_nonneg h3)) i (Finset.mem_univ _)
    simpa using mul_self_eq_zero.1 this
  refine ⟨hdet, fun j k => ?_⟩
  set u := Y⁻¹ *ᵥ Pi.single k 1 with hu
  have hYu : Y *ᵥ u = Pi.single k 1 := by
    rw [hu, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  have hentry : Y⁻¹ j k = u j := by
    rw [hu, mulVec_single_one]; rfl
  set N := u ⬝ᵥ u with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  have hcomp : ∀ i, u i ^ 2 ≤ N := fun i => by
    rw [hN, dotProduct, sq]
    exact Finset.single_le_sum (f := fun i => u i * u i) (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ i)
  have h1 : c * N ≤ u k := by
    have := hY u
    rwa [hYu, dotProduct_single, mul_one] at this
  have huk : 0 ≤ u k := le_trans (mul_nonneg hc.le hN0) h1
  have h2 : c ^ 2 * N ^ 2 ≤ N := by
    calc c ^ 2 * N ^ 2 = (c * N) ^ 2 := by ring
      _ ≤ u k ^ 2 := pow_le_pow_left₀ (mul_nonneg hc.le hN0) h1 2
      _ ≤ N := hcomp k
  have h3 : c ^ 2 * N ≤ 1 := by
    rcases hN0.eq_or_lt with h | h
    · rw [← h]; simp
    · nlinarith
  have h4 : (c * u j) ^ 2 ≤ 1 := by
    calc (c * u j) ^ 2 = c ^ 2 * u j ^ 2 := by ring
      _ ≤ c ^ 2 * N := mul_le_mul_of_nonneg_left (hcomp j) (sq_nonneg c)
      _ ≤ 1 := h3
  rw [hentry, le_div_iff₀ hc, mul_comm]
  have := (sq_le_one_iff_abs_le_one _).1 h4
  rwa [abs_mul, abs_of_pos hc] at this

end GlobalTheory.ConnPointwise

namespace GlobalTheory.ConnPointwise

variable {g : ℕ}

theorem entry_le_of_mulVec (P : Matrix (Fin g) (Fin g) ℝ) {W : ℝ} (hW : 0 ≤ W)
    (h : ∀ x, ‖P *ᵥ x‖ ≤ W * ‖x‖) (j k : Fin g) : |P j k| ≤ W := by
  have h1 := h (Pi.single k 1)
  have hs : ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ ≤ 1 :=
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
      by_cases hi : i = k
      · subst hi; simp
      · simp [Pi.single_apply, hi]
  rw [mulVec_single_one] at h1
  calc |P j k| = ‖Pᵀ k j‖ := by simp [Real.norm_eq_abs]
    _ ≤ ‖Pᵀ k‖ := norm_le_pi_norm _ j
    _ ≤ W * ‖(Pi.single k (1 : ℝ) : Fin g → ℝ)‖ := h1
    _ ≤ W := mul_le_of_le_one_right hW hs

end GlobalTheory.ConnPointwise

namespace GlobalTheory

open GlobalTheory.ConnPointwise

theorem connMatrix_opNorm_le : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by
  intro g a Y Bs Dm s t c K W hc hK hW hY ht hB hD
  obtain ⟨hdet, hinv⟩ := inv_entry_le Y hc hY
  have hmapinv : (Y.map Complex.ofReal)⁻¹ = (Y⁻¹).map Complex.ofReal := by
    apply inv_eq_left_inv
    show (Y⁻¹).map Complex.ofRealHom * Y.map Complex.ofRealHom = 1
    rw [← Matrix.map_mul, nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBe : ∀ i j k, |(Y⁻¹ * Bs i) j k| ≤ W / t i := fun i j k => by
    have := entry_le_of_mulVec _ hW (hB i) j k
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (ht i)] at this
    rw [le_div_iff₀ (ht i), mul_comm]; exact this
  have hE0 : 0 ≤ (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := by
    have : 0 ≤ ∑ i, ‖s i‖ / t i := Finset.sum_nonneg fun i _ => div_nonneg (norm_nonneg _) (ht i).le
    positivity
  refine opNorm_one_le_of_entry _ hE0 fun j k => ?_
  rw [hmapinv]
  have hexp : ((Y⁻¹).map Complex.ofReal * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) j k
      = (1 / (2 * Complex.I)) * (∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)) := by
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.sum_apply, map_apply, smul_eq_mul, ofReal_sum,
      ofReal_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by ring
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  rw [hexp, norm_mul]
  have hhalf : ‖(1 / (2 * Complex.I) : ℂ)‖ ≤ 1 := by simp; norm_num
  have hA : ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ g * K / c := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ l, ‖((Y⁻¹ j l : ℝ) : ℂ) * Dm l k‖ ≤ ∑ _l : Fin g, 1 / c * K :=
          Finset.sum_le_sum fun l _ => by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul (hinv j l) (hD l k) (norm_nonneg _) (by positivity)
      _ = g * K / c := by simp; ring
  have hBs : ‖∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖ ≤ W * ∑ i, ‖s i‖ / t i := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖s i‖ * |(Y⁻¹ * Bs i) j k| ≤ ‖s i‖ * (W / t i) :=
          mul_le_mul_of_nonneg_left (hBe i j k) (norm_nonneg _)
      _ = W * (‖s i‖ / t i) := by ring
  calc ‖(1 / (2 * Complex.I) : ℂ)‖ * ‖∑ l, ((Y⁻¹ j l : ℝ) : ℂ) * Dm l k + ∑ i, s i * (((Y⁻¹ * Bs i) j k : ℝ) : ℂ)‖
      ≤ 1 * ((g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i) :=
        mul_le_mul hhalf ((norm_add_le _ _).trans (add_le_add hA hBs)) (norm_nonneg _) zero_le_one
    _ = (g : ℝ) * K / c + W * ∑ i, ‖s i‖ / t i := one_mul _

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionMatrixGramOperatorNormLeStatement
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectionMatrix_gramOperatorNorm_le : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ) (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K W : ℝ), 0 < c → 0 ≤ K → 0 ≤ W → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, 0 < t i) → (∀ i x, ‖(t i • (Y⁻¹ * Bs i)) *ᵥ x‖ ≤ W * ‖x‖) → (∀ j k, ‖Dm j k‖ ≤ K) → opNorm 1 1 ((Y.map Complex.ofReal)⁻¹ * ((1 / (2 * Complex.I)) • (Dm + ∑ i, s i • (Bs i).map Complex.ofReal))) ≤ g * (g * K / c + W * ∑ i, ‖s i‖ / t i) := by
  first | exact @GlobalTheory.connMatrix_opNorm_le | exact GlobalTheory.connMatrix_opNorm_le | (intros; apply GlobalTheory.connMatrix_opNorm_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvr
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem ideal_map_eq_span_pow_uniformizer
    : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  intro V W _ _ _ _ _ _ f _ ϖ w e a I hϖ hw hfe hI
  by_cases h0 : I = ⊥
  · exfalso
    subst h0
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at hI
    exact hw.ne_zero (pow_eq_zero_iff'.mp hI).1
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h0 hϖ
  refine ⟨b, ?_, hb⟩
  rw [hb, Ideal.map_span, Set.image_singleton, map_pow,
    Ideal.span_singleton_eq_span_singleton] at hI
  have h1 : Associated (w ^ (e * b)) (w ^ a) := by
    rw [pow_mul]
    exact (hfe.pow_pow (n := b)).symm.trans hI
  have hw0 : w ≠ 0 := hw.ne_zero
  have hwu : ¬ IsUnit w := hw.not_isUnit
  apply le_antisymm
  · exact (pow_dvd_pow_iff hw0 hwu).mp h1.dvd
  · exact (pow_dvd_pow_iff hw0 hwu).mp h1.symm.dvd

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapEqSpanPowUniformizerDvrStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_map_eq_span_pow_uniformizer_dvr : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : V →+* W), Function.Injective f → ∀ (ϖ : V) (w : W) (e a : ℕ) (I : Ideal V), Irreducible ϖ → Irreducible w → Associated (f ϖ) (w ^ e) → I.map f = Ideal.span {w ^ a} → ∃ b : ℕ, e * b = a ∧ I = Ideal.span {ϖ ^ b} := by
  first | exact @GlobalTheory.ideal_map_eq_span_pow_uniformizer | exact GlobalTheory.ideal_map_eq_span_pow_uniformizer | (intros; apply GlobalTheory.ideal_map_eq_span_pow_uniformizer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatible
set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem exists_param_of_deg_zero {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) (hK : K.Rich) (G : C0 K.Oc)
    (hG : ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) :
    ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  let a : ∀ k, Hol (K.W k) := fun k ↦ G (K.triv k)
  have h1 : ∀ k k' (e : K.le 0 k' k), K.sh e (a k) = a k' := fun k k' e ↦
    (hG (K.triv k) (K.triv k') (ptHom (K.triv k') e) rfl).symm
  have h2 : ∀ k i, dw i (a k) = 0 := fun k i ↦ by
    have e0 : G (K.jet k) = TrivSqZeroExt.inl (K.sh (K.le_refl k) (a k)) := hG _ _ (ptHom (K.jet k) (K.le_refl k)) rfl
    let j : K.Hom (K.triv k) (K.jet k) :=
      fromTriv (K.jet k) (K.le_refl k) (tszeSec dw)
        (fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)))
        (Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
          fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
            simp only [RingHom.comp_apply, sh_refl]
            exact tsze_expand h fun a ↦ dw a h⟩)
    have e1 : G (K.jet k) = tszeSec dw (a k) := hG _ _ j rfl
    have e2 := congrArg (fun x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) ↦ x.snd i) (e1.symm.trans e0)
    exact (snd_tszeSec dw (a k) i).symm.trans e2
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_parameter_function_of_fibreDeriv_zero K hK a h1 h2
  refine ⟨p, fun T ↦ ?_⟩
  have e : G T = T.ρ (K.sh (K.le_refl T.k) (a T.k)) := hG _ _ (ptHom T (K.le_refl T.k)) rfl
  rw [e, sh_refl, hp, T.ρ_cst]

end GlobalTheory.AnPer.Charts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatibleStatement
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ G : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) → ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  first | exact @GlobalTheory.AnPer.Charts.exists_param_of_deg_zero | exact GlobalTheory.AnPer.Charts.exists_param_of_deg_zero | (intros; apply GlobalTheory.AnPer.Charts.exists_param_of_deg_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacter
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.HCChar

theorem gal_id_apply {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem hc_isChar : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  intro F _ _ a b n hn α β hα hβ
  obtain ⟨H, π, hH, -, hπ, -, -⟩ := GlobalTheory.T.exists_blockParabolic_subgroup_levi_projection F a b n hn
  haveI : Finite (GL (Fin n) F) := inferInstance
  have h1 : IsChar ℂ ℂ (fun p : H => α (π p).1) := by
    obtain ⟨m, ρ, hρ⟩ := hα
    exact ⟨m, ρ.comp ((MonoidHom.fst _ _).comp π), fun p => hρ _⟩
  have h2 : IsChar ℂ ℂ (fun p : H => β (π p).2) := by
    obtain ⟨m, ρ, hρ⟩ := hβ
    exact ⟨m, ρ.comp ((MonoidHom.snd _ _).comp π), fun p => hρ _⟩
  have hψ : IsChar ℂ ℂ ((fun p : H => α (π p).1) * (fun p : H => β (π p).2)) := isChar_mul_complex h1 h2
  have hind := isChar_ind ℂ ℂ (GL (Fin n) F) H _ hψ
  convert hind using 1
  funext x
  have hcard : (Nat.card {p : GL (Fin n) F // InPar a p} : ℂ) = (Nat.card H : ℂ) := by
    congr 1
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => (hH x).symm))
  unfold hc hcTw ind
  rw [hcard]
  congr 1
  apply finsum_congr
  intro y
  rw [gal_id_apply]
  unfold ext0
  by_cases hy : y⁻¹ * x * y ∈ H
  · rw [dite_eq_left hy, if_pos ((hH _).1 hy), Pi.mul_apply, hπ]
  · rw [dite_eq_right hy, if_neg (fun e => hy ((hH _).2 e))]

end GlobalTheory.Shin.HCChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLIsCharacterStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_isCharacter : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsChar ℂ ℂ α → IsChar ℂ ℂ β → IsChar ℂ ℂ (hc a b α β n) := by
  first | (exact @GlobalTheory.Shin.HCChar.hc_isChar) | (exact GlobalTheory.Shin.HCChar.hc_isChar) | (intros; apply GlobalTheory.Shin.HCChar.hc_isChar  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemIntegralClosureOverGenericFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemIntegralClosureOverGenericFibre
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem exists_common_multiple_mem_closure :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] (s : Finset D),
    ∃ a : A, a ≠ 0 ∧ ∀ d ∈ s,
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) * d ∈ GlobalTheory.KeyOriginNoeth.closure A R D := by
  intro A R _ _ _ _ D _ _ _ s
  classical
  letI : Algebra R D := (baseHom A R D).toAlgebra
  haveI : IsScalarTower R (GlobalTheory.LocAcyc.GenFib A R) D :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ d : D, ∃ a : A, a ≠ 0 ∧ IsIntegral R (baseHom A R D (algebraMap A R a) * d) := by
    intro d
    have hd : IsIntegral (GlobalTheory.LocAcyc.GenFib A R) d := Algebra.IsIntegral.isIntegral d
    obtain ⟨⟨m, hm⟩, hmi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (Algebra.algebraMapSubmonoid R (nonZeroDivisors A)) (Rₘ := GlobalTheory.LocAcyc.GenFib A R) d hd
    obtain ⟨a, ha, rfl⟩ := hm
    refine ⟨a, nonZeroDivisors.ne_zero ha, ?_⟩
    exact hmi
  have hmem : ∀ x : D, IsIntegral R x → x ∈ closure A R D := fun x hx => hx
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert d s hds ih =>
    obtain ⟨a₂, ha₂, h₂⟩ := ih
    obtain ⟨a₁, ha₁, h₁⟩ := key d
    refine ⟨a₁ * a₂, mul_ne_zero ha₁ ha₂, ?_⟩
    intro e he
    apply hmem
    rw [Finset.mem_insert] at he
    rcases he with rfl | he
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₂) * (baseHom A R D (algebraMap A R a₁) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul h₁
    · have : baseHom A R D (algebraMap A R (a₁ * a₂)) * e =
          algebraMap R D (algebraMap A R a₁) * (baseHom A R D (algebraMap A R a₂) * e) := by
        simp only [map_mul]; show _ = baseHom A R D _ * _; ring
      rw [this]
      exact isIntegral_algebraMap.mul (h₂ e he)

end GlobalTheory.KeyOriginNoeth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMemIntegralClosureOverGenericFibreStatement
open IsLocalRing Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_mem_integralClosureOverGenericFibre : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] (s : Finset D),
    ∃ a : A, a ≠ 0 ∧ ∀ d ∈ s,
      GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a) * d ∈ GlobalTheory.KeyOriginNoeth.closure A R D := by
  first | (exact @GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure) | (exact GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure) | (intros; apply GlobalTheory.KeyOriginNoeth.exists_common_multiple_mem_closure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeLiftClassFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusShapeOfSidePreserving
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

open Polynomial SemidirectProduct in
open scoped Classical in
private lemma isCl_apply_eq_of_isConj {G : Type} [Group G] {f : G → ℂ}
    (hf : _root_.GlobalTheory.Shin.IsCl f) {a b : G} (h : IsConj a b) : f a = f b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  have := hf a c⁻¹
  rw [inv_inv] at this
  exact this.symm


open Polynomial SemidirectProduct in
open scoped Classical in
theorem _root_.GlobalTheory.Shin.shLift_isNorm_and_twisted_inv : ∀ (F F' : Type) [Field F] [Field F']
    [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) →
    ∀ (n : ℕ) (f : GL (Fin n) F → ℂ), _root_.GlobalTheory.Shin.IsCl f →
    (∀ δ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ → _root_.GlobalTheory.Shin.shLift s f δ = f γ) ∧
    ∀ δ y : GL (Fin n) F', _root_.GlobalTheory.Shin.shLift s f
      (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) = _root_.GlobalTheory.Shin.shLift s f δ := by
  intro F F' _ _ _ _ s hs n f hf
  have hconj := (_root_.GlobalTheory.Shin.NrmBasic.main F F' s hs n).2.2.1
  refine ⟨fun δ γ hδ => ?_, fun δ y => ?_⟩
  · unfold _root_.GlobalTheory.Shin.IsNorm at hδ
    unfold _root_.GlobalTheory.Shin.shLift
    have hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ := ⟨γ, hδ⟩
    rw [dite_eq_left hex]
    have hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ) :=
      hex.choose_spec
    exact isCl_apply_eq_of_isConj hf
      (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _ (hspec.trans hδ.symm))
  · have hN : IsConj (_root_.GlobalTheory.Shin.nrm s δ)
        (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y)) := by
      rw [hconj δ y, isConj_iff]
      exact ⟨y⁻¹, by rw [inv_inv]⟩
    unfold _root_.GlobalTheory.Shin.shLift
    by_cases hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ
    · have hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ) :=
        hex.choose_spec
      have hex' : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ :=
        ⟨hex.choose, hspec.trans hN⟩
      have hspec' : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex'.choose)
          (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y)) :=
        hex'.choose_spec
      rw [dite_eq_left hex, dite_eq_left hex']
      exact isCl_apply_eq_of_isConj hf
        (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _
          (hspec'.trans (hspec.trans hN).symm))
    · have hex' : ¬ ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ :=
        fun ⟨γ, hγ⟩ => hex ⟨γ, (show IsConj (_root_.GlobalTheory.Shin.incl F F' n γ) _ from hγ).trans hN.symm⟩
      rw [dite_eq_right hex, dite_eq_right hex']

end GlobalTheory.Shin
end

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_lift_class_function : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (f : GL (Fin n) F → ℂ), IsCl f → (∀ δ γ, IsNorm s δ γ → shLift s f δ = f γ) ∧ ∀ δ y : GL (Fin n) F', shLift s f (y⁻¹ * δ * galAct F F' n s y) = shLift s f δ := by
  first | (exact @GlobalTheory.Shin.shLift_isNorm_and_twisted_inv) | (exact GlobalTheory.Shin.shLift_isNorm_and_twisted_inv) | (intros; apply GlobalTheory.Shin.shLift_isNorm_and_twisted_inv <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExactAtOfProd
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.WExactProd

theorem exactAt_of_prod {ι : Type} {c : ComplexShape ℕ} {K : HomologicalComplex AddCommGrpCat.{1} c}
    {L : ι → HomologicalComplex AddCommGrpCat.{1} c} (φ : ∀ i, K ⟶ L i)
    (hφ : ∀ n, Function.Bijective (fun (x : K.X n) (i : ι) => (φ i).f n x)) (p : ℕ)
    (hL : ∀ i, (L i).ExactAt p) : K.ExactAt p := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff]
  suffices key : ∀ z : K.X p, K.d p (c.next p) z = 0 → ∃ v : K.X (c.prev p), K.d (c.prev p) p v = z from key
  intro z hz
  have hcomm : ∀ i {q r : ℕ} (x : K.X q), (L i).d q r ((φ i).f q x) = (φ i).f r (K.d q r x) := by
    intro i q r x
    rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, (φ i).comm]
  have hw : ∀ i, ∃ w : (L i).X (c.prev p), (L i).d (c.prev p) p w = (φ i).f p z := by
    intro i
    have hex := hL i
    rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff] at hex
    refine hex ((φ i).f p z) ?_
    change (L i).d p (c.next p) ((φ i).f p z) = 0
    rw [hcomm, hz, map_zero]
  choose w hw using hw
  obtain ⟨v, hv⟩ := (hφ (c.prev p)).2 w
  refine ⟨v, ?_⟩
  apply (hφ p).1
  funext i
  change (φ i).f p (K.d (c.prev p) p v) = (φ i).f p z
  rw [← hcomm, ← hw i]
  exact congrArg _ (congrFun hv i)

theorem wexact_of_prod (T : Type 1) [Category.{0} T] (U : T) (X : CosimplicialObject T)
    (a : (CosimplicialObject.const T).obj U ⟶ X) (ι : Type) (M : ι → T ⥤ AddCommGrpCat.{1})
    (N : T ⥤ AddCommGrpCat.{1}) (π : ∀ i, N ⟶ M i)
    (hπ : ∀ V, Function.Bijective (fun (x : N.obj V) (i : ι) => (π i).app V x))
    (hM : ∀ i, WExact (M i) a) : WExact N a := by
  have nat : ∀ i {P Q : T} (f : P ⟶ Q) (x : N.obj P), (π i).app Q (N.map f x) = (M i).map f ((π i).app P x) := by
    intro i P Q f x
    exact ConcreteCategory.congr_hom ((π i).naturality f) x
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    apply (hπ U).1
    funext i
    apply (hM i).1
    have h := congrArg ((π i).app _) hxy
    rw [nat, nat] at h
    exact h
  · intro y hy
    have hx : ∀ i, ∃ x : (M i).obj U, (M i).map (a.app (SimplexCategory.mk 0)) x = (π i).app _ y := by
      intro i
      refine (hM i).2.1 ((π i).app _ y) ?_
      rw [← nat, ← nat, hy]
    choose x hx using hx
    obtain ⟨x', hx'⟩ := (hπ U).2 x
    refine ⟨x', ?_⟩
    apply (hπ _).1
    funext i
    change (π i).app _ (N.map (a.app (SimplexCategory.mk 0)) x') = (π i).app _ y
    rw [nat, ← hx i]
    exact congrArg _ (congrFun hx' i)
  · intro n
    refine exactAt_of_prod (fun i => (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{1}).map
      (Functor.whiskerLeft X (π i))) (fun k => ?_) (n + 1) (fun i => (hM i).2.2 n)
    exact hπ (X.obj (SimplexCategory.mk k))

end GlobalTheory.EtC.WExactProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTransposeInvTranspose
noncomputable section

namespace GlobalTheory.InvTransposeEnds

section General

variable {G H V W Y : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
  [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem isIrreducible_comp {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (φ : H →* G)
    (hφ : Function.Surjective φ) : Representation.IsIrreducible (ρ.comp φ) := by
  haveI hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  refine { toNontrivial := ⟨⟨⊥, ⊤, fun e => ?_⟩⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule ℂ V) (congrArg Subrepresentation.toSubmodule e)
  · let S' : Subrepresentation ρ := ⟨S.toSubmodule, fun g v hv => by
      obtain ⟨x, rfl⟩ := hφ g
      exact S.apply_mem_toSubmodule x hv⟩
    rcases h.eq_bot_or_eq_top S' with e | e
    · exact Or.inl (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))
    · exact Or.inr (Subrepresentation.toSubmodule_injective
        (congrArg (Subrepresentation.toSubmodule (ρ := ρ)) e :))

end General

end GlobalTheory.InvTransposeEnds
end
end
