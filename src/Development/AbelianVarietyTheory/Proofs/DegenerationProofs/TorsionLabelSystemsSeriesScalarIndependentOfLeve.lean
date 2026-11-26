module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeve
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeve
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.ModelData.Scalar

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.ModelData.Scalar.tx_congr {O : Type} [CommRing O] [TopologicalSpace O] (N : _root_.GlobalTheory.Ex.NumD O) {m : ℕ} (hm : Odd m)
    {p p' : N.QT (m ^ 2)} (h : N.QEq p p') : N.tx m p = N.tx m p' := by
  unfold _root_.GlobalTheory.Ex.NumD.QEq at h
  obtain ⟨z, hz1, hz2⟩ := h
  unfold _root_.GlobalTheory.Ex.NumD.tx
  have ht : ∀ χ, N.txT m p' χ = N.txT m p (χ + m • z) := fun χ =>
    (_root_.GlobalTheory.Ex.txT_shift O N m hm p p' χ).1 z hz1 hz2
  rw [tsum_congr ht]
  exact ((Equiv.addRight (m • z)).tsum_eq (fun χ => N.txT m p χ)).symm

variable {O : Type} [CommRing O] {N : NumD O} {La : Type} [AddCommGroup La] {EF : LinearMap.BilinForm ℤ La}
  {ζ : ℕ → Oˣ} {lab : ∀ k : ℕ, La → N.QT k}

attribute [local instance] Over.cartesianMonoidalCategory in
private theorem qEq_mul' (N : _root_.GlobalTheory.Ex.NumD O) {k : ℕ}
    {p p' q q' : N.QT k} (h : N.QEq p p')
    (h' : N.QEq q q') :
    N.QEq (p * q) (p' * q') := by
  unfold _root_.GlobalTheory.Ex.NumD.QEq at *
  obtain ⟨z, hz1, hz2⟩ := h
  obtain ⟨z', hz1', hz2'⟩ := h'
  refine ⟨z + z', ?_, ?_⟩
  · simp only [Subgroup.coe_mul, Prod.fst_mul, toAdd_mul, hz1, hz1', smul_add]
    abel
  · simp only [Subgroup.coe_mul, Prod.snd_mul, hz2, hz2', N.io_add]
    ac_rfl

attribute [local instance] Over.cartesianMonoidalCategory in
private theorem qEq_label_pow_nsmul
    (hL : _root_.GlobalTheory.ModelData.Labels N EF ζ lab) {k : ℕ} (hk : 0 < k) (x : La) :
    ∀ d : ℕ, 1 ≤ d → N.QEq ((lab k x) ^ d) (lab k (d • x)) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => simpa using (N.qEq_equivalence k).refl (lab k x)
  | succ d hd ih =>
    rw [pow_succ, succ_nsmul]
    unfold _root_.GlobalTheory.ModelData.Labels at hL
    exact (N.qEq_equivalence k).trans
      (qEq_mul' N ih ((N.qEq_equivalence k).refl _)) (hL.1 k hk _ _)

attribute [local instance] Over.cartesianMonoidalCategory in
private theorem tx_label_nsmul_eq_of_odd [TopologicalSpace O]
    (hL : _root_.GlobalTheory.ModelData.Labels N EF ζ lab) {d m : ℕ} (hd : Odd d) (hm : Odd m)
    (K : ℕ) (hK : K = d * m) (x : La) :
    N.tx K (lab (K ^ 2) (d • x)) = N.tx m (lab (m ^ 2) x) := by
  subst hK
  have hdm : Odd (d * m) := hd.mul hm
  set q := lab ((d * m) ^ 2) x with hq
  have hmem : ((q : Multiplicative N.X × N.Gt).1, (q : Multiplicative N.X × N.Gt).2 ^ (d ^ 2)) ∈
      N.QT (m ^ 2) := by
    rw [N.mem_QT]
    have hqm := (N.mem_QT).1 q.2
    rw [← pow_mul, show d ^ 2 * m ^ 2 = (d * m) ^ 2 by ring]
    exact hqm
  set p : N.QT (m ^ 2) := ⟨_, hmem⟩ with hp
  have h1 : N.tx (d * m) (lab ((d * m) ^ 2) (d • x)) =
      N.tx (d * m) (q ^ d) :=
    (_root_.GlobalTheory.ModelData.Scalar.tx_congr N hdm
      (qEq_label_pow_nsmul hL (pow_pos hdm.pos 2) x d hd.pos)).symm
  have h2 : N.tx (d * m) (q ^ d) = N.tx m p := by
    unfold _root_.GlobalTheory.Ex.NumD.tx
    refine tsum_congr (fun χ => ?_)
    refine _root_.GlobalTheory.Ex.Nest.txT_nest O N d m hd hm (q ^ d) p ?_ ?_ χ
    · rw [SubgroupClass.coe_pow, Prod.pow_fst]
    · rw [SubgroupClass.coe_pow, Prod.pow_snd, ← pow_mul, ← sq]
  have h3 : N.QEq p (lab (m ^ 2) x) := by
    have c4 : ∀ K, m ^ 2 * d ^ 2 = K → ∀ p' : N.QT (m ^ 2),
        (p' : Multiplicative N.X × N.Gt).1 = (lab K x : Multiplicative N.X × N.Gt).1 →
        (p' : Multiplicative N.X × N.Gt).2 = (lab K x : Multiplicative N.X × N.Gt).2 ^ (d ^ 2) →
        N.QEq p' (lab (m ^ 2) x) := by
      intro K hK
      subst hK
      unfold _root_.GlobalTheory.ModelData.Labels at hL
      exact hL.2.2.2.1 (m ^ 2) (d ^ 2) (pow_pos hm.pos 2) (pow_pos hd.pos 2) x
    exact c4 ((d * m) ^ 2) (by ring) p rfl rfl
  rw [h1, h2]
  exact _root_.GlobalTheory.ModelData.Scalar.tx_congr N hm h3

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.ModelData.Scalar.scalar_const : ∀ (C : Type) [NormedField C] (N N' : _root_.GlobalTheory.Ex.NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), Odd n → _root_.GlobalTheory.ModelData.Labels N EF ζ lab → _root_.GlobalTheory.ModelData.Labels N' EF ζ' lab' → (∀ j, ∃ c : Cˣ, ∀ x, N'.tx (n ^ j) (lab' _ x) = c * N.tx (n ^ j) (lab _ x)) → (∃ x, N.tx (n ^ 1) (lab _ x) ≠ 0) → ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x) := by
  intro C _ N N' La _ EF ζ ζ' lab lab' n hn hL hL' hc hx
  obtain ⟨x₀, hx₀⟩ := hx
  obtain ⟨c₁, hc₁⟩ := hc 1
  have hn1 : Odd (n ^ 1) := by simpa using hn
  refine ⟨c₁, c₁.ne_zero, fun j x => ?_⟩
  cases j with
  | zero =>
    have e1 := tx_label_nsmul_eq_of_odd hL hn (Odd.pow hn : Odd (n ^ 0)) (n ^ 1) (by ring) x
    have e2 := tx_label_nsmul_eq_of_odd hL' hn (Odd.pow hn : Odd (n ^ 0)) (n ^ 1) (by ring) x
    rw [← e1, ← e2, hc₁]
  | succ i =>
    obtain ⟨c, hc'⟩ := hc (i + 1)
    have e1 := tx_label_nsmul_eq_of_odd hL (Odd.pow hn : Odd (n ^ i)) hn1 (n ^ (i + 1))
      (by ring) x₀
    have e2 := tx_label_nsmul_eq_of_odd hL' (Odd.pow hn : Odd (n ^ i)) hn1 (n ^ (i + 1))
      (by ring) x₀
    have hcc : (c : C) = c₁ := by
      have h := hc' (n ^ i • x₀)
      rw [e1, e2, hc₁] at h
      exact (mul_right_cancel₀ hx₀ h).symm
    rw [hc' x, hcc]

end GlobalTheory.ModelData.Scalar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionLabelSystems_series_scalar_independent_of_level : ∀ (C : Type) [NormedField C] (N N' : NumD C) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (ζ ζ' : ℕ → Cˣ) (lab : ∀ k : ℕ, La → N.QT k) (lab' : ∀ k : ℕ, La → N'.QT k) (n : ℕ), Odd n → Labels N EF ζ lab → Labels N' EF ζ' lab' → (∀ j, ∃ c : Cˣ, ∀ x, N'.tx (n ^ j) (lab' _ x) = c * N.tx (n ^ j) (lab _ x)) → (∃ x, N.tx (n ^ 1) (lab _ x) ≠ 0) → ∃ c₀ : C, c₀ ≠ 0 ∧ ∀ j x, N'.tx (n ^ j) (lab' _ x) = c₀ * N.tx (n ^ j) (lab _ x) := by
  first | exact @GlobalTheory.ModelData.Scalar.scalar_const | exact GlobalTheory.ModelData.Scalar.scalar_const | (intros; apply GlobalTheory.ModelData.Scalar.scalar_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRExtensionTorsionRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRExtensionTorsionRational
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

namespace GlobalTheory.Ex.TorsionField

open GlobalTheory.Ex.UnifModel

theorem exists_descend_algClosed (hM : MulNSt) {K F C : Type} [Field K] [Field F] [IsAlgClosed F] [Field C]
    [IsAlgClosed C] [CharZero C] (P : PolAV (Sp K)) (a : K →+* F) (i : F →+* C) (c : K →+* C)
    (h : ∀ x, i (a x) = c x) {n : ℕ} (hn : 1 ≤ n) (x : Over.mk (spMap c) ⟶ P.A) (hx : x ^ n = 1) :
    ∃ y : Over.mk (spMap a) ⟶ P.A, y ^ n = 1 ∧ spMap i ≫ y.left = x.left := by
  have hC : (n : C) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hF : (n : F) ≠ 0 := fun e => hC (by rw [← map_natCast i, e, map_zero])
  have c₁ := (hM _ P n hn).2.2.2.2 C (spMap c) hC
  have c₂ := (hM _ P n hn).2.2.2.2 F (spMap a) hF
  have := Nat.finite_of_card_ne_zero (c₁ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)
  let u : Over.mk (spMap c) ⟶ Over.mk (spMap a) := Over.homMk (spMap i) (spMap_comp h)
  let Φ : {y : Over.mk (spMap a) ⟶ P.A // y ^ n = 1} → {y : Over.mk (spMap c) ⟶ P.A // y ^ n = 1} :=
    fun y => ⟨u ≫ y.1, by rw [← MonObj.comp_pow, y.2, MonObj.comp_one]⟩
  have := epi_spMap i
  have hΦ : Function.Injective Φ := fun y y' e =>
    Subtype.ext (Over.OverMorphism.ext ((cancel_epi (spMap i)).1 congr(($e).1.left)))
  obtain ⟨y, hy⟩ := (hΦ.bijective_of_nat_card_le (c₁.trans c₂.symm).le).2 ⟨x, hx⟩
  exact ⟨y.1, y.2, congr(($hy).1.left)⟩

theorem exists_finset (hM : MulNSt) {K F : Type} [Field K] [Field F] [IsAlgClosed F] [CharZero F] [Algebra K F]
    [Algebra.IsAlgebraic K F] (P : PolAV (Sp K)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset F, ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) →
      (∀ c ∈ s, c ∈ β.fieldRange) → ∀ x : Over.mk (spMap (algebraMap K F)) ⟶ P.A, x ^ n = 1 →
        ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.left := by
  classical
  have c₂ := (hM _ P n hn).2.2.2.2 F (spMap (algebraMap K F)) (Nat.cast_ne_zero.2 (by omega))
  have := Nat.finite_of_card_ne_zero (c₂ ▸ pow_ne_zero _ (by omega) : _ ≠ 0)
  have := Fintype.ofFinite {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}
  have hpr := P.isAb.proper
  have key : ∀ x : {y : Over.mk (spMap (algebraMap K F)) ⟶ P.A // y ^ n = 1}, ∃ s : Finset F,
      ∀ (k : Type) [Field k] (β : k →+* F), (∀ c, algebraMap K F c ∈ β.fieldRange) →
        (∀ c ∈ s, c ∈ β.fieldRange) → ∃ y : Sp k ⟶ P.A.left, spMap β ≫ y = x.1.left := by
    intro x
    obtain ⟨E, -, h2, h3⟩ := GlobalTheory.SS.exists_fieldOfValues P.A.left F x.1.left
    obtain ⟨L, hL, rfl⟩ := h3 K P.A.hom inferInstance (Over.w x.1) inferInstance
    obtain ⟨s, hs⟩ := (Submodule.fg_top L.toSubalgebra.toSubmodule).1 hL.fg_top
    refine ⟨s, fun k _ β h₁ h₂ => (h2 k β).1 fun c hc => ?_⟩
    have hc' : c ∈ Submodule.span K (s : Set F) := hs ▸ hc
    clear hc
    induction hc' using Submodule.span_induction with
    | mem c hc => exact h₂ c hc
    | zero => exact zero_mem _
    | add _ _ _ _ ha hb => exact add_mem ha hb
    | smul r c _ hc => rw [Algebra.smul_def]; exact mul_mem (h₁ r) hc
  choose s hs using key
  exact ⟨Finset.univ.biUnion s, fun k _ β h₁ h₂ x hx => hs ⟨x, hx⟩ k β h₁ fun c hc =>
    h₂ c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩

theorem exists_finset_ratTors (hL : Laws) {K F C : Type} [Field K] [Field F] [IsAlgClosed F] [Algebra K F]
    [Algebra.IsAlgebraic K F] [Field C] [IsAlgClosed C] [CharZero C] (i : F →+* C) {S : Scheme.{0}} (t : Sp K ⟶ S)
    (B₁ : PolAV S) {n : ℕ} (hn : 1 ≤ n) :
    ∃ s : Finset F, ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) C] (β : FractionRing R →+* F),
      (∀ c, i (β c) = algebraMap _ C c) → (∀ c, algebraMap K F c ∈ β.fieldRange) → (∀ c ∈ s, c ∈ β.fieldRange) →
      ∀ r : Sp R ⟶ S, spMap β ≫ jK R ≫ r = spMap (algebraMap K F) ≫ t →
      ∀ (B : PolAV (Sp R)) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A r ψ → RatTors B C n := by
  have : CharZero F := i.charZero
  obtain ⟨P, φ, hφ₀, -, hm, -⟩ := hL.polBaseChange S (Sp K) t B₁
  have hφ : IsGrpPullback P.A B₁.A t φ := ⟨hφ₀, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hφ₀.w x), (Over.OverMorphism.ext hy : y₀ = toBase hφ₀.w y), ← hm]
    rfl⟩
  obtain ⟨s, hs⟩ := exists_finset (F := F) hL.mulN P hn
  refine ⟨s, fun R _ _ _ β hβ h₁ h₂ r hr B ψ hψ x hx => ?_⟩
  have e₁ : spMap i ≫ spMap β = jFK (R := R) C := spMap_comp hβ
  have e₂ : spMap i ≫ spMap (algebraMap K F) = spMap (i.comp (algebraMap K F)) := spMap_comp fun _ => rfl
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback hψ (jFK (R := R) C ≫ jK R) _ rfl
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback hφ (spMap (i.comp (algebraMap K F)))
    ((jFK (R := R) C ≫ jK R) ≫ r) (by rw [← e₁, ← e₂, Category.assoc, Category.assoc, hr, Category.assoc])
  obtain ⟨y, hy, hy'⟩ := exists_descend_algClosed hL.mulN P (algebraMap K F) i _ (fun _ => rfl) hn
    (e'.symm (e x)) (by rw [← map_pow, ← map_pow, hx, map_one, map_one])
  obtain ⟨z, hz⟩ := hs _ β h₁ h₂ y hy
  have := epi_spMap β
  have w : (z ≫ φ) ≫ B₁.A.hom = jK R ≫ r := by
    rw [← cancel_epi (spMap β), hr, Category.assoc, hφ₀.w, reassoc_of% hz]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ t) (Over.w y))
  refine ⟨Over.homMk (hψ.1.lift _ _ w) (hψ.1.lift_snd _ _ _), hψ.1.hom_ext ?_ ?_⟩
  · refine (he x).symm.trans ?_
    rw [← e'.apply_symm_apply (e x), he', ← hy', ← hz, ← e₁]
    simp only [Category.assoc]
    exact congrArg (fun q => spMap i ≫ spMap β ≫ q) (hψ.1.lift_fst _ _ w).symm
  · refine (Over.w x).trans ?_
    exact (congrArg (fun q => jFK (R := R) C ≫ q) (hψ.1.lift_snd _ _ w).symm).trans (Category.assoc _ _ _).symm

theorem exists_cDvr_ratTors : Laws → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing W) C], CExt W (IsLocalRing.maximalIdeal W) C → ∀ n : ℕ, 1 ≤ n → ∀ (S₁ S₂ : Scheme.{0}) (s₁ : Sp W ⟶ S₁) (s₂ : Sp W ⟶ S₂) (B₁ : PolAV S₁) (B₂ : PolAV S₂), ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (_ : Algebra (FractionRing W') C) (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ Along io C ∧ CExt W' (IsLocalRing.maximalIdeal W') C ∧ (∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A (spMap io ≫ s₁) ψ → RatTors B C n) ∧ ∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₂.A.left), IsGrpPullback B.A B₂.A (spMap io ≫ s₂) ψ → RatTors B C n := by
  intro hL W _ _ _ ⟨d, hc, h0⟩ C _ _ _ _ hext n hn S₁ S₂ s₁ s₂ B₁ B₂
  classical
  let F := algebraicClosure (FractionRing W) C
  have : IsAlgClosed F := (algebraicClosure.isAlgClosure (FractionRing W) C).isAlgClosed
  let : Algebra W F := ((algebraMap (FractionRing W) F).comp (algebraMap W _)).toAlgebra
  have : IsScalarTower W (FractionRing W) F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have iW : Function.Injective (algebraMap W F) :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  have : FaithfulSMul W F := (faithfulSMul_iff_algebraMap_injective W F).2 iW
  have : Algebra.IsAlgebraic W F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := W) (K := FractionRing W) (C := F)).2 inferInstance
  have : CharZero (FractionRing W) := IsFractionRing.charZero_of_isFractionRing W
  have : CharZero C := charZero_of_injective_algebraMap (algebraMap (FractionRing W) C).injective
  obtain ⟨t₁, ht₁⟩ := exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₁) B₁ hn
  obtain ⟨t₂, ht₂⟩ := exists_finset_ratTors hL (algebraMap F C) (jK W ≫ s₂) B₂ hn
  obtain ⟨V, dV, cV, -, fV, -, lV, hV, -⟩ := exists_complete_dvr_finite_subalgebra W F (t₁ ∪ t₂)
  have i₁ : Function.Injective (algebraMap V F) := Subtype.val_injective
  let β : FractionRing V →+* F := IsFractionRing.lift i₁
  have hβ : ∀ x, β (algebraMap V _ x) = algebraMap V F x := IsFractionRing.lift_algebraMap i₁
  let : Algebra (FractionRing V) C := ((algebraMap F C).comp β).toAlgebra
  have hA : Along (algebraMap W V) C := fun x => congrArg (algebraMap F C) (hβ _)
  have h₁ : ∀ c, algebraMap (FractionRing W) F c ∈ β.fieldRange := fun c => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) c
    rw [map_div₀]
    exact div_mem ⟨_, hβ (algebraMap W V a)⟩ ⟨_, hβ (algebraMap W V b)⟩
  have h₂ : ∀ c ∈ t₁ ∪ t₂, c ∈ β.fieldRange := fun x hx => by
    obtain ⟨u, hu, v, hv, h0, e⟩ := hV x hx
    refine ⟨algebraMap V _ ⟨u, hu⟩ / algebraMap V _ ⟨v, hv⟩, ?_⟩
    rw [map_div₀, hβ, hβ]
    exact (div_eq_iff h0).2 e.symm
  have e : spMap β ≫ jK V ≫ spMap (algebraMap W V) = spMap (algebraMap (FractionRing W) F) ≫ jK W := by
    rw [← Category.assoc, spMap_comp hβ, spMap_comp (d := algebraMap W F) fun _ => rfl]
    exact (spMap_comp fun _ => rfl).symm
  have : CharZero V := (algebraMap V F).charZero
  refine ⟨V, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap W V, ⟨dV, cV, inferInstance⟩,
    fun a b h => iW (congrArg Subtype.val h), RingHom.finite_algebraMap.2 fV, lV, hA, cExt_of_integral hext hA,
    ht₁ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_left _ hc)) _ ?_,
    ht₂ V β (fun _ => rfl) h₁ (fun c hc => h₂ c (Finset.mem_union_right _ hc)) _ ?_⟩
  · rw [reassoc_of% e]
  · rw [reassoc_of% e]

end GlobalTheory.Ex.TorsionField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRExtensionTorsionRationalStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_extension_torsion_rational : Laws → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing W) C], CExt W (IsLocalRing.maximalIdeal W) C → ∀ n : ℕ, 1 ≤ n → ∀ (S₁ S₂ : Scheme.{0}) (s₁ : Sp W ⟶ S₁) (s₂ : Sp W ⟶ S₂) (B₁ : PolAV S₁) (B₂ : PolAV S₂), ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (_ : Algebra (FractionRing W') C) (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ IsLocalHom io ∧ Along io C ∧ CExt W' (IsLocalRing.maximalIdeal W') C ∧ (∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₁.A.left), IsGrpPullback B.A B₁.A (spMap io ≫ s₁) ψ → RatTors B C n) ∧ ∀ (B : PolAV (Sp W')) (ψ : B.A.left ⟶ B₂.A.left), IsGrpPullback B.A B₂.A (spMap io ≫ s₂) ψ → RatTors B C n := by
  first | exact @GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors | exact GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors | (intros; apply GlobalTheory.Ex.TorsionField.exists_cDvr_ratTors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationOverFiniteDvrExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationOverFiniteDvrExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

namespace GlobalTheory.FiniteDVRValuation

section
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) {c : V}
    (hc : c ≠ 0) :
    ∃ n : ℕ, v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) =
        ((n : ℚ) : WithTop ℚ) ∧ (n = 0 → IsUnit c) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  refine ⟨n, ?_, fun hn => by subst hn; simp⟩
  rw [hv _ n ⟨u, by rw [zpow_natCast, map_mul, map_pow, mul_comm]⟩]
  norm_cast

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.FiniteDVRValuation.val_nonneg (hϖ : Irreducible ϖ) (hv : _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v) (c : V) :
    0 ≤ v (algebraMap (FractionRing V) F (algebraMap V (FractionRing V) c)) := by
  by_cases hc : c = 0
  · subst hc
    simp
  · obtain ⟨n, hn, -⟩ := _root_.GlobalTheory.FiniteDVRValuation.exists_nat_val hϖ hv hc
    rw [hn]
    exact_mod_cast n.cast_nonneg

end

def nonnegSubring {F K : Type} [Field F] [Field K] (v : AddValuation F (WithTop ℚ)) (e : K →+* F) :
    ValuationSubring K where
  carrier := {x | 0 ≤ v (e x)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul, AddValuation.map_mul] at *
    exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, map_neg, AddValuation.map_neg] at *
    exact ha
  mem_or_inv_mem' := by
    intro x
    simp only [Set.mem_setOf_eq]
    by_cases hx : x = 0
    · left; simp [hx]
    by_contra hcon
    push_neg at hcon
    have h1 : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx, map_one, AddValuation.map_one]
    have h2 : v (e x) + v (e x⁻¹) < 0 := by
      calc v (e x) + v (e x⁻¹) ≤ 0 + v (e x⁻¹) := by gcongr; exact hcon.1.le
        _ = v (e x⁻¹) := zero_add _
        _ < 0 := hcon.2
    exact h2.ne h1

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.FiniteDVRValuation.main :
    ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W']
      [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i →
      i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F]
      [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ F v →
      (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧
      (∃ i' : FractionRing W →+* FractionRing W',
        (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧
        ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 →
          ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧
      ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K,
        ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  intro W W' _ _ _ _ _ _ i hi hfin ϖ hϖ F _ _ v hv
  refine ⟨fun r => _root_.GlobalTheory.FiniteDVRValuation.val_nonneg hϖ hv r, ?_,
    fun K _ e => ⟨_root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e, fun x => ⟨Iff.rfl, fun h => ?_⟩⟩⟩
  · have hinj : Function.Injective ((algebraMap W' (FractionRing W')).comp i) :=
      (IsFractionRing.injective W' (FractionRing W')).comp hi
    have hunit : ∀ x : W,
        v (algebraMap (FractionRing W') F (algebraMap W' _ (i x))) = 0 → IsUnit x := by
      intro x hx
      by_contra hxu
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hx
      have hmax := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' i hfin.to_isIntegral
        (IsLocalRing.maximalIdeal W')
      have hcomap : (IsLocalRing.maximalIdeal W').comap i = IsLocalRing.maximalIdeal W :=
        IsLocalRing.eq_maximalIdeal hmax
      have hmem : x ∈ (IsLocalRing.maximalIdeal W').comap i := by
        rw [hcomap]
        exact (IsLocalRing.mem_maximalIdeal x).2 hxu
      have hix : ¬IsUnit (i x) := (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 hmem)
      have hle := (_root_.ReciprocityTheory.ChartRestriction.G.DVR.TWO.v_of_V v hϖ hv (i x)).2 hix ((map_ne_zero_iff i hi).2 hx0)
      have hle' : (1 : WithTop ℚ) ≤ 0 := by
        rw [← hx]
        exact hle
      exact absurd hle' (by norm_num)
    refine ⟨IsFractionRing.lift hinj, fun r => IsFractionRing.lift_algebraMap hinj r,
      fun a ha => ?_⟩
    by_cases ha0 : a = 0
    · subst ha0
      simp at ha
    rcases ValuationRing.isInteger_or_isInteger W a with ⟨x, hx⟩ | ⟨x, hx⟩
    · subst hx
      rw [IsFractionRing.lift_algebraMap, RingHom.comp_apply] at ha
      exact ⟨(hunit x ha).unit, rfl⟩
    · have hinv : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
        have hsum : v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a)) +
            v (algebraMap (FractionRing W') F (IsFractionRing.lift hinj a⁻¹)) = 0 := by
          rw [← AddValuation.map_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one,
            AddValuation.map_one]
        rwa [ha, zero_add] at hsum
      rw [← hx, IsFractionRing.lift_algebraMap, RingHom.comp_apply] at hinv
      refine ⟨(hunit x hinv).unit⁻¹, ?_⟩
      rw [← inv_inv a, ← hx, map_units_inv, IsUnit.unit_spec]
  · have hx0 : x ≠ 0 := by
      rintro rfl
      simp at h
    have h1 : x ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e := (ValuationSubring.valuation_le_one_iff _ _).1 h.le
    have h2 : x⁻¹ ∈ _root_.GlobalTheory.FiniteDVRValuation.nonnegSubring v e :=
      (ValuationSubring.valuation_le_one_iff _ _).1 (by rw [map_inv₀, h, inv_one])
    change 0 ≤ v (e x) at h1
    change 0 ≤ v (e x⁻¹) at h2
    have hsum : v (e x) + v (e x⁻¹) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, AddValuation.map_one]
    exact le_antisymm (le_add_of_nonneg_right h2 |>.trans_eq hsum) h1

end GlobalTheory.FiniteDVRValuation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationOverFiniteDvrExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_over_finite_dvr_extension : ∀ (W W' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CommRing W'] [IsDomain W'] [IsDiscreteValuationRing W'] (i : W →+* W'), Function.Injective i → i.Finite → ∀ (ϖ : W'), Irreducible ϖ → ∀ (F : Type) [Field F] [Algebra (FractionRing W') F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v → (∀ r : W', 0 ≤ v (algebraMap (FractionRing W') F (algebraMap W' _ r))) ∧ (∃ i' : FractionRing W →+* FractionRing W', (∀ r, i' (algebraMap W _ r) = algebraMap W' _ (i r)) ∧ ∀ a : FractionRing W, v (algebraMap (FractionRing W') F (i' a)) = 0 → ∃ u : Wˣ, algebraMap W (FractionRing W) u = a) ∧ ∀ (K : Type) [Field K] (e : K →+* F), ∃ S : ValuationSubring K, ∀ x, (x ∈ S ↔ 0 ≤ v (e x)) ∧ (S.valuation x = 1 → v (e x) = 0) := by
  first | exact @GlobalTheory.FiniteDVRValuation.main | exact GlobalTheory.FiniteDVRValuation.main | (intros; apply GlobalTheory.FiniteDVRValuation.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedRosatiGeneratorValuesMoveAlongIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedRosatiGeneratorValuesMoveAlongIso
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
noncomputable section
namespace GlobalTheory.RosMove

def rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) : Fin 6 → (A ⊗ A ⟶ A) :=
  ![(fst A A ≫ f) * snd A A, fst A A ≫ f, snd A A, fst A A * (snd A A ≫ g), fst A A, snd A A ≫ g]

theorem rosO_left {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) (k : Fin 6) :
    (rosO A f g k).left = rosatiφ A f g k := by
  fin_cases k <;> rfl

theorem lift_rosO {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A)
    (k : Fin 6) : lift x y ≫ rosO A f g k = ![(x ≫ f) * y, x ≫ f, y, x * (y ≫ g), x, y ≫ g] k := by
  fin_cases k <;> simp [rosO, MonObj.comp_mul]

theorem val_origin {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left} {f g : A ⟶ A}
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)}
    (hu : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L z J) : val u (lift (1 : T ⟶ A) (1 : T ⟶ A)).left z J = 1 := by
  have e : lift (1 : T ⟶ A) (1 : T ⟶ A) = toUnit T ≫ lift η[A] η[A] := by simp [Hom.one_def]
  have := val_corr hJ hu (toUnit T).left
  rw [val_pull hJ, val_one] at this
  rw [e]; exact this

theorem val_move (hG : GlobalFnsSt) {F : Type} [Field F] [IsAlgClosed F] {S S' : Scheme.{0}} (t : Sp F ⟶ S) (t' : Sp F ⟶ S')
    {A : Over S} [GrpObj A] [IsCommMonObj A] {A' : Over S'} [GrpObj A'] [IsCommMonObj A'] (hA : IsAbelianScheme A)
    (hA' : IsAbelianScheme A') {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (Φ : (Over.mk t ⊗ A).left ⟶ A'.left) (w : LB.Iso (L.pull (snd (Over.mk t) A).left) (L'.pull Φ)) (hw : w.IsGen)
    (hΦ : Φ ≫ A'.hom = (fst (Over.mk t) A).left ≫ t') (ψ : (Over.mk t ⟶ A) →* (Over.mk t' ⟶ A'))
    (hψ : ∀ x, (lift (𝟙 (Over.mk t)) x).left ≫ Φ = (ψ x).left) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] (f' g' : A' ⟶ A')
    (hf : ∀ x, ψ (x ≫ f) = ψ x ≫ f') (hg : ∀ x, ψ (x ≫ g) = ψ x ≫ g')
    {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : u.IsGen)
    (u₀ : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L))
    {u' : LB.Gen (LB.LinComb L' (rosatiφ A' f' g') rosatiε)} (hu' : u'.IsGen)
    (u₀' : LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ u' (zero2 A')) (LB.oneGen L'))
    (z : Sp F) (N) (J) (hN : Good L z N) (hJ : Good L' z J) (b b' : Over.mk t ⟶ A) :
    val u' (lift (ψ b) (ψ b')).left z J =
      (∏ k, gw w (lift (𝟙 (Over.mk t)) (lift b b' ≫ rosO A f g k)).left z (J (ψ (lift b b' ≫ rosO A f g k)).left)
        (fun _ => N (lift b b' ≫ rosO A f g k).left) ^ rosatiε k) * val u (lift b b').left z N := by
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  let Y : Over S := T ⊗ (A ⊗ A)
  let p : Y.left ⟶ Sp F := (fst T (A ⊗ A)).left
  let Y' : Over S' := Over.mk (p ≫ t')
  let Θ : (Y ⟶ A) → (Y' ⟶ A') := fun x => Over.homMk ((lift (fst T (A ⊗ A)) x).left ≫ Φ) (by
    show ((lift (fst T (A ⊗ A)) x).left ≫ Φ) ≫ A'.hom = p ≫ t'
    rw [Category.assoc, hΦ, ← Category.assoc, ← Over.comp_left, lift_fst])
  let pt : (T ⟶ A ⊗ A) → (T' ⟶ Y') := fun c => Over.homMk (lift (𝟙 T) c).left (by
    show (lift (𝟙 T) c).left ≫ (fst T (A ⊗ A)).left ≫ t' = t'
    rw [← Category.assoc, ← Over.comp_left, lift_fst]; exact Category.id_comp _)
  have hΘ : ∀ c x, pt c ≫ Θ (snd _ _ ≫ x) = ψ (c ≫ x) := fun c x => by
    ext
    show (lift (𝟙 T) c).left ≫ (lift (fst T (A ⊗ A)) (snd _ _ ≫ x)).left ≫ Φ = _
    rw [← Category.assoc, ← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, hψ]
  let H : Y' ⟶ A' ⊗ A' := lift (Θ (snd _ _ ≫ fst A A)) (Θ (snd _ _ ≫ snd A A))
  have hH : ∀ x y, pt (lift x y) ≫ H = lift (ψ x) (ψ y) := fun x y => by
    rw [comp_lift, hΘ, hΘ, lift_fst, lift_snd]
  have hr : ∀ x y k, lift (ψ x) (ψ y) ≫ rosO A' f' g' k = ψ (lift x y ≫ rosO A f g k) := fun x y k => by
    rw [lift_rosO, lift_rosO]
    fin_cases k <;> simp [hf, hg]
  have := hA.smooth
  have := hA'.proper
  have sm : Smooth (A ⊗ A).hom := by
    show Smooth (pullback.fst A.hom A.hom ≫ A.hom); infer_instance
  have sp : Smooth p := by
    show Smooth (pullback.fst t (A ⊗ A).hom); infer_instance
  have rd : IsReduced Y.left := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hE : ∀ k, (Θ (snd _ _ ≫ rosO A f g k)).left = H.left ≫ rosatiφ A' f' g' k := fun k => by
    rw [← rosO_left, ← Over.comp_left]
    refine ComplexPoints.hom_ext_of_points (X := Y.left) p A'.hom ((Over.w _).trans (Over.w _).symm) fun x hx => ?_
    let x₀ : T ⟶ Y := Over.homMk x (by
      show x ≫ Y.hom = t
      rw [← Over.w (fst T (A ⊗ A)), ← Category.assoc]
      exact (congrArg (· ≫ t) hx).trans (Category.id_comp _))
    have e : x₀ = lift (𝟙 T) (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A)) := by
      refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
      · rw [lift_fst]; ext; exact hx
      · rw [lift_snd, ← comp_lift, ← comp_lift, lift_fst_snd, Category.comp_id]
    have e' : x = (pt (lift (x₀ ≫ snd _ _ ≫ fst A A) (x₀ ≫ snd _ _ ≫ snd A A))).left := congrArg (·.left) e
    rw [e', ← Over.comp_left, ← Over.comp_left, hΘ, ← Category.assoc (pt _), hH, hr]
  let φ : Fin 6 → (Y.left ⟶ (T ⊗ A).left) := fun k => (lift (fst T (A ⊗ A)) (snd _ _ ≫ rosO A f g k)).left
  have hφ : ∀ k, φ k ≫ (snd T A).left = (snd T (A ⊗ A)).left ≫ rosatiφ A f g k := fun k => by
    rw [← rosO_left, ← Over.comp_left, ← Over.comp_left, lift_snd]
  have hφc : ∀ c k, (lift (𝟙 T) c).left ≫ φ k = (lift (𝟙 T) (c ≫ rosO A f g k)).left := fun c k => by
    rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
  obtain ⟨a, ha, va⟩ := exists_gen hL (φ' := fun k => φ k ≫ (snd T A).left) (ε' := rosatiε)
    (fun U _ h => by simp only [hφ]) (LB.pullGen L _ _ u (snd T (A ⊗ A)).left) (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨s, hs, vs⟩ := GlobalTheory.EndRosati.exists_gen_through hL hL' w hw φ rosatiε a ha
  have ev : ∀ (c : T ⟶ A ⊗ A) (y : Sp F) N J, Good L y N → Good L' y J → val s (lift (𝟙 T) c).left y J =
      (∏ k, gw w (lift (𝟙 T) (c ≫ rosO A f g k)).left y (J (ψ (c ≫ rosO A f g k)).left)
        (fun _ => N (c ≫ rosO A f g k).left) ^ rosatiε k) * val u c.left y N := fun c y N J hN hJ => by
    rw [vs _ _ y J N hJ hN, va _ _ y N hN, val_pull hN, ← Over.comp_left, lift_snd]
    refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
    rw [hφc, hψ, ← Over.comp_left, lift_snd]
  have ev' : ∀ (x x' : T ⟶ A) (y : Sp F) J, Good L' y J →
      val (LB.pullGen L' _ _ u' H.left) (lift (𝟙 T) (lift x x')).left y J = val u' (lift (ψ x) (ψ x')).left y J :=
    fun x x' y J hJ => by rw [val_pull hJ, ← hH]; rfl
  have hp : Function.Surjective p.appTop.hom := by
    let β : Y ≅ A ⊗ (A ⊗ T) := β_ _ _ ≪≫ α_ _ _ _
    have e : p = β.hom.left ≫ (snd A (A ⊗ T)).left ≫ (snd A T).left := by
      have : fst T (A ⊗ A) = β.hom ≫ snd A (A ⊗ T) ≫ snd A T := by simp [β, Y]
      exact congrArg (·.left) this
    rw [e]
    refine surj_comp ?_ (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    have : IsIso β.hom.left := inferInstanceAs (IsIso ((Over.forget S).map β.hom))
    have : IsIso β.hom.left.appTop := inferInstanceAs (IsIso (β.hom.left.app ⊤))
    exact (ConcreteCategory.bijective_of_isIso β.hom.left.appTop).2
  refine (ev' b b' z J hJ).symm.trans (Eq.trans ?_ (ev _ z N J hN hJ))
  refine gen_unique' hL' (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ _) (hE k)) p
    (lift (𝟙 T) (lift 1 1)).left (by rw [← Over.comp_left, lift_fst]; rfl) hp
    (DVR.pullGen_isGen _ _ _ _ hu' _) hs (fun y I hI => ?_) _ _ z J hJ
  choose M hM using fun χ : Sp F ⟶ A.left => exists_chart hL (χ y)
  have o : ∀ k, lift (1 : T ⟶ A) 1 ≫ rosO A f g k = 1 := fun k => by
    rw [lift_rosO]; fin_cases k <;> simp [MonObj.one_comp]
  refine (ev' _ _ y I hI).trans (Eq.trans ?_ (ev _ y M I hM hI).symm)
  rw [map_one, val_origin u₀' (T := T') hI, val_origin u₀ (T := T) hM]
  simp [o, rosatiε, Fin.prod_univ_succ]

theorem rosV_move : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  intro hL R R' _ _ _ _ D D' F _ _ _ _ N N' ν ν' O _ _ oa oa' Φ w φ wv hw hΦ hφ hwv hact a ρ ρ' ⟨u, hu, u₀, hρ⟩
    ⟨u', hu', u₀', hρ'⟩ b b'
  have := oa.hom a
  have := oa.hom (star a)
  let ψ : (TF (R := R) F ⟶ D.P.A) →* (TF (R := R') F ⟶ D'.P.A) :=
    (ν'.eA.toMonoidHom.comp φ).comp ν.eA.symm.toMonoidHom
  have e : ∀ x, ψ (ν.eA x) = ν'.eA (φ x) := fun x => by simp [ψ]
  have ea : ∀ y x, ν.eA (actV ν oa y x) = ν.eA x ≫ oa.act y := fun y x => ν.eA.apply_symm_apply _
  have hf : ∀ y x, ψ (x ≫ oa.act y) = ψ x ≫ oa'.act y := fun y x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [← ea, e, e, hact]; exact ν'.eA.apply_symm_apply _
  have hψ : ∀ x, (lift (𝟙 (TF (R := R) F)) x).left ≫ Φ = (ψ x).left := fun x => by
    obtain ⟨x, rfl⟩ := ν.eA.surjective x
    rw [e, hφ]
  let z : Sp F := IsLocalRing.closedPoint F
  have hN : Good D.P.L z ν.J := fun q => ν.good q trivial
  have hJ : Good D'.P.L z ν'.J := fun q => ν'.good q trivial
  have H := val_move hL.globalFns _ _ D.P.isAb D'.P.isAb D.P.isLB D'.P.isLB Φ w hw hΦ ψ hψ _ _ _ _ (hf (star a)) (hf a)
    hu u₀ hu' u₀' z ν.J ν'.J hN hJ (ν.eA b) (ν.eA b')
  let W : (TF (R := R) F ⟶ D.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x =>
    gw w (lift (𝟙 (TF (R := R) F)) x).left z (ν'.J (ψ x).left) (fun _ => ν.J x.left)
  have hW : ∀ x, toStk z (wv x) = (W (ν.eA x)).val := fun x => by
    rw [hwv, ← e]
    have m₁ : Φ ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left) :=
      (congrArg (fun q : Sp F ⟶ _ => q z ∈ D'.P.L.U (ν'.J (ψ (ν.eA x)).left)) (hψ (ν.eA x))).mpr (hJ _)
    have m₂ : (snd (TF (R := R) F) D.P.A).left ((lift (𝟙 (TF (R := R) F)) (ν.eA x)).left z) ∈ D.P.L.U (ν.J (ν.eA x).left) :=
      (congrArg (fun q : TF (R := R) F ⟶ _ => q.left z ∈ D.P.L.U (ν.J (ν.eA x).left))
        (lift_snd (𝟙 (TF (R := R) F)) (ν.eA x))).mpr (hN _)
    exact toStk_valF _ (_ ⊓ _) z ⟨mem_pull.2 m₁, mem_pull.2 m₂⟩ _
  have H' : val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J =
      (∏ k, W (lift (ν.eA b) (ν.eA b') ≫ rosO _ (oa.act (star a)) (oa.act a) k) ^ rosatiε k) * val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J := by
    rw [← e, ← e]; exact H
  have v : toStk z (ρ b b') = (val (Z := Sp F) u (lift (ν.eA b) (ν.eA b')).left z ν.J).val := by
    rw [hρ]; exact toStk_valF _ _ z (hN.mem _ _) _
  have v' : toStk z (ρ' (φ b) (φ b')) = (val (Z := Sp F) u' (lift (ν'.eA (φ b)) (ν'.eA (φ b'))).left z ν'.J).val := by
    rw [hρ']; exact toStk_valF _ _ z (hJ.mem _ _) _
  apply (toStk z).injective
  simp only [map_mul, hW, v, v', ea, ← Units.val_mul, H', lift_rosO]
  congr 1
  clear_value W
  apply Additive.ofMul.injective
  simp [rosatiε, Fin.prod_univ_succ, ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.RosMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisedRosatiGeneratorValuesMoveAlongIsoStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedRosatiGenerator_values_move_along_iso : Laws → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (D : DegPre R) (D' : DegPre R') (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F] (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N') (O : Type) [CommRing O] [StarRing O] (oa : D.P.OAct O) (oa' : D'.P.OAct O) (Φ : (TF (R := R) F ⊗ D.P.A).left ⟶ D'.P.A.left) (w : LB.Iso (D.P.L.pull (snd (TF (R := R) F) D.P.A).left) (D'.P.L.pull Φ)) (φ : N.A →* N'.A) (wv : N.A → F), w.IsGen → Φ ≫ D'.P.A.hom = (fst (TF (R := R) F) D.P.A).left ≫ (TF (R := R') F).hom → (∀ x, (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left ≫ Φ = (ν'.eA (φ x)).left) → (∀ x, wv x = valF (lift (𝟙 (TF (R := R) F)) (ν.eA x)).left _ (w.s (fun _ => ν'.J (ν'.eA (φ x)).left, fun _ => ν.J (ν.eA x).left)).val) → (∀ y b, φ (actV ν oa y b) = actV ν' oa' y (φ b)) → ∀ (a : O) ρ ρ', RosV ν oa a ρ → RosV ν' oa' a ρ' → ∀ b b', ρ' (φ b) (φ b') * (wv (actV ν oa (star a) b) * wv b' * wv (b * actV ν oa a b')) = ρ b b' * (wv (actV ν oa (star a) b * b') * wv b * wv (actV ν oa a b')) := by
  first | exact @GlobalTheory.RosMove.rosV_move | exact GlobalTheory.RosMove.rosV_move | (intros; apply GlobalTheory.RosMove.rosV_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ObjStOfTripleReframe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem int_eq_of_exp_div_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) :
    m = n := by
  have hd : ∀ k : ℕ, 0 < k → (k : ℤ) ∣ m - n := fun k hk => by
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h k hk)
    have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    refine ⟨-j, ?_⟩
    have : ((m - n : ℤ) : ℂ) = ((k * -j : ℤ) : ℂ) := by
      push_cast
      apply mul_left_cancel₀ hp
      have h2 := congrArg (· * (k : ℂ)) hj
      simp only [add_mul, div_mul_cancel₀ _ hk'] at h2
      linear_combination -h2
    exact_mod_cast this
  refine sub_eq_zero.1 (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hd ((m - n).natAbs + 1) (Nat.succ_pos _)) ?_)
  rw [Int.natAbs_natCast]
  exact Nat.lt_succ_self _

theorem objSt_of_triple_reframe : Laws → TripleSt → ReframeSt → ObjSt := by
  intro laws hT hR E _ _ _ H D La _ _ EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨Q, oa, L₀, u₀, hg, hiso, hdet, ht₁, ht₂, hker, hact, hW⟩ :=
    hT E H D La EF g ty P Hm₀ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨u, Hm, χ, Ef, F, hAH, hE, hF⟩ := hR Q L₀ g u₀ hg ht₁ ht₂
  have hΛ : ∀ a, F (P a) ∈ u.Λ := fun a => (u.ker _).1 ((hF _).trans ((hker _).2 ⟨a, rfl⟩))
  have hsur : ∀ z ∈ u.Λ, ∃ a, z = F (P a) := fun z hz => by
    obtain ⟨w, rfl⟩ := F.surjective z
    obtain ⟨a, ha⟩ := (hker w).1 ((hF w).symm.trans ((u.ker _).2 hz))
    exact ⟨a, by rw [ha]⟩
  have hW' : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • F (P a))) (u.ex ((k : ℂ)⁻¹ • F (P b))) (unitOn c) := fun k a b c hk hc => by
    rw [← map_smul F, ← map_smul F, hF, hF]
    exact hW k a b c hk hc
  have hEf : ∀ a b, Ef ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩ = EF a b := fun a b => int_eq_of_exp_div_eq fun k hk => by
    have w₁ := PeriodPoint.weilIs_of_isAH laws Q rfl u hAH Ef hE k ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩
      (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    have w₂ := hW' k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
    exact congrArg Units.val
      (PrimUnif.unitOn_inj' (CommutatorPairing.weilIs_unique laws.globalFns Q.isAb Q.isLB w₁ w₂))
  have hact' : ∀ (a : 𝓞 E) z, u.ex (F fun k => ty k (a : E) * z k) = u.ex (F z) ≫ oa.act a := fun a z => by
    rw [hF, hF, hact]
  let d : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
    LinearMap.pi fun k => ty k (H.w0 : E) • LinearMap.proj (R := ℂ) (φ := fun _ => ℂ) k
  let G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ) := F.toLinearMap ∘ₗ d ∘ₗ F.symm.toLinearMap
  have hG : ∀ z, G (F z) = F fun k => ty k (H.w0 : E) * z k := fun z => by
    change F (d (F.symm (F z))) = _
    rw [F.symm_apply_apply]
    rfl
  have hGP : ∀ a, G (F (P a)) = F (P (H.w0 • a)) := fun a => by
    rw [hG]
    congr 1
    funext k
    exact (h4 _ _ _).symm
  have hGΛ : ∀ l ∈ u.Λ, G l ∈ u.Λ := fun l hl => by
    obtain ⟨a, rfl⟩ := hsur l hl
    rw [hGP]
    exact hΛ _
  have hGex : ∀ z, u.ex (G z) = u.ex z ≫ oa.act H.w0 := fun z => by
    obtain ⟨w, rfl⟩ := F.surjective z
    rw [hG, hact']
  have hχ := (@GlobalTheory.SelfCube.appellHumbert_data_of_iso_cube GlobalTheory.valAt'_rules
    (GlobalTheory.holFamily_lift GlobalTheory.valAt'_rules) Q Q.isAb.comm u Hm χ Ef
    ⟨hAH.1, hAH.2.2.1, hE, hAH.2.2.2⟩ (oa.act H.w0) G hGΛ hGex hiso).2
  refine ⟨Q, oa, u, Hm, χ, F, hΛ, hiso, hdet, hAH, hsur, fun a b => ?_, fun a => ?_, hact', hW'⟩
  · rw [← hEf]
    exact (hE ⟨F (P a), hΛ a⟩ ⟨F (P b), hΛ b⟩).symm
  · rw [hχ, ← hEf]
    congr 2
    exact Subtype.ext (hGP a)

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VFCorr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.ActValues
open GlobalTheory.TorusExt GlobalTheory.ValuesExist

section Val
variable {F : Type} [Field F] {X Y Y' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : (Sp F ⟶ X) → L.ι}

theorem vF_corr {z : Sp F} (hJ : Good L z J) {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y' ⟶ X)} {ε'' : K'' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {u : LB.Gen (LB.LinComb L φ' ε')}
    {t' : LB.Gen (LB.LinComb L φ'' ε'')} {h : Y' ⟶ Y}
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ u h)) t') (r : Sp F ⟶ Y') :
    vF t r J * vF u (r ≫ h) J = vF t' r J := by
  have e := val_corr hJ H r
  rw [val_mul hJ, val_pull hJ] at e
  rw [← coe_val t r hJ, ← coe_val u _ hJ, ← coe_val t' r hJ, ← e, map_mul, Units.val_mul]
end Val

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N)

theorem good (z : Sp F) : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem psi_eq (y : N.X) :
    (N.ψ y : F) = vF (LB.mulGen D.P.L _ _ _ _ (D.psi (ν.eX y)) D.rigK) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  rw [ν.ψ_eq, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← Units.val_mul, ← map_mul]
  exact congrArg (fun q => (((stalkUnits z).symm q : Fˣ) : F))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm

theorem tau_eq (a b : N.X) : (N.τ a b : F) = vF (D.tau (ν.eX a) (ν.eX b)) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  let e := (stalkUnits z).symm
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z ν.J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z ν.J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have hψ : ∀ y, N.ψ y = e (p (ν.eX y) * ρ) := fun y => Units.ext ((psi_eq ν y).trans
    ((coe_val _ _ hJ).symm.trans (congrArg (fun q => ((e q : Fˣ) : F)) (val_mul hJ _ _ _))))
  refine Eq.trans ?_ (coe_val _ _ hJ)
  rw [hτ, NumD.τ, hψ, hψ, hψ, ← map_div, ← map_div, map_add (f := _)]
  refine congrArg (fun q => ((e q : Fˣ) : F)) (Additive.ofMul.injective ?_)
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

theorem brAct : Laws → BrActSt := by
  intro hL R _ _ D _ _ F _ _ _ N ν O _ _ _ oa
  have hJ := good ν (IsLocalRing.closedPoint F)
  refine ⟨fun a => ?_, fun a => ?_, fun w₀ hw => ?_⟩
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
    refine ⟨r, ⟨hr, r₀⟩, fun y y' => ?_⟩
    have h := vF_corr hJ (oa.tau_bal a r hr r₀ (ν.eX y) (ν.eX y')) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.pt2 (ν.eX y) (ν.eX y') = (lift (ν.eA (N.c y)) (ν.eA (N.c y'))).left := by
      rw [ν.c_eq, ν.c_eq]
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
      refine congrArg CommaMorphism.left (show κ ≫ lift _ _ = _ from ?_)
      simp only [comp_lift, comp_toUnit_assoc]
    rw [tau_eq ν, tau_eq ν, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← h2]
    exact h
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    have hr := oa.onB.rosati (star a)
    rw [star_star] at hr
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ hr
    refine ⟨r, ⟨hr, r₀⟩, fun g g' c c' hc hc' hg => ⟨by rw [hc.1, hc'.1, hg.1], fun χ => ?_⟩⟩
    have h := vF_corr hJ (hg.2 r hr r₀ (ν.eX χ)) (𝟙 (Sp F))
    rw [hc'.2, hc.2, AddEquiv.apply_symm_apply, ν.c_eq, hc.1]
    exact h.symm.trans (congrArg (fun q => _ * vF r q ν.J) (Category.id_comp _))
  · obtain ⟨t, ht, t₀, hy⟩ := hw
    refine ⟨t, ⟨ht, t₀⟩, fun y => ?_⟩
    have h := vF_corr hJ (hy (ν.eX y)) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.xK (ν.eX y) = (ν.eA (N.c y)).left := by
      rw [ν.c_eq]
      exact (Category.assoc _ _ _).symm
    rw [tau_eq ν, psi_eq ν, AddEquiv.apply_symm_apply, ← h2]
    exact h

end GlobalTheory.ActValues
end
