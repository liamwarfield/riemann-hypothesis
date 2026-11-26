module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFacts
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordInjectiveRangeMem
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

noncomputable section

namespace GlobalTheory.WachTie

theorem coord_injective_range_mem : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → IsCrys PD T.ρ → Function.Injective (coord W R jE T (fun k => (b k : W.DD T))) ∧ LinearMap.range (coord W R jE T (fun k => (b k : W.DD T))) = DDinv W T ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) x ∈ W.NΔ T ↔ ∀ i, x i ∈ R.N0 r := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF hE hb hc
  obtain ⟨-, hFr, -⟩ := hF
  obtain ⟨hext, hinj, hEr, -⟩ := hE
  let c : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hc).basis b
  have hcb : ∀ k, c k = (b k : W.DD T) := fun k => IsBaseChange.basis_apply b (W.N_base T hc) k
  have huniq : ∀ y y' : Fin r → W.EE,
      ∑ k, y k • (b k : W.DD T) = ∑ k, y' k • (b k : W.DD T) → y = y' := by
    intro y y' h
    apply c.equivFun.symm.injective
    simp only [Module.Basis.equivFun_symm_apply, hcb]
    exact h
  have hex : ∀ m : W.DD T, ∃ y : Fin r → W.EE, ∑ k, y k • (b k : W.DD T) = m := by
    intro m
    refine ⟨c.repr m, ?_⟩
    simp only [← hcb]
    exact c.sum_repr m
  have hγ : ∀ δ ∈ W.DelF, ∀ y : Fin r → W.EE, W.γD T δ (∑ k, y k • (b k : W.DD T)) =
      ∑ k, W.γE δ (y k) • (b k : W.DD T) := by
    intro δ hδ y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.γD_smul, (hb k).2 δ hδ]
  have hinv : ∀ x, ∀ δ ∈ W.DelF, W.γD T δ (coord W R jE T (fun k => (b k : W.DD T)) x) =
      coord W R jE T (fun k => (b k : W.DD T)) x := by
    intro x δ hδ
    rw [coord_apply, hγ δ hδ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hEr _).1 ⟨_, rfl⟩ δ hδ]
  refine ⟨?_, ?_, ?_⟩
  · intro x x' h
    have := huniq _ _ h
    funext i k
    exact congrFun (hinj (congrFun this k)) i
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hinv x
    · intro m hm
      obtain ⟨y, rfl⟩ := hex m
      have hy : ∀ k, ∃ x, jE x = y k := fun k => (hEr _).2 fun δ hδ =>
        congrFun (huniq _ _ ((hγ δ hδ y).symm.trans (hm δ hδ))) k
      choose x hx using hy
      refine ⟨fun i k => x k i, ?_⟩
      rw [coord_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hx k]
  · intro x
    constructor
    · rintro ⟨hN, -⟩
      set a := b.repr ⟨_, hN⟩ with ha
      have h1 : ∑ k, algebraMap (LetA O n) W.EE (a k) • (b k : W.DD T) =
          ∑ k, jE (fun i => x i k) • (b k : W.DD T) := by
        have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hN⟩)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at this
        simp only [algebraMap_smul]
        exact this
      have h2 := huniq _ _ h1
      intro i k _
      have h3 : algebraMap (LetA O n) W.EE (a k) = jE (fun i => x i k) := congrFun h2 k
      have h4 : ∀ i', ∃ a', j a' = a k i' := fun i' => (hFr _).2 fun δ hδ => by
        have h5 := (hEr _).1 ⟨_, h3.symm⟩ δ hδ
        rw [W.γE_ext] at h5
        exact congrFun (W.EE_inj h5) i'
      choose a' ha' using h4
      have h6 : jE (fun i => R.ι (a' i)) = jE (fun i => x i k) := by
        rw [hext, ← h3]
        congr 1
        funext i'
        exact ha' i'
      exact ⟨a' i, congrFun (hinj h6) i⟩
    · intro hx
      refine ⟨?_, hinv x⟩
      rw [coord_apply]
      refine Submodule.sum_mem _ fun k _ => ?_
      have h4 : ∀ i, ∃ a', R.ι a' = x i k := fun i => hx i k (Set.mem_univ _)
      choose a' ha' using h4
      have : (fun i => x i k) = fun i => R.ι (a' i) := funext fun i => (ha' i).symm
      rw [this, hext, algebraMap_smul]
      exact (W.N T).smul_mem _ (b k).2

end GlobalTheory.WachTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPsiKPreservesTestFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPsiKPreservesTestFunctions
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp.PtTest

theorem hasCompactSupport_of_loc {X : Type} [TopologicalSpace X] (g : X → ℂ) (hg : IsLocallyConstant g)
    (C : Set X) (hC : IsCompact C) (hz : ∀ x ∉ C, g x = 0) : HasCompactSupport g := by
  have hcl : IsClosed (Function.support g) := by
    have := (hg.isOpen_fiber 0).isClosed_compl
    convert this using 1
    ext; simp [Function.mem_support]
  show IsCompact (closure (Function.support g))
  rw [hcl.closure_eq]
  exact hC.of_isClosed_subset hcl fun x hx => by
    by_contra h
    exact hx (hz x h)

theorem slice_eventually {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : ∀ᶠ a' in 𝓝 a, (fun b => Φ (a', b)) = fun b => Φ (a, b) := by
  have hC : IsCompact (Prod.snd '' tsupport Φ) := hΦ.2.isCompact.image continuous_snd
  have h := hC.eventually_forall_of_forall_eventually (x₀ := a) (P := fun a' b => Φ (a', b) = Φ (a, b))
    fun y _ => by
      have h1 : ∀ᶠ z in 𝓝 (a, y), Φ z = Φ (a, y) := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 (a, y)
      have hc : Continuous fun z : X × Y => (a, z.2) := continuous_const.prodMk continuous_snd
      have h2 : ∀ᶠ z in 𝓝 (a, y), Φ (a, z.2) = Φ (a, y) :=
        (hc.tendsto (a, y)).eventually ((IsLocallyConstant.iff_eventually_eq Φ).1 hΦ.1 (a, y))
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
  filter_upwards [h] with a' ha'
  funext b
  by_cases hb : b ∈ Prod.snd '' tsupport Φ
  · exact ha' b hb
  · have h0 : ∀ c, Φ (c, b) = 0 := fun c => by
      by_contra hne
      exact hb ⟨(c, b), subset_tsupport _ hne, rfl⟩
    rw [h0, h0]

theorem slice_isTest {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (Φ : X × Y → ℂ) (hΦ : IsTest Φ)
    (a : X) : IsTest fun b => Φ (a, b) := by
  have hl : IsLocallyConstant fun b => Φ (a, b) :=
    hΦ.1.comp_continuous (continuous_const.prodMk continuous_id)
  refine ⟨hl, hasCompactSupport_of_loc _ hl _ (hΦ.2.isCompact.image continuous_snd) fun b hb => ?_⟩
  by_contra hne
  exact hb ⟨(a, b), subset_tsupport _ hne, rfl⟩

end GlobalTheory.JR.Hyp.PtTest


open GlobalTheory.JR.Hyp.PtTest in
theorem GlobalTheory.JR.Hyp.pt_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ) := by
  intro F E _ _ _ _ _ A ψ hψ x ν hν Φ hΦ

  let β : LinearMap.BilinForm F A.K := LinearMap.comp (Algebra.traceForm F A.K) (LinearMap.mulLeft F (x : A.K))
  have hβapp : ∀ u b, β u b = Algebra.trace F A.K ((x : A.K) * u * b) := fun u b => by simp [β, Algebra.traceForm_apply, mul_assoc]
  have hsymm : β.IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [RingHom.id_apply, hβapp]
    ring_nf
  have htr := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  have hsepL : ∀ u : A.K, (∀ b, β u b = 0) → u = 0 := fun u hu => by
    have h1 : (x : A.K) * u = 0 := htr.1 _ fun b => by simpa [hβapp] using hu b
    simpa using congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h1
  have hnd : β.Nondegenerate := ⟨hsepL, fun b hb => hsepL b fun u => by
    have := hb u
    rw [hβapp] at this
    rw [hβapp, mul_right_comm]; exact this⟩
  have hF : ∀ f : A.K → ℂ, IsTest f → IsTest (fourB ν (kx A ψ (x : A.K)) f) := fun f hf =>
    (GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K β hsymm hnd).2 ν hν f hf
  have hG : ∀ p, Hyp.pt A ν ψ x Φ p = fourB ν (kx A ψ (x : A.K)) (fun b => Φ (p.1, b)) p.2 := fun p => rfl
  have hloc : IsLocallyConstant (Hyp.pt A ν ψ x Φ) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨a, u⟩
    have h1 := slice_eventually Φ hΦ a
    have h2 := (IsLocallyConstant.iff_eventually_eq _).1 (hF _ (slice_isTest Φ hΦ a)).1 u
    rw [nhds_prod_eq]
    filter_upwards [h1.prod_mk h2] with q hq
    rw [hG, hG, hq.1]
    exact hq.2
  refine ⟨hloc, ?_⟩
  have hC1 : IsCompact (Prod.fst '' tsupport Φ) := hΦ.2.isCompact.image continuous_fst
  obtain ⟨t, -, ht⟩ := hC1.elim_nhds_subcover (fun a => {a' | (fun b => Φ (a', b)) = fun b => Φ (a, b)})
    fun a _ => slice_eventually Φ hΦ a
  refine hasCompactSupport_of_loc _ hloc
    ((Prod.fst '' tsupport Φ) ×ˢ ⋃ i ∈ t, tsupport (fourB ν (kx A ψ (x : A.K)) fun b => Φ (i, b)))
    (hC1.prod (t.isCompact_biUnion fun i _ => (hF _ (slice_isTest Φ hΦ i)).2.isCompact)) ?_
  rintro ⟨a, u⟩ hq
  by_contra hne
  apply hq
  have ha : a ∈ Prod.fst '' tsupport Φ := by
    by_contra ha
    apply hne
    have h0 : ∀ b, Φ (a, b) = 0 := fun b => by
      by_contra hb
      exact ha ⟨(a, b), subset_tsupport _ hb, rfl⟩
    simp [hG, fourB, h0]
  refine ⟨ha, ?_⟩
  obtain ⟨i, hi, hai⟩ := Set.mem_iUnion₂.1 (ht ha)
  refine Set.mem_iUnion₂.2 ⟨i, hi, subset_tsupport _ ?_⟩
  rw [hG] at hne
  simp only [Set.mem_setOf_eq] at hai
  rw [Function.mem_support]
  rwa [hai] at hne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPsiKPreservesTestFunctionsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourier_psiK_preserves_testFunctions : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (ν : Measure A.K), ν.IsAddHaarMeasure → ∀ Φ : A.K × A.K → ℂ, IsTest Φ → IsTest (Hyp.pt A ν ψ x Φ) := by
  first | exact @GlobalTheory.JR.Hyp.pt_isTest | exact GlobalTheory.JR.Hyp.pt_isTest | (intros; apply GlobalTheory.JR.Hyp.pt_isTest <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfSumSmul
noncomputable section

open PowerSeries GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

namespace GlobalTheory.WachTie

def Laur (L M : Type) [Field L] [AddCommGroup M] [Module L M] : Type := HahnModule ℤ L M

namespace Laur

variable {L M M' : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup M'] [Module L M']

instance : AddCommGroup (Laur L M) := inferInstanceAs (AddCommGroup (HahnModule ℤ L M))

instance : Module L⟦X⟧ (Laur L M) :=
  Module.compHom (HahnModule ℤ L M) (HahnSeries.ofPowerSeries ℤ L)

def co : Laur L M →+ (ℤ → M) where
  toFun x := ((HahnModule.of L).symm x).coeff
  map_zero' := rfl
  map_add' _ _ := rfl

theorem co_injective : Function.Injective (co : Laur L M → ℤ → M) := by
  intro x y h
  exact HahnModule.ext x y h

theorem isLaurent_co (x : Laur L M) : IsLaurent (co x) := by
  exact ⟨((HahnModule.of L).symm x).order, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩

def mk (u : ℤ → M) (hu : IsLaurent u) : Laur L M :=
  HahnModule.of L (HahnSeries.ofSuppBddBelow u (by
    obtain ⟨m, hm⟩ := hu
    exact ⟨m, fun k hk => not_lt.1 fun h => hk (hm k h)⟩))

private theorem coeff_ofPowerSeries_smul_eq_serMul (f : L⟦X⟧) (y : HahnModule ℤ L M) (k : ℤ) :
    ((HahnModule.of L).symm (HahnSeries.ofPowerSeries ℤ L f • y)).coeff k =
      serMul f ((HahnModule.of L).symm y).coeff k := by
  set F := HahnSeries.ofPowerSeries ℤ L f with hFdef
  have hF : ∀ j : ℕ, F.coeff (j : ℤ) = PowerSeries.coeff j f := fun j =>
    HahnSeries.ofPowerSeries_apply_coeff f j
  have hneg : ∀ i : ℤ, F.coeff i ≠ 0 → 0 ≤ i := by
    intro i hi
    by_contra hlt
    apply hi
    rw [hFdef, HahnSeries.ofPowerSeries_apply]
    apply HahnSeries.embDomain_notin_image_support
    rintro ⟨j, -, hj⟩
    change (j : ℤ) = i at hj
    omega
  have key : ∀ ij : ℤ × ℤ, F.coeff ij.1 ≠ 0 → ij.1 + ij.2 = k →
      ((ij.1.toNat : ℕ) : ℤ) = ij.1 ∧ k - ((ij.1.toNat : ℕ) : ℤ) = ij.2 := by
    intro ij h1 h3
    have := hneg _ h1
    constructor <;> omega
  have hlau : IsLaurent ((HahnModule.of L).symm y).coeff :=
    ⟨_, fun k hk => HahnSeries.coeff_eq_zero_of_lt_order hk⟩
  have hfin := serMul_finite f hlau k
  rw [HahnModule.coeff_smul]
  show _ = ∑ᶠ j : ℕ, PowerSeries.coeff j f • ((HahnModule.of L).symm y).coeff (k - (j : ℤ))
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by rw [Set.Finite.coe_toFinset])]
  apply Finset.sum_bij_ne_zero (fun ij _ _ => ij.1.toNat)
  · intro ij hij hne
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij
    obtain ⟨e1, e2⟩ := key ij hij.1 hij.2.2
    rw [Set.Finite.mem_toFinset, Function.mem_support, e2, ← hF, e1]
    exact hne
  · intro a ha _ b hb _ hab
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at ha hb
    obtain ⟨ea1, ea2⟩ := key a ha.1 ha.2.2
    obtain ⟨eb1, eb2⟩ := key b hb.1 hb.2.2
    apply Prod.ext <;> omega
  · intro j _ hne
    refine ⟨((j : ℤ), k - j), ?_, ?_, ?_⟩
    · simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add]
      refine ⟨?_, right_ne_zero_of_smul hne, by omega⟩
      rw [hF]
      exact left_ne_zero_of_smul hne
    · show F.coeff (j : ℤ) • ((HahnModule.of L).symm y).coeff (k - j) ≠ 0
      rw [hF]
      exact hne
    · show ((j : ℤ)).toNat = j
      simp
  · intro ij hij _
    simp only [Finset.mem_vaddAntidiagonal, HahnSeries.mem_support, vadd_eq_add] at hij
    obtain ⟨e1, e2⟩ := key ij hij.1 hij.2.2
    show F.coeff ij.1 • ((HahnModule.of L).symm y).coeff ij.2 =
      PowerSeries.coeff ij.1.toNat f • ((HahnModule.of L).symm y).coeff (k - (ij.1.toNat : ℤ))
    rw [e2, ← hF, e1]

theorem co_smul (f : L⟦X⟧) (x : Laur L M) : co (f • x) = serMul f (co x) := by
  funext k
  exact coeff_ofPowerSeries_smul_eq_serMul f x k

private theorem co_smul_add_eq_coeff_smul_co (f : L⟦X⟧) (x : Laur L M) (m : ℤ) (n : ℕ)
    (hf : ∀ j < n, PowerSeries.coeff j f = 0) (hx : ∀ k < m, co x k = 0) :
    co (f • x) (m + n) = PowerSeries.coeff n f • co x m := by
  rw [co_smul]
  show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (m + n - j) = _
  rw [finsum_eq_single _ n]
  · simp
  · intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hf j h, zero_smul]
    · rw [hx (m + n - j) (by omega), smul_zero]

theorem co_smul_low (f : L⟦X⟧) (x : Laur L M) (m : ℤ) (hx : ∀ k < m, co x k = 0) :
    (∀ k < m, co (f • x) k = 0) ∧ co (f • x) m = constantCoeff f • co x m := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [co_smul]
    show ∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j) = 0
    exact (finsum_congr fun j => by rw [hx (k - j) (by omega), smul_zero]).trans finsum_zero
  · have e := co_smul_add_eq_coeff_smul_co f x m 0 (fun j hj => absurd hj (Nat.not_lt_zero j)) hx
    simpa using e

def tw (c : L) (g : M →ₗ[L] M') : Laur L M →+ Laur L M' where
  toFun x := mk (fun k => c ^ k • g (co x k)) (by
    obtain ⟨m, hm⟩ := isLaurent_co x
    exact ⟨m, fun k hk => by simp [hm k hk]⟩)
  map_zero' := co_injective (by
    funext k
    simp
    rfl)
  map_add' x y := co_injective (by
    funext k
    simp
    rfl)

@[simp] theorem co_tw (c : L) (g : M →ₗ[L] M') (x : Laur L M) (k : ℤ) :
    co (tw c g x) k = c ^ k • g (co x k) := rfl

theorem tw_smul {c : L} (hc : c ≠ 0) (g : M →ₗ[L] M') (f : L⟦X⟧) (x : Laur L M) :
    tw c g (f • x) = rescale c f • tw c g x := by
  apply co_injective
  funext k
  rw [co_tw, co_smul, co_smul]
  show (c ^ k • g) (∑ᶠ j : ℕ, PowerSeries.coeff j f • co x (k - j)) =
    ∑ᶠ j : ℕ, PowerSeries.coeff j (rescale c f) • co (tw c g x) (k - j)
  rw [map_finsum (c ^ k • g) (serMul_finite f (isLaurent_co x) k)]
  refine finsum_congr fun j => ?_
  rw [LinearMap.smul_apply, map_smul, co_tw, PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show c ^ k = c ^ (j : ℤ) * c ^ (k - j) by rw [← zpow_add₀ hc, add_sub_cancel], zpow_natCast]
  ring

end Laur

end GlobalTheory.WachTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianTraceDualIntegersEqUniformizerPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianTraceDualIntegersEqUniformizerPow
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DualLattice

variable {R : Type} [CommRing R]

theorem eq_zpow_mul_unit (O : Subring R) (p : Rˣ)
    (hdich : ∀ y ∈ O, (∃ z ∈ O, y = (p : R) * z) ∨ ∃ z ∈ O, y * z = 1)
    (hsep : ∀ x : R, x ≠ 0 → ∃ n : ℕ, ∀ z ∈ O, (p : R) ^ n * z ≠ x)
    (hex : ∀ y : R, ∃ n : ℕ, (p : R) ^ n * y ∈ O) :
    ∀ y : R, y ≠ 0 → ∃ v : ℤ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ y = ((p ^ v : Rˣ) : R) * u := by
  classical
  have hO : ∀ x ∈ O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ x = (p : R) ^ k * u := by
    intro x hxO hx0
    have hex' : ∃ k : ℕ, ¬ ∃ z ∈ O, x = (p : R) ^ k * z := by
      obtain ⟨n, hn⟩ := hsep x hx0
      exact ⟨n, fun ⟨z, hz, hzx⟩ => hn z hz hzx.symm⟩
    obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, (¬ ∃ z ∈ O, x = (p : R) ^ m * z) ∧
        ∀ j < m, ∃ z ∈ O, x = (p : R) ^ j * z :=
      ⟨Nat.find hex', Nat.find_spec hex', fun j hj => by simpa using Nat.find_min hex' hj⟩
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hm ⟨x, hxO, by simp⟩
    obtain ⟨z, hz, hxz⟩ := hmin (m - 1) (by omega)
    rcases hdich z hz with ⟨w, hw, hzw⟩ | hu
    · exfalso
      apply hm
      refine ⟨w, hw, ?_⟩
      rw [hxz, hzw, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
    · exact ⟨_, z, hz, hu, hxz⟩
  intro y hy
  obtain ⟨n, hn⟩ := hex y
  have hne : (p : R) ^ n * y ≠ 0 := by
    intro h
    apply hy
    have := congrArg (fun t => ((p⁻¹ : Rˣ) : R) ^ n * t) h
    simpa [← mul_assoc, ← mul_pow] using this
  obtain ⟨k, u, hu, hunit, hk⟩ := hO _ hn hne
  refine ⟨(k : ℤ) - n, u, hu, hunit, ?_⟩
  have e1 : ((p ^ ((k : ℤ) - n) : Rˣ) : R) = ((p⁻¹ : Rˣ) : R) ^ n * (p : R) ^ k := by
    rw [_root_.zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, mul_comm]
  rw [e1, mul_assoc, ← hk, ← mul_assoc, ← mul_pow]
  simp

theorem eq_zpow_smul (O : Subring R) (p : Rˣ) (D : Set R) (hpO : (p : R) ∈ O)
    (hmul : ∀ y ∈ D, ∀ r ∈ O, r * y ∈ D)
    (hbig : ∃ n : ℕ, ∀ z ∈ O, (p : R) ^ n * z ∈ D)
    (hne : ∃ y, y ∉ D)
    (hex : ∀ y : R, ∃ n : ℕ, (p : R) ^ n * y ∈ O)
    (hunit : ∀ y : R, y ≠ 0 → ∃ v : ℤ, ∃ u ∈ O, (∃ w ∈ O, u * w = 1) ∧ y = ((p ^ v : Rˣ) : R) * u) :
    ∃ e : ℤ, D = {y | ∃ z ∈ O, y = ((p ^ e : Rˣ) : R) * z} := by
  classical
  have hup : ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D → ∀ k : ℕ, ((p ^ (v + k) : Rˣ) : R) ∈ D := by
    intro v hv k
    have : ((p ^ (v + k) : Rˣ) : R) = (p : R) ^ k * ((p ^ v : Rˣ) : R) := by
      rw [_root_.zpow_add, zpow_natCast, mul_comm, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [this]
    exact hmul _ hv _ (pow_mem hpO k)
  obtain ⟨n, hn⟩ := hbig
  have hinh : ∃ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D := ⟨n, by simpa using hn 1 (one_mem O)⟩
  have hbdd : ∃ b : ℤ, ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D → b ≤ v := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ v : ℤ, ((p ^ v : Rˣ) : R) ∈ D := by
      intro v
      obtain ⟨w, hw, hwv⟩ := hcon v
      have := hup w hw (v - w).toNat
      rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at this
    obtain ⟨y, hy⟩ := hne
    obtain ⟨m, hm⟩ := hex y
    apply hy
    have h1 := hmul _ (hall (-(m : ℤ))) _ hm
    have hq : ((p ^ (-(m : ℤ)) : Rˣ) : R) * (p : R) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add,
        neg_add_cancel, zpow_zero, Units.val_one]
    have h2 : (p : R) ^ m * y * ((p ^ (-(m : ℤ)) : Rˣ) : R) = y := by
      linear_combination y * hq
    rwa [h2] at h1
  obtain ⟨e, he, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
  refine ⟨e, Set.ext fun y => ⟨fun hy => ?_, fun ⟨z, hz, hyz⟩ => ?_⟩⟩
  · by_cases hy0 : y = 0
    · exact ⟨0, zero_mem O, by simp [hy0]⟩
    obtain ⟨v, u, hu, ⟨w, hw, huw⟩, hyv⟩ := hunit y hy0
    have hv : ((p ^ v : Rˣ) : R) ∈ D := by
      have := hmul y hy w hw
      have e2 : w * y = ((p ^ v : Rˣ) : R) := by rw [hyv, mul_comm, mul_assoc, huw, mul_one]
      rwa [e2] at this
    have hev := hmin v hv
    refine ⟨(p : R) ^ (v - e).toNat * u, O.mul_mem (pow_mem hpO _) hu, ?_⟩
    rw [hyv, ← mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← _root_.zpow_add,
      Int.toNat_of_nonneg (by omega), add_sub_cancel]
  · rw [hyz, mul_comm]
    exact hmul _ he _ hz

end GlobalTheory.JR.DualLattice

namespace GlobalTheory.JR.DualLattice


set_option maxHeartbeats 1000000 in
theorem dual_eq_zpow : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → IsField A.L → ∀ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) → (∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O) → ∀ a : A.Kˣ, ∃ e : ℤ, {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((ϖ ^ e : A.Kˣ) : A.K) * z} := by
  intro F E _ _ _ _ U A ψ hψ hK hL ϖ O hOo hOc hOstar hpO hpnu hdich hnbhd hex a
  have := U.charZero; have := U.ultraF; have := U.lcF
  have := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hLnt : Nontrivial A.L := ⟨hL.exists_pair_ne⟩
  have hKnt : Nontrivial A.K := ⟨hK.exists_pair_ne⟩
  let p : A.Lˣ := Units.map (algebraMap A.K A.L).toMonoidHom ϖ
  have hp : (p : A.L) = algebraMap A.K A.L (ϖ : A.K) := rfl
  have hpz : ∀ v : ℤ, ((p ^ v : A.Lˣ) : A.L) = algebraMap A.K A.L ((ϖ ^ v : A.Kˣ) : A.K) := by
    intro v
    rw [show p ^ v = Units.map (algebraMap A.K A.L).toMonoidHom (ϖ ^ v) from (map_zpow _ ϖ v).symm]
    rfl
  have hpn : ∀ n : ℕ, (p : A.L) ^ n = algebraMap A.K A.L ((ϖ : A.K) ^ n) := by
    intro n; rw [hp, map_pow]

  have hmul : ∀ y ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1}, ∀ r ∈ O,
      r * y ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    intro y hy r hr m hm
    have e1 : star (r * y) * m = star y * (star r * m) := by rw [star_mul']; ring
    simp only [Et.kerL, Set.mem_setOf_eq] at hy ⊢
    rw [e1]
    exact hy _ (O.mul_mem (hOstar r hr) hm)

  have hψl : IsLocallyConstant (fun x => ψ x) := ((GlobalTheory.StdChar.psi_conductor F E).2 ψ hψ).1
  have hg : Continuous (fun q : A.L × A.L =>
      Algebra.trace F A.K ((a : A.K) * Algebra.trace A.K A.L (star q.1 * q.2))) := by
    have hs : Continuous (star : A.L → A.L) := IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)
    have ht : Continuous (Algebra.trace A.K A.L) :=
      IsModuleTopology.continuous_of_linearMap ((Algebra.trace A.K A.L).restrictScalars F)
    have htF : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap (Algebra.trace F A.K)
    exact htF.comp (continuous_const.mul (ht.comp ((hs.comp continuous_fst).mul continuous_snd)))
  have hW : IsOpen {q : A.L × A.L | A.kerL ψ (a : A.K) q.1 q.2 = 1} :=
    (hψl.isOpen_fiber 1).preimage hg
  obtain ⟨u, v, hu, -, h0u, hOv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := (0 : A.L))) hOc hW
    (by
      rintro ⟨y, m⟩ ⟨hy, -⟩
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      simp [Et.kerL, Et.psiK])
  obtain ⟨n, hn⟩ := hnbhd u (hu.mem_nhds (h0u rfl))
  have hbig : ∃ n : ℕ, ∀ z ∈ O, (p : A.L) ^ n * z ∈ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    refine ⟨n, fun z hz m hm => ?_⟩
    have : ((p : A.L) ^ n * z, m) ∈ u ×ˢ v := ⟨by rw [hpn]; exact hn z hz, hOv hm⟩
    exact huv this

  have hinj : ∀ k₁ k₂ : A.K, algebraMap A.K A.L k₁ = algebraMap A.K A.L k₂ → k₁ = k₂ := by
    intro k₁ k₂ h
    by_contra hne
    obtain ⟨k', hk'⟩ := hK.mul_inv_cancel (sub_ne_zero.2 hne)
    have : algebraMap A.K A.L ((k₁ - k₂) * k') = 0 := by rw [map_mul, map_sub, h, sub_self, zero_mul]
    rw [hk', map_one] at this
    exact one_ne_zero this
  have hne : ∃ y, y ∉ {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} := by
    obtain ⟨-, x, hx, -⟩ := hψ
    have hd : (Module.finrank F A.K : F) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    set t : F := x / (2 * (Module.finrank F A.K : F)) with ht
    set c : A.K := ((a⁻¹ : A.Kˣ) : A.K) * algebraMap F A.K t with hc
    refine ⟨algebraMap A.K A.L c, fun h => hx ?_⟩
    have h1 := h 1 (one_mem O)
    have htr : Algebra.trace A.K A.L (star (algebraMap A.K A.L c) * 1) = 2 * c := by
      apply hinj
      rw [mul_one, A.star_K, (GlobalTheory.JR.EtFacts.main F E A).2.1, A.star_K, two_mul, map_add (f := _)]
    have hac : (a : A.K) * (2 * c) = algebraMap F A.K (2 * t) := by
      rw [hc, map_mul, map_ofNat, ← mul_assoc, mul_comm (a : A.K) 2, mul_assoc 2, ← mul_assoc (a : A.K),
        Units.mul_inv, one_mul]
    simp only [Et.kerL, Et.psiK, htr, hac, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
    rw [← h1, ht]
    congr 1
    field_simp

  have hsep : ∀ x : A.L, x ≠ 0 → ∃ n : ℕ, ∀ z ∈ O, (p : A.L) ^ n * z ≠ x := by
    intro x hx
    obtain ⟨n, hn⟩ := hnbhd {x}ᶜ (isOpen_compl_singleton.mem_nhds (Ne.symm hx))
    exact ⟨n, fun z hz => by rw [hpn]; exact hn z hz⟩
  have hex' : ∀ y : A.L, ∃ n : ℕ, (p : A.L) ^ n * y ∈ O := by
    intro y
    obtain ⟨n, hn⟩ := hex y
    exact ⟨n, by rw [hpn]; exact hn⟩
  have hdich' : ∀ y ∈ O, (∃ z ∈ O, y = (p : A.L) * z) ∨ ∃ z ∈ O, y * z = 1 := by
    rw [hp]; exact hdich
  have hunit := eq_zpow_mul_unit O p hdich' hsep hex'
  obtain ⟨e, he⟩ := eq_zpow_smul O p _ (by rw [hp]; exact hpO) hmul hbig hne hex' hunit
  refine ⟨e, ?_⟩
  rw [he]
  simp only [hpz]

end GlobalTheory.JR.DualLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianTraceDualIntegersEqUniformizerPowStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTraceDual_integers_eq_uniformizer_pow : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → IsField A.K → IsField A.L → ∀ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) → IsCompact (O : Set A.L) → (∀ y ∈ O, star y ∈ O) → algebraMap A.K A.L (ϖ : A.K) ∈ O → (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) → (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) → (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) → (∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O) → ∀ a : A.Kˣ, ∃ e : ℤ, {y : A.L | ∀ m ∈ O, A.kerL ψ (a : A.K) y m = 1} = {y : A.L | ∃ z ∈ O, y = algebraMap A.K A.L ((ϖ ^ e : A.Kˣ) : A.K) * z} := by
  first | exact @GlobalTheory.JR.DualLattice.dual_eq_zpow | exact GlobalTheory.JR.DualLattice.dual_eq_zpow | (intros; apply GlobalTheory.JR.DualLattice.dual_eq_zpow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismTensorEquiv
noncomputable section

namespace GlobalTheory.FontCmp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Tools

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']


variable (LL) in
def mB (b : B) : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

@[simp] theorem mB_tmul (b b' : B) (v : V) : mB (LL := LL) b (v ⊗ₜ[Qp] b') = v ⊗ₜ[Qp] (b * b') := by
  simp [mB]

theorem mulVB_eq (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (LL := LL) c x = mB (LL := LL) (algebraMap K₀ B c) x := rfl

theorem mB_mul (b b' : B) (x : V ⊗[Qp] B) : mB (LL := LL) (b * b') x = mB (LL := LL) b (mB (LL := LL) b' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [mul_assoc]
  | add a c ha hc => simp only [map_add (f := _), ha, hc]

theorem mB_add (b b' : B) (x : V ⊗[Qp] B) : mB (LL := LL) (b + b') x = mB (LL := LL) b x + mB (LL := LL) b' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [add_mul, tmul_add]
  | add a c ha hc => simp only [map_add (f := _), ha, hc]; abel

theorem mB_one (x : V ⊗[Qp] B) : mB (LL := LL) (1 : B) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add a c ha hc => simp only [map_add (f := _), ha, hc]

theorem comm_smulB (b : B) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (b • x) = mB (LL := LL) b (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp [TensorProduct.smul_tmul']
  | add a c ha hc => simp only [smul_add, map_add (f := _), ha, hc]

def mK (ρ : Representation LL G V) (c : K₀) : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρ) :=
  (mB (LL := LL) (algebraMap K₀ B c)).restrict (fun x hx => by
    rw [CrystallineSubrepresentation.mem_Dcris] at hx ⊢
    intro g
    rw [← mulVB_eq, CrystallineSubrepresentation.actVB_mulVB, hx])

theorem cmp_ind {ρ : Representation LL G V} (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    {P : V ⊗[Qp] B → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hb : ∀ (b : B) (d : ↥(Dcris PD ρ)), P (mB (LL := LL) b d)) (x : V ⊗[Qp] B) : P x := by
  obtain ⟨u, hu⟩ := h.2 ((TensorProduct.comm Qp B V).symm x)
  have : x = TensorProduct.comm Qp B V (CrystallineSubrepresentation.comparison PD ρ u) := by rw [hu]; simp
  subst this
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul b d =>
    rw [CrystallineSubrepresentation.comparison_tmul, comm_smulB (LL := LL)]
    exact hb b ⟨_, d.2⟩
  | add a c ha hc => simpa only [map_add (f := _)] using hadd _ _ ha hc

include PD in
theorem exists_retr : ∃ lam : B →ₗ[K₀] K₀, lam 1 = 1 := by
  have : (1 : B) ≠ 0 := by
    intro h
    apply PD.not_mem_filtration_two
    rw [← mul_one PD.t, h, mul_zero, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K₀ this
  exact ⟨(f 1)⁻¹ • f, by simp [hf]⟩

theorem prod_mB_left (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (mB (LL := LL) b x ⊗ₜ[LL] y) = mB (LL := LL) b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add (f := _), add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add (f := _), tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_assoc]

theorem prod_mB_right (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] mB (LL := LL) b y) = mB (LL := LL) b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add (f := _), add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add (f := _), tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_left_comm]

theorem act_prod (ρ : Representation LL G V) (ρ' : Representation LL G V') (g : G)
    (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    actVB PD (ρ.tprod ρ') g (CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] y)) =
      CrystallineSubrepresentation.prodB (actVB PD ρ g x ⊗ₜ[LL] actVB PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add (f := _), add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add (f := _), tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, actVB]

theorem prod_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (x : ↥(Dcris PD ρ)) (y : ↥(Dcris PD ρ')) :
    CrystallineSubrepresentation.prodB (LL := LL) ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B)) ∈ Dcris PD (ρ.tprod ρ') := by
  rw [CrystallineSubrepresentation.mem_Dcris]
  intro g
  rw [act_prod, (CrystallineSubrepresentation.mem_Dcris PD ρ x).1 x.2, (CrystallineSubrepresentation.mem_Dcris PD ρ' y).1 y.2]

theorem unit_eq : Dcris PD (Representation.trivial LL G LL) =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  obtain ⟨lam, hl⟩ := exists_retr PD
  ext x
  rw [CrystallineSubrepresentation.mem_Dcris]
  constructor
  · intro hx

    let ctr : (LL →ₗ[Qp] Qp) → (LL ⊗[Qp] B →ₗ[Qp] B) := fun f =>
      (TensorProduct.lid Qp B).toLinearMap ∘ₗ LinearMap.rTensor B f
    have hc : ∀ f g y, ctr f (actVB PD (Representation.trivial LL G LL) g y) =
        PD.actB g (ctr f y) := by
      intro f g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add (f := _), ha, hc]
      | tmul a b =>
        simp only [ctr, actVB]
        simp
        rw [← IsScalarTower.algebraMap_smul K₀ (f a) b, map_smul, IsScalarTower.algebraMap_smul]
    let r : B →ₗ[Qp] K₀ := lam.restrictScalars Qp
    let j : K₀ →ₗ[Qp] B := (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap
    have hr : ∀ f y, ctr f (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) j
        (LinearMap.lTensor LL r y)) = j (r (ctr f y)) := by
      intro f y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add (f := _), ha, hc]
      | tmul a b => simp [ctr]
    have hsep : ∀ y : LL ⊗[Qp] B, (∀ f, ctr f y = 0) → y = 0 := by
      intro y hy
      classical
      let bs := Module.Free.chooseBasis Qp LL
      apply (TensorProduct.comm Qp LL B).injective
      apply (TensorProduct.equivFinsuppOfBasisRight bs).injective
      ext i
      have : ∀ y : LL ⊗[Qp] B, TensorProduct.equivFinsuppOfBasisRight bs
          (TensorProduct.comm Qp LL B y) i = ctr (bs.coord i) y := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]
        | tmul a b => simp [ctr]
      simp [this, hy]
    refine ⟨LinearMap.lTensor LL r x, ?_⟩
    rw [← sub_eq_zero]
    apply hsep
    intro f
    rw [map_sub, hr]
    obtain ⟨c, hc'⟩ := PD.invB (ctr f x) (fun g => by rw [← hc, hx])
    rw [← hc', sub_eq_zero]
    change algebraMap K₀ B (lam (algebraMap K₀ B c)) = _
    rw [Algebra.algebraMap_eq_smul_one c, map_smul, hl]
    simp [Algebra.algebraMap_eq_smul_one]
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add (f := _), ha, hc]
    | tmul a b => simp [actVB]


theorem mem_DcrisL (ρ : Representation LL G V) (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ x ∈ Dcris PD ρ ∧ ∀ c : K₀, mB (LL := LL) (algebraMap K₀ B c) x = τ c • x := by
  simp [DcrisL, Submodule.mem_iInf, sub_eq_zero, mulVB_eq]

end Tools

variable (LL : Type) [Field LL] [Algebra Qp LL]

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

end GlobalTheory.FontCmp
end
end
