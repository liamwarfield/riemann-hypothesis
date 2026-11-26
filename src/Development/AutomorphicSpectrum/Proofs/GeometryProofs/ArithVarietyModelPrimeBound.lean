module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeDegree
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.NatAbsDiscrMemDifferent
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.VectorBundleLatticeLabels

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.DualLatticeFamily
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.DualLatticeFamily

theorem mem_dotDual {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) {r : ℕ}
    (L : AddSubgroup (Fin r → Ω)) (e : Fin r → Ω) :
    e ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ e ∈ R := by
  unfold GlobalTheory.CompanionTheory.Ar.Num.dotDual
  simp only [AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

noncomputable def dotB (Ω : Type) [Field Ω] (r : ℕ) : (Fin r → Ω) →ₗ[Ω] (Fin r → Ω) →ₗ[Ω] Ω :=
  LinearMap.mk₂ Ω (fun a b => a ⬝ᵥ b) (fun a a' b => add_dotProduct a a' b)
    (fun c a b => smul_dotProduct c a b) (fun a b b' => dotProduct_add a b b')
    (fun c a b => dotProduct_smul c a b)

theorem dotB_apply {Ω : Type} [Field Ω] {r : ℕ} (a b : Fin r → Ω) : dotB Ω r a b = a ⬝ᵥ b := rfl

theorem dotB_bij (Ω : Type) [Field Ω] (r : ℕ) : Function.Bijective (dotB Ω r).flip := by
  classical
  refine ⟨fun a b h => funext fun i => ?_, fun ψ => ⟨fun i => ψ (Pi.single i 1), ?_⟩⟩
  · have := LinearMap.congr_fun h (Pi.single i 1)
    simpa [dotB_apply] using this
  · refine LinearMap.pi_ext fun i x => ?_
    have hx : (Pi.single i x : Fin r → Ω) = x • (Pi.single i 1 : Fin r → Ω) := by
      rw [← Pi.single_smul, smul_eq_mul, _root_.mul_one]
    rw [LinearMap.flip_apply, dotB_apply, single_dotProduct, hx, map_smul, smul_eq_mul]

theorem overlap {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] {T : Type} (x : T → Ω) {r : ℕ}
    (i j : T) (hi : x i ≠ 0) (hj : x j ≠ 0) (Li Lj : AddSubgroup (Fin r → Ω))
    (hov : ∀ e ∈ Lj, ∃ m : ℕ, (x j / x i) ^ m • e ∈ Li) (hL : LocFree (chartRing O x j) r Lj)
    (w : Fin r → Ω) (hw : w ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual (chartRing O x i) Li) :
    ∃ m : ℕ, (x i / x j) ^ m • w ∈ GlobalTheory.CompanionTheory.Ar.Num.dotDual (chartRing O x j) Lj := by
  rw [mem_dotDual] at hw
  have hdiv : x i / x j ∈ chartRing O x j := ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing x j i
  obtain ⟨m, hm⟩ := GlobalTheory.CompanionTheory.Ar.Num.Reflexive.exists_uniform_denominator (chartRing O x j) r Lj hL
    (x i / x j) hdiv ((dotB Ω r).flip w) fun e he => by
      obtain ⟨m, hm⟩ := hov e he
      have h1 := hw _ hm
      rw [smul_dotProduct, smul_eq_mul] at h1
      obtain ⟨m', hm'⟩ : ∃ m' : ℕ, (x i / x j) ^ m' * ((x j / x i) ^ m * (e ⬝ᵥ w)) ∈ chartRing O x j :=
        ReciprocityTheory.ChartRestriction.G.Geo.exists_pow_mul_mem_chartRing x i j hi h1
      have hone : (x i / x j) ^ m * (x j / x i) ^ m = 1 := by
        rw [← mul_pow, div_mul_div_comm, _root_.mul_comm (x i), div_self (mul_ne_zero hj hi), one_pow]
      have h2 := mul_mem (pow_mem hdiv m) hm'
      have h3 : (x i / x j) ^ m * ((x i / x j) ^ m' * ((x j / x i) ^ m * (e ⬝ᵥ w))) =
          (x i / x j) ^ m' * (e ⬝ᵥ w) := by
        calc _ = (x i / x j) ^ m' * (e ⬝ᵥ w) * ((x i / x j) ^ m * (x j / x i) ^ m) := by ring
          _ = _ := by rw [hone, _root_.mul_one]
      rw [h3] at h2
      exact ⟨m', h2⟩
  refine ⟨m, (mem_dotDual _ _ _).2 fun l hl => ?_⟩
  rw [dotProduct_smul, smul_eq_mul]
  exact hm l hl

end PositivityTheory.Xgn.DualLatticeFamily

open PositivityTheory.Xgn.DualLatticeFamily in
theorem PositivityTheory.Xgn.dual_lattice_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) := by
  intro O _ Ω _ _ K _ J _ y r Γ hΓ hL
  refine ⟨⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩, fun c hc => ?_⟩
  · refine (mem_dotDual _ _ _).2 fun l hl => ?_
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha ((mem_dotDual _ _ _).1 hw l hl)
  · exact overlap (mseg y) s t hs ht (Γ s) (Γ t) (hΓ.2 t s ht hs) (hL t ht) w hw
  · exact (GlobalTheory.CompanionTheory.Ar.Num.DualLattice.locFree_dual _ (dotB Ω r) (dotB_bij Ω r) r (Γ c) _ (hL c hc)
      fun w => mem_dotDual _ _ w).1
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LatticeChartPoints
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.LatticeChartPoints

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}

theorem int_le (O : Type) [CommRing O] [Algebra O Ω] (S : Set Ω) {a : Ω} (ha : a ∈ Algebra.adjoin ℤ S) :
    a ∈ Algebra.adjoin O S := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap n =>
    have : algebraMap ℤ Ω n = algebraMap O Ω (n : O) := by simp
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem unitAt_mul_iff {q : Cpt ξ} {a s : Ω} (ha : unitAt ξ q a) : unitAt ξ q (a * s) ↔ unitAt ξ q s := by
  obtain ⟨h0, h1, h2⟩ := ha
  constructor
  · rintro ⟨k0, k1, k2⟩
    have hs : s ≠ 0 := right_ne_zero_of_mul k0
    refine ⟨hs, ?_, ?_⟩
    · have : s = a⁻¹ * (a * s) := by field_simp
      rw [this]; exact mul_mem h2 k1
    · have : s⁻¹ = a * (a * s)⁻¹ := by field_simp
      rw [this]; exact mul_mem h1 k2
  · rintro ⟨k0, k1, k2⟩
    refine ⟨mul_ne_zero h0 k0, mul_mem h1 k1, ?_⟩
    rw [mul_inv]; exact mul_mem h2 k2

theorem reg (O : Type) [CommRing O] [Algebra O Ω] (x : κ → Ω) (c : κ) (a : Ω)
    (ha : a ∈ Algebra.adjoin O (Set.range fun j => x j / x c)) (q : Cpt ξ) (hq : InChart ξ x c q)
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) : a ∈ regAt ξ q := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hq.2 j
  | algebraMap o => exact hO o
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_incl {O : Type} [CommRing O] [Algebra O Ω] (B : Subalgebra ℤ Ω) (R : Subalgebra O Ω)
    (h : ∀ a ∈ B, a ∈ R) : ∃ φ : B →+* R, ∀ t : B, ((φ t : R) : Ω) = t :=
  ⟨{ toFun := fun t => ⟨t.1, h _ t.2⟩
     map_one' := Subtype.ext rfl
     map_mul' := fun _ _ => Subtype.ext rfl
     map_zero' := Subtype.ext rfl
     map_add' := fun _ _ => Subtype.ext rfl }, fun _ => rfl⟩

theorem point_of_prime (C : Cpt ξ → Prop)
    (A : Type) [CommRing A] [Algebra A Ω] (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O]
    [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (B : Subalgebra ℤ Ω) (R : Subalgebra O Ω) (hle : ∀ a ∈ B, a ∈ R)
    (hpt : ∀ I : Ideal B, I.IsPrime → ∃ q, C q ∧ ∀ s : B, s ∉ I ↔ unitAt ξ q (s : Ω))
    (hreg : ∀ a ∈ B, ∀ q, C q → a ∈ regAt ξ q)
    (hconst : ∀ a : A, algebraMap A Ω a ∈ B)
    (hloc : ∀ t ∈ R, ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ B)
    (P : Ideal R) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, C q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧
      ∀ s : R, s ∉ P ↔ unitAt ξ q (s : Ω) := by
  obtain ⟨φ, hφ⟩ := exists_incl B R hle
  obtain ⟨q, hq, hI⟩ := hpt (P.comap φ) (Ideal.comap_isPrime φ P)
  have hAO : ∀ a : A, algebraMap A Ω a = algebraMap O Ω (algebraMap A O a) := fun a =>
    IsScalarTower.algebraMap_apply A O Ω a
  have hnot : ∀ a : A, a ∉ m → φ ⟨_, hconst a⟩ ∉ P := by
    intro a ha hmem
    have hu : IsUnit (algebraMap A O a) := IsLocalization.map_units O (⟨a, ha⟩ : m.primeCompl)
    have he : φ ⟨_, hconst a⟩ = algebraMap O R (algebraMap A O a) :=
      Subtype.ext ((hφ _).trans (hAO a))
    rw [he] at hmem
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem (hu.map _))
  have hunit : ∀ a : A, a ∉ m → unitAt ξ q (algebraMap A Ω a) := fun a ha =>
    (hI ⟨_, hconst a⟩).1 (fun h => hnot a ha (Ideal.mem_comap.1 h))
  refine ⟨q, hq, fun o => ?_, fun s => ?_⟩
  · obtain ⟨a, ha, hb⟩ := hloc _ (R.algebraMap_mem o)
    obtain ⟨h0, -, h2⟩ := hunit a ha
    have : algebraMap O Ω o = (algebraMap A Ω a)⁻¹ * (algebraMap A Ω a * algebraMap O Ω o) := by
      rw [← _root_.mul_assoc, inv_mul_cancel₀ h0, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (hreg _ hb q hq)
  · obtain ⟨a, ha, hb⟩ := hloc s s.2
    refine Iff.trans ?_ ((hI ⟨_, hb⟩).trans (unitAt_mul_iff (hunit a ha)))
    have he : φ ⟨_, hb⟩ = φ ⟨_, hconst a⟩ * s := Subtype.ext (by
      rw [hφ, MulMemClass.coe_mul, hφ])
    rw [Ideal.mem_comap, he, hP.mul_mem_iff_mem_or_mem]
    exact ⟨fun h h' => h'.elim (hnot a ha) h, fun h h' => h (Or.inr h')⟩

open GlobalTheory.CompanionTheory.Ar.ChartPrimes in
theorem basic_nbhd (x : κ → Ω) (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0) (q : Cpt ξ) (hq : InChart ξ x c q)
    (U : X.Opens) (hU : q.1 ∈ U) : ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), unitAt ξ q g ∧
      ∀ q' : Cpt ξ, InChart ξ x c q' → unitAt ξ q' g → q'.1 ∈ U := by
  obtain ⟨V, hV, hmem⟩ := T.affine c hc
  have hqV : q.1 ∈ V := (hmem _).2 ⟨q.2, hq⟩
  have hg : genPt ξ ∈ V := q.2.mem_open V.2 hqV
  obtain ⟨f, hfU, hqf⟩ := hV.exists_basicOpen_le ⟨q.1, hU⟩ hqV
  have key : ∀ (p : Cpt ξ), p.1 ∈ V → (p.1 ∈ X.basicOpen f ↔ unitAt ξ p (secVal ξ V hg f)) := fun p hp => by
    rw [X.mem_basicOpen f _ hp, ← genMap_germ_eq V hg p hp f]
    exact isUnit_iff_unitAt p (T.gen.inj _) _
  refine ⟨secVal ξ V hg f, (T.ring c hc _).2 fun p hp => ⟨_, genMap_germ_eq V hg p ((hmem _).2 ⟨p.2, hp⟩) f⟩,
    (key q hqV).1 hqf, fun q' hq' hu => hfU ((key q' ((hmem _).2 ⟨q'.2, hq'⟩)).2 hu)⟩

end PositivityTheory.Xgn.LatticeChartPoints

open PositivityTheory.Xgn.LatticeChartPoints in
theorem PositivityTheory.Xgn.lattice_chart_points : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) := by
  intro X Ω _ ξ K _ _ J _ y T A _ _ hA m _ O _ _ _ _ _ _ _ c hc
  refine ⟨fun a ha q hq hO => reg O (mseg y) c a ha q hq hO, fun P hP => ?_, fun q hq _ a ha => ?_,
    fun q hq _ U hU => ?_⟩
  · exact point_of_prime (InChart ξ (mseg y) c) A m O (Algebra.adjoin ℤ (Set.range fun j => mseg y j / mseg y c)) _
      (fun a ha => int_le O _ ha)
      (fun I hI => (chart_point_of_prime X Ω ξ ℤ _ (mseg y) T c hc I hI).exists)
      (fun a ha => (T.ring c hc a).1 ha) (hA c hc)
      (fun t ht => (mem_chartRing_atPrime_iff K J Ω y A hA m O c hc t).1 ht) P hP
  · obtain ⟨s, hs, hu, hsa⟩ := (regAt_iff_exists_chart_fraction X Ω ξ ℤ _ (mseg y) T c q hq a).1 ha
    exact ⟨s, int_le O _ hs, hu, int_le O _ hsa⟩
  · obtain ⟨g, hg, hu, h⟩ := basic_nbhd (mseg y) T c hc q hq U hU
    exact ⟨g, int_le O _ hg, hu, fun q' hq' _ hu' => h q' hq' hu'⟩
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LatticeSectionAlgebra
open GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.Xgn.LatticeSectionAlgebra

theorem denom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type)
    (reg : Q → Subring Ω)
    (h3 : ∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q))
    (h4 : ∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R)
    (g : Ω) (hg : g ∈ R) (a : Ω) (ha : ∀ q, g ≠ 0 → g⁻¹ ∈ reg q → a ∈ reg q) :
    ∃ n : ℕ, g ^ n * a ∈ R := by
  let I : Ideal R :=
    { carrier := {s | (s : Ω) * a ∈ R}
      add_mem' := by
        intro x y hx hy
        have := R.add_mem hx hy
        simpa [add_mul] using this
      zero_mem' := by simp
      smul_mem' := by
        intro c x hx
        have := R.mul_mem c.2 hx
        simpa [mul_assoc] using this }
  have hI : ∀ s : R, s ∈ I ↔ (s : Ω) * a ∈ R := fun s => Iff.rfl
  have hrad : (⟨g, hg⟩ : R) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hIP, hP⟩
    by_contra hgP
    obtain ⟨q, hq⟩ := h3 P hP
    obtain ⟨h0, hu⟩ := (hq _).1 hgP
    obtain ⟨s, hsR, hs0, hsu, hsa⟩ := h4 q a (ha q h0 hu)
    exact (hq ⟨s, hsR⟩).2 ⟨hs0, hsu⟩ (hIP ((hI ⟨s, hsR⟩).2 hsa))
  obtain ⟨n, hn⟩ := hrad
  refine ⟨n, ?_⟩
  have := (hI _).1 hn
  simpa using this

theorem unif {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω)
    {ι : Type} [Fintype ι] (g a : ι → Ω) (hg : ∀ i, g i ∈ R)
    (h : ∀ i, ∃ n : ℕ, g i ^ n * a i ∈ R) : ∃ n : ℕ, ∀ i, g i ^ n * a i ∈ R := by
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := n) (Finset.mem_univ i))
  rw [hd, add_comm, pow_add, mul_assoc]
  exact R.mul_mem (R.pow_mem (hg i) d) (hn i)

theorem some_unit {Ω : Type} [Field Ω] (A : Subring Ω) [IsLocalRing A] {k : ℕ} (c g : Fin k → Ω)
    (hc : ∀ l, c l ∈ A) (hg : ∀ l, g l ∈ A) (h : ∑ l, c l * g l = 1) :
    ∃ l, (g l)⁻¹ ∈ A ∧ g l ≠ 0 := by
  by_contra hne
  have hm : ∀ l, (⟨g l, hg l⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    intro l
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb' : g l * (b : Ω) = 1 := by simpa using congrArg Subtype.val hb
    refine hne ⟨l, ?_, left_ne_zero_of_mul_eq_one hb'⟩
    rw [inv_eq_of_mul_eq_one_right hb']
    exact b.2
  have h1 : (∑ l, (⟨c l, hc l⟩ : A) * ⟨g l, hg l⟩) ∈ IsLocalRing.maximalIdeal A :=
    Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hm l)
  have h2 : (∑ l, (⟨c l, hc l⟩ : A) * ⟨g l, hg l⟩) = 1 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simpa using h
  rw [h2] at h1
  exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem span_top {Ω : Type} [Field Ω] {r : ℕ} (f : Fin r → (Fin r → Ω))
    (hf : LinearIndependent Ω f) : Submodule.span Ω (Set.range f) = ⊤ :=
  hf.span_eq_top_of_card_eq_finrank' (by simp)

theorem coords {Ω : Type} [Field Ω] {r : ℕ} (f : Fin r → (Fin r → Ω))
    (hf : LinearIndependent Ω f) (e : Fin r → Ω) : ∃ a : Fin r → Ω, e = ∑ i, a i • f i := by
  have : e ∈ Submodule.span Ω (Set.range f) := by rw [span_top f hf]; trivial
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
  exact ⟨a, ha.symm⟩

end PositivityTheory.Xgn.LatticeSectionAlgebra

open PositivityTheory.Xgn.LatticeSectionAlgebra in
theorem PositivityTheory.Xgn.lattice_section_algebra : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
  intro o Ω _ _ _ R Q reg r Λ h1 h2 h3 h4 h5
  choose G hGR hG0 hGu F hF hfr using h5
  have hstab : ∀ q, ∀ a ∈ reg q, ∀ e ∈ Λ q, a • e ∈ Λ q := by
    intro q a ha e he
    obtain ⟨b, hb, rfl⟩ := (hfr q q (hGu q) e).1 he
    refine (hfr q q (hGu q) _).2 ⟨fun i => a * b i, fun i => mul_mem ha (hb i), ?_⟩
    simp only [Finset.smul_sum, smul_smul]
  have hcoord : ∀ q q', (G q)⁻¹ ∈ reg q' → ∀ a : Fin r → Ω, (∑ i, a i • F q i) ∈ Λ q' →
      ∀ i, a i ∈ reg q' := by
    intro q q' hq a ha i
    obtain ⟨b, hb, hab⟩ := (hfr q q' hq _).1 ha
    rw [Fintype.linearIndependent_iffₛ.1 (hF q) a b hab i]
    exact hb i
  have htop : Ideal.span (Set.range fun q => (⟨G q, hGR q⟩ : R)) = ⊤ := by
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨q, hq⟩ := h3 P hP.isPrime
    exact (hq ⟨G q, hGR q⟩).2 ⟨hG0 q, hGu q⟩ (hle (Ideal.subset_span ⟨q, rfl⟩))
  obtain ⟨k, c, t, hsum⟩ := Submodule.mem_span_set'.1 ((Ideal.eq_top_iff_one _).1 htop)
  choose p hp using fun l => (t l).2
  have hsum' : ∑ l, (c l : Ω) * G (p l) = 1 := by
    have := congrArg Subtype.val hsum
    rw [AddSubmonoidClass.coe_finsetSum] at this
    refine Eq.trans (Finset.sum_congr rfl fun l _ => ?_) this
    rw [← hp l]
    simp
  have hcov : ∀ q, ∃ l, (G (p l))⁻¹ ∈ reg q := by
    intro q
    haveI := h1 q
    obtain ⟨l, hl, -⟩ := some_unit (reg q) (fun l => (c l : Ω)) (fun l => G (p l))
      (fun l => h2 q _ (c l).2) (fun l => h2 q _ (hGR _)) hsum'
    exact ⟨l, hl⟩
  have hsec : ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) →
      ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
    intro g hg e he
    choose a ha using fun l => coords (F (p l)) (hF _) e
    obtain ⟨n, hn⟩ := unif R (ι := Fin k × Fin r) (fun x => g * G (p x.1)) (fun x => a x.1 x.2)
      (fun x => R.mul_mem hg (hGR _)) (by
        rintro ⟨l, i⟩
        refine denom R Q reg h3 h4 _ (R.mul_mem hg (hGR _)) _ ?_
        intro q h0 hu
        have hg0 : g ≠ 0 := left_ne_zero_of_mul h0
        have hl0 := hG0 (p l)
        have e1 : g⁻¹ = G (p l) * (g * G (p l))⁻¹ := by field_simp
        have e2 : (G (p l))⁻¹ = g * (g * G (p l))⁻¹ := by field_simp
        have u1 : g⁻¹ ∈ reg q := by rw [e1]; exact mul_mem (h2 q _ (hGR _)) hu
        have u2 : (G (p l))⁻¹ ∈ reg q := by rw [e2]; exact mul_mem (h2 q _ hg) hu
        exact hcoord (p l) q u2 (a l) (ha l ▸ he q hg0 u1) i)
    refine ⟨n, AddSubgroup.mem_iInf.2 fun q => ?_⟩
    obtain ⟨l, hl⟩ := hcov q
    refine (hfr (p l) q hl _).2 ⟨fun i => g ^ n * a l i, fun i => ?_, ?_⟩
    · have hl0 := hG0 (p l)
      have e1 : g ^ n * a l i = (G (p l))⁻¹ ^ n * ((g * G (p l)) ^ n * a l i) := by
        rw [mul_pow, inv_pow]; field_simp
      show g ^ n * a l i ∈ reg q
      rw [e1]
      exact mul_mem (pow_mem hl n) (h2 q _ (hn (l, i)))
    · conv_lhs => rw [ha l]
      simp only [Finset.smul_sum, smul_smul]
  refine ⟨⟨?_, k, fun l => G (p l), fun l => c l, fun l => hGR _, fun l => (c l).2, hsum', ?_⟩, hsec⟩
  · intro a ha e he
    exact AddSubgroup.mem_iInf.2 fun q => hstab q a (h2 q a ha) e (AddSubgroup.mem_iInf.1 he q)
  · intro l
    have hl0 := hG0 (p l)
    refine ⟨F (p l), hF _, span_top _ (hF _), fun e => ⟨?_, ?_⟩⟩
    · rintro ⟨n, hn⟩
      obtain ⟨a, rfl⟩ := coords (F (p l)) (hF _) e
      refine ⟨a, fun i => denom R Q reg h3 h4 _ (hGR _) _ ?_, rfl⟩
      intro q _ hu
      refine hcoord (p l) q hu a ?_ i
      have := hstab q _ (pow_mem hu n) _ (AddSubgroup.mem_iInf.1 hn q)
      rwa [smul_smul, ← mul_pow, inv_mul_cancel₀ hl0, one_pow, one_smul] at this
    · rintro ⟨a, ha, rfl⟩
      refine hsec _ (hGR _) _ fun q _ hu => (hfr (p l) q hu _).2 ⟨a, fun i => ?_, rfl⟩
      obtain ⟨n, hn⟩ := ha i
      have e1 : a i = (G (p l))⁻¹ ^ n * (G (p l) ^ n * a i) := by
        rw [inv_pow]; field_simp
      rw [e1]
      exact mul_mem (pow_mem hu n) (h2 q _ hn)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmFlagUnramifiedPrime
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmFlagUnramifiedPrime
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem hodgeLattices_isVBOn_overPrime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q) → ∀ t : CMType H ⊕ CMType H, (𝔐.dR t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) ∧ (𝔐.HT p t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) :=
  PositivityTheory.Xgn.vector_bundle_lattice_labels

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmFlagUnramifiedPrimeStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_flag_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → ¬ (p : ℤ) ∣ NumberField.discr E → (∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q) → ∀ t : CMType H ⊕ CMType H, (𝔐.dR t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) ∧ (𝔐.HT p t).IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.hodgeLattices_isVBOn_overPrime | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.hodgeLattices_isVBOn_overPrime | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.hodgeLattices_isVBOn_overPrime <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpRatioUnramifiedOddPrime
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpRatioUnramifiedOddPrime
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem integers_regular {F : Type} [Field F] [NumberField F] (hN : Flat.NormalCpt ξ) (σ : 𝓞 F →+* Ω) (q : Cpt ξ)
    (a : 𝓞 F) : σ a ∈ regAt ξ q := by
  refine hN q _ ?_
  have h : IsIntegral ℤ (σ a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map σ.toIntAlgHom
  exact h.tower_top

theorem unitAt_nat {q : Cpt ξ} [CharZero Ω] (n : ℕ) (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → unitAt ξ q (p : Ω)) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one => simpa using Flat.ZUnit.one
  | prime p hp => exact h p hp dvd_rfl
  | mul a b ha hb =>
    rw [Nat.cast_mul]
    exact Flat.ZUnit.mul (ha (left_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_right b))
      (hb (right_ne_zero_of_mul hn) fun p hp hd => h p hp (hd.mul_left a))

theorem unitAt_natAbs_discr {F : Type} [Field F] [NumberField F] {q : Cpt ξ} [CharZero Ω]
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr F → unitAt ξ q (p : Ω)) :
    unitAt ξ q (((discr F).natAbs : ℕ) : Ω) :=
  unitAt_nat _ (Int.natAbs_ne_zero.2 (discr_ne_zero F)) fun p hp hd =>
    h p hp (Int.natCast_dvd.2 hd)

theorem natAbs_discr_mem_different (F : Type) [Field F] [NumberField F] :
    (((discr F).natAbs : ℕ) : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
  have h := Ideal.absNorm_mem (differentIdeal ℤ (𝓞 F))
  rwa [absNorm_differentIdeal F] at h

theorem htW_eq_htDual {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li)
    (L : Semi.LB G.left) (n : ℕ) {F : Type} [Field F] [NumberField F] (ρ : 𝓞 F →+* Module.End Ω Li)
    (σ : 𝓞 F →+* Ω) (q : Cpt ξ) (hσ : ∀ a, σ a ∈ regAt ξ q)
    (hu : unitAt ξ q (((discr F).natAbs : ℕ) : Ω)) :
    M.htW L n ρ σ (differentIdeal ℤ (𝓞 F)) q = M.htDual L n ρ σ q := by
  apply le_antisymm
  · refine Submodule.span_le.2 fun e he => ?_
    have h1 := he.2 _ (natAbs_discr_mem_different F)
    rw [map_natCast] at h1
    have h2 := Submodule.smul_mem _ (⟨_, hu.2.2⟩ : regAt ξ q) h1
    have h3 : (⟨_, hu.2.2⟩ : regAt ξ q) • (((discr F).natAbs : ℕ) : Ω) • e = e := by
      show (((discr F).natAbs : ℕ) : Ω)⁻¹ • (((discr F).natAbs : ℕ) : Ω) • e = e
      exact inv_smul_smul₀ hu.1 e
    rw [h3] at h2
    exact h2
  · intro e he
    refine Submodule.subset_span ⟨M.mem_eigSp_of_mem_htDual L n ρ σ he, fun d _ => ?_⟩
    exact Submodule.smul_mem _ (⟨σ d, hσ d⟩ : regAt ξ q) he

theorem exists_mul_of_isCp {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {κ w : Ω} (hκ : HT.IsCp p κ) (hw : HT.IsCp p w)
    (R : Subring Ω) (hR : w ∈ R) : ∃ u ∈ R, w = u * κ := by
  unfold HT.IsCp at hκ hw
  rw [if_neg h2] at hκ hw
  obtain ⟨z, hz, rfl⟩ := hκ
  obtain ⟨z', hz', rfl⟩ := hw
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨j, -, hj⟩ := hz'.eq_pow_of_pow_eq_one hz.pow_eq_one
  obtain ⟨k, -, hk⟩ := hz.eq_pow_of_pow_eq_one hz'.pow_eq_one
  have h1 : z' ∈ R := by simpa using R.add_mem hR R.one_mem
  have h3 : z ∈ R := hj ▸ R.pow_mem h1 j
  refine ⟨∑ i ∈ Finset.range k, z ^ i, R.sum_mem fun i _ => R.pow_mem h3 i, ?_⟩
  rw [geom_sum_mul, hk]

theorem sandwich_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ κ w : Ω, HT.IsCp p κ → HT.IsCp p w → HT.Sandwich 𝔐 p κ → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → w ∈ regAt 𝔐.ξ q → ∀ t : CMType H ⊕ CMType H, 𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, w • e ∈ 𝔐.dR t q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ J y 𝔐 p hp _ h2 hd κ w hκ hw hS q hq hwq t
  haveI : CharZero Ω := ⟨fun a b h => by
    have h' : 𝔐.cst (a : c.F) = 𝔐.cst (b : c.F) := by rw [map_natCast, map_natCast, h]
    exact Nat.cast_injective (𝔐.cst.injective h')⟩
  have hN : Flat.NormalCpt 𝔐.ξ := GlobalTheory.CompanionTheory.Ar.XR.normalCpt_of_isCptGen 𝔐.tie.gen (fun x => ⟨𝔐.normal.1 x, 𝔐.normal.2 x⟩)
  have hu : unitAt 𝔐.ξ q (((discr E).natAbs : ℕ) : Ω) := unitAt_natAbs_discr fun r hr hrd => by
    by_contra hn
    have : r = p := GlobalTheory.CompanionTheory.Ar.inFibre_unique hp.out hr hq hn
    exact hd (this ▸ hrd)
  have hHT : 𝔐.HT p t q = 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb t) q := by
    cases t with
    | inl τ => exact htW_eq_htDual 𝔐.M _ _ 𝔐.ρ _ q (integers_regular hN _ q) hu
    | inr τ => rfl
  obtain ⟨-, -, -, hs⟩ := hS q hq
  obtain ⟨h1, h3⟩ := hs t
  obtain ⟨u, huR, rfl⟩ := exists_mul_of_isCp hp.out h2 hκ hw (regAt 𝔐.ξ q) hwq
  rw [hHT]
  refine ⟨h1, fun e he => ?_⟩
  rw [mul_smul]
  exact Submodule.smul_mem _ (⟨u, huR⟩ : regAt 𝔐.ξ q) (h3 e he)

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpRatioUnramifiedOddPrimeStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cp_ratio_unramified_odd_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ κ w : Ω, HT.IsCp p κ → HT.IsCp p w → HT.Sandwich 𝔐 p κ → ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → w ∈ regAt 𝔐.ξ q → ∀ t : CMType H ⊕ CMType H, 𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, w • e ∈ 𝔐.dR t q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTorsionUnramifiedPrime
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTorsionUnramifiedPrime
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem htLattice_eq_dR_of_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → Nonempty (GenTors 𝔐 p) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q :=
  @PositivityTheory.Xgn.lattice_height_unit

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTorsionUnramifiedPrimeStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_torsion_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (p : ℕ) [Fact p.Prime], p ∈ S → Nonempty (GenTors 𝔐 p) → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (t : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ), (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → 𝔐.HT p t q = 𝔐.dR t q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.htLattice_eq_dR_of_charZero | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.htLattice_eq_dR_of_charZero | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.htLattice_eq_dR_of_charZero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DotDualLatticeFamily
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DotDualLatticeFamily
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem dotDual_latFamily : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) :=
  @PositivityTheory.Xgn.dual_lattice_family

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DotDualLatticeFamilyStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dot_dual_lattice_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (r : ℕ) (Γ : (∀ k, J k) → AddSubgroup (Fin r → Ω)), IsLatFamily O y Γ → (∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (Γ c)) → IsLatFamily O y (fun c => dotDual (chartRing O (mseg y) c) (Γ c)) ∧ ∀ c, mseg y c ≠ 0 → LocFree (chartRing O (mseg y) c) r (dotDual (chartRing O (mseg y) c) (Γ c)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.dotDual_latFamily | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.dotDual_latFamily | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.dotDual_latFamily <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrLocalizationConstants
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrLocalizationConstants
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem chart_points_over_place : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) :=
  @PositivityTheory.Xgn.lattice_chart_points

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrLocalizationConstantsStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_localization_constants : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (mseg y) → ∀ (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, J k), mseg y c ≠ 0 → (∀ a ∈ chartRing O (mseg y) c, ∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → a ∈ regAt ξ q) ∧ (∀ P : Ideal (chartRing O (mseg y) c), P.IsPrime → ∃ q : Cpt ξ, InChart ξ (mseg y) c q ∧ (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) ∧ ∀ s : chartRing O (mseg y) c, s ∉ P ↔ unitAt ξ q (s : Ω)) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ a ∈ regAt ξ q, ∃ s ∈ chartRing O (mseg y) c, unitAt ξ q s ∧ s * a ∈ chartRing O (mseg y) c) ∧ (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ U : X.Opens, q.1 ∈ U → ∃ g ∈ chartRing O (mseg y) c, unitAt ξ q g ∧ ∀ q' : Cpt ξ, InChart ξ (mseg y) c q' → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q') → unitAt ξ q' g → q'.1 ∈ U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLatticeLocalFree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLatticeLocalFree
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.SecAlg

theorem locFree_and_extend : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q :=
  @PositivityTheory.Xgn.lattice_section_algebra

end GlobalTheory.CompanionTheory.Ar.Num.SecAlg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLatticeLocalFreeStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_lattice_local_free : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (Q : Type) (reg : Q → Subring Ω) (r : ℕ) (Λ : Q → AddSubgroup (Fin r → Ω)), (∀ q, IsLocalRing (reg q)) → (∀ q, ∀ a ∈ R, a ∈ reg q) → (∀ P : Ideal R, P.IsPrime → ∃ q, ∀ s : R, s ∉ P ↔ ((s : Ω) ≠ 0 ∧ (s : Ω)⁻¹ ∈ reg q)) → (∀ q, ∀ a ∈ reg q, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ reg q ∧ s * a ∈ R) → (∀ q, ∃ g ∈ R, g ≠ 0 ∧ g⁻¹ ∈ reg q ∧ ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q', g⁻¹ ∈ reg q' → ∀ e, e ∈ Λ q' ↔ ∃ a : Fin r → Ω, (∀ i, a i ∈ reg q') ∧ e = ∑ i, a i • f i) → LocFree R r (⨅ q, Λ q) ∧ ∀ g ∈ R, ∀ e : Fin r → Ω, (∀ q, g ≠ 0 → g⁻¹ ∈ reg q → e ∈ Λ q) → ∃ n : ℕ, g ^ n • e ∈ ⨅ q, Λ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend | exact GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeBound
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamLat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isLocalRing_regAt (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

theorem coordLat_locFree (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (hT : CoordTie ℤ ξ (mseg y)) (A : Type)
    [CommRing A] [Algebra A Ω] (hA : HasConstants ℤ A y) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (Vg : Submodule Ω V) (b : Fin r → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = Vg)
    (hVB : L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt ξ q} r Vg) (c : ∀ k, J k) (hc : mseg y c ≠ 0) :
    LocFree (chartRing O (mseg y) c) r (coordLat O y L b c) ∧ ∀ g ∈ chartRing O (mseg y) c, ∀ e : Fin r → Ω,
      (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → g ≠ 0 → g⁻¹ ∈ regAt ξ q →
        Fintype.linearCombination Ω b e ∈ L q) → ∃ n : ℕ, g ^ n • e ∈ coordLat O y L b c := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := GlobalTheory.T.dvr_localization_constants X Ω ξ K J y hT A hA m O c hc
  let Q : Type := {q : Cpt ξ // InChart ξ (mseg y) c q ∧ ∀ o : O, algebraMap O Ω o ∈ regAt ξ q}
  let Λ : Q → AddSubgroup (Fin r → Ω) := fun q =>
    (L q.1).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom
  have hcoord : coordLat O y L b c = ⨅ q, Λ q := by
    ext e
    simp only [coordLat, AddSubgroup.mem_iInf, Subtype.forall, Λ, Q]
    exact ⟨fun h q hq => h q hq.1 hq.2, fun h q h1 h2 => h q ⟨h1, h2⟩⟩
  have hinj : Function.Injective (Fintype.linearCombination Ω b) :=
    hli.fintypeLinearCombination_injective
  have hfr : ∀ q : Q, ∃ g ∈ chartRing O (mseg y) c, g ≠ 0 ∧ g⁻¹ ∈ regAt ξ q.1 ∧
      ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q' : Q, g⁻¹ ∈ regAt ξ q'.1 → ∀ e, e ∈ Λ q' ↔
        ∃ a : Fin r → Ω, (∀ i, a i ∈ regAt ξ q'.1) ∧ e = ∑ i, a i • f i := by
    intro q
    obtain ⟨U, hU, f, hfs, hf⟩ := hVB q.1 q.2.2
    obtain ⟨g, hg, hgu, hgU⟩ := h4 q.1 q.2.1 q.2.2 U hU
    have hmem : ∀ i, ∃ f' : Fin r → Ω, Fintype.linearCombination Ω b f' = f i := by
      intro i
      have : f i ∈ Submodule.span Ω (Set.range b) := by
        rw [hsp, ← hfs]; exact Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
      exact ⟨a, by rw [Fintype.linearCombination_apply]; exact ha⟩
    choose f' hf' using hmem
    refine ⟨g, hg, hgu.1, hgu.2.2, f', ?_, fun q' hq' e => ?_⟩
    · have hl := (hf q.1 q.2.2 hU).1
      have : (Fintype.linearCombination Ω b) ∘ f' = f := funext hf'
      rw [← this] at hl
      exact hl.of_comp _
    · have hu : unitAt ξ q'.1 g := ⟨hgu.1, h1 g hg q'.1 q'.2.1 q'.2.2, hq'⟩
      have hq'U := hgU q'.1 q'.2.1 q'.2.2 hu
      have hfrm := (hf q'.1 q'.2.2 hq'U).2
      show Fintype.linearCombination Ω b e ∈ L q'.1 ↔ _
      rw [hfrm]
      constructor
      · intro he
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ q'.1)).1 he
        refine ⟨fun i => (a i : Ω), fun i => (a i).2, hinj ?_⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← ha, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hf']
        rfl
      · rintro ⟨a, ha, rfl⟩
        refine (Submodule.mem_span_range_iff_exists_fun (regAt ξ q'.1)).2 ⟨fun i => ⟨a i, ha i⟩, ?_⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hf']
        rfl
  have key := GlobalTheory.T.regular_lattice_local_free (chartRing O (mseg y) c) Q (fun q => regAt ξ q.1) r Λ (fun q => isLocalRing_regAt q.1)
    (fun q a ha => h1 a ha q.1 q.2.1 q.2.2)
    (fun P hP => by
      obtain ⟨q, hq1, hq2, hq⟩ := h2 P hP
      refine ⟨⟨q, hq1, hq2⟩, fun s => ?_⟩
      rw [hq s]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h1 _ s.2 q hq1 hq2, h.2⟩⟩)
    (fun q a ha => by
      obtain ⟨s, hs, hu, hsa⟩ := h3 q.1 q.2.1 q.2.2 a ha
      exact ⟨s, hs, hu.1, hu.2.2, hsa⟩)
    hfr
  rw [hcoord]
  refine ⟨key.1, fun g hg e he => key.2 g hg e fun q h h' => ?_⟩
  exact he q.1 q.2.1 q.2.2 h h'

theorem coordLat_family (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (hT : CoordTie ℤ ξ (mseg y)) (A : Type)
    [CommRing A] [Algebra A Ω] (hA : HasConstants ℤ A y) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (Vg : Submodule Ω V) (b : Fin r → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = Vg)
    (hVB : L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt ξ q} r Vg) :
    IsLatFamily O y (coordLat O y L b) := by
  have key := coordLat_locFree X Ω ξ K J y hT A hA m O V L r Vg b hli hsp hVB
  refine ⟨fun s hs a ha v hv => (key s hs).1.1 a ha v hv, fun s t hs ht v hv => ?_⟩
  have hg : mseg y s / mseg y t ∈ chartRing O (mseg y) t := Algebra.subset_adjoin ⟨s, rfl⟩
  refine (key t ht).2 _ hg v fun q hq hO hg0 hgi => ?_
  have hqs : InChart ξ (mseg y) s q := by
    refine ⟨hs, fun c' => ?_⟩
    have e : mseg y c' / mseg y s = mseg y c' / mseg y t * (mseg y s / mseg y t)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hq.2 c') hgi
  have := (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hqs) hO)
  exact this

theorem coordLat_mono {O : Type} [CommRing O] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V] {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V)
    (c : ∀ k, J k) (h : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → L q ≤ L' q) :
    coordLat O y L b c ≤ coordLat O y L' b c := by
  intro v hv
  refine AddSubgroup.mem_iInf.2 fun q => AddSubgroup.mem_iInf.2 fun hq => AddSubgroup.mem_iInf.2 fun hO => ?_
  exact h q hO (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hq) hO)

theorem coordLat_le_divLat {O : Type} [CommRing O] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V] {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V)
    (c : ∀ k, J k) (a : Ω) (h : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ e ∈ L' q, a • e ∈ L q) :
    coordLat O y L' b c ≤ divLat a (coordLat O y L b c) := by
  intro v hv
  show a • v ∈ coordLat O y L b c
  refine AddSubgroup.mem_iInf.2 fun q => AddSubgroup.mem_iInf.2 fun hq => AddSubgroup.mem_iInf.2 fun hO => ?_
  have := h q hO _ (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hq) hO)
  show Fintype.linearCombination Ω b (a • v) ∈ L q
  rw [map_smul]
  exact this

theorem mem_dotDual' {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ} (L : AddSubgroup (Fin n → Ω))
    (v : Fin n → Ω) : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf]
  rfl

theorem dotDual_anti {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ} {L L' : AddSubgroup (Fin n → Ω)}
    (h : L ≤ L') : dotDual R L' ≤ dotDual R L := fun v hv =>
  (mem_dotDual' R L v).2 fun l hl => (mem_dotDual' R L' v).1 hv l (h hl)

theorem dotDual_le_divLat {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ}
    {L L' : AddSubgroup (Fin n → Ω)} (a : Ω) (h : L' ≤ divLat a L) : dotDual R L ≤ divLat a (dotDual R L') := by
  intro v hv
  show a • v ∈ dotDual R L'
  refine (mem_dotDual' R L' _).2 fun l hl => ?_
  have h2 := (mem_dotDual' R L v).1 hv _ (show a • l ∈ L from h hl)
  rwa [dotProduct_smul, ← smul_dotProduct]

theorem unit_of_place {A : Type} [CommRing A] [Algebra A Ω] {m : Ideal A} [m.IsPrime] {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] {p : ℕ} (hpm : (p : A) ∈ m) (hp : p.Prime) {q : Cpt ξ}
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) : q ∈ overPrime ξ p := by
  intro r hr hrp hf
  have hco : IsCoprime (r : ℤ) (p : ℤ) := by
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hr hp).2 hrp)
  obtain ⟨a, b, hab⟩ := hco
  have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hpm
    simpa using this
  have hrO : IsUnit (r : O) := by
    by_contra hn
    have hr' : (r : O) ∈ IsLocalRing.maximalIdeal O := hn
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have e : (1 : O) = (a : O) * (r : O) + (b : O) * (p : O) := by
        have := congrArg (Int.cast : ℤ → O) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hr') (Ideal.mul_mem_left _ _ hpO)
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal O).ne_top this
  obtain ⟨u, hu⟩ := hrO.exists_right_inv
  have hu' : (r : Ω) * algebraMap O Ω u = 1 := by
    have := congrArg (algebraMap O Ω) hu
    simpa using this
  have hr0 : (r : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hu'
  refine hf ⟨hr0, natCast_mem _ r, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hu']
  exact hO u

theorem lat_main : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ t : CMType H ⊕ CMType H, IsLatFamily O y (fun c' => coordLat O y (𝔐.dR t) (b t) c') ∧ IsLatFamily O y (fun c' => coordLat O y (𝔐.HT p t) (b t) c') ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ coordLat O y (𝔐.dR t) (b t) c' ≤ coordLat O y (𝔐.HT p t) (b t) c' ∧ coordLat O y (𝔐.HT p t) (b t) c' ≤ divLat (algebraMap O Ω w) (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c') ≤ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ≤ divLat (algebraMap O Ω w) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hvar hpq p _ hpS hfree hp2 hdisc b hb A _ _ _ m _ hpm O _ _ _ _
    _ _ _ w hw t
  have hpp : p.Prime := Fact.out
  have hG : Nonempty (GenTors 𝔐 p) := GlobalTheory.T.arith_variety_hodge_prime_degree E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar hpq p hpS hfree hp2 hdisc
  obtain ⟨κ, hκ, hS⟩ := GlobalTheory.T.exists_sandwich_of_hodge_tate_free hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hpq hfree
  obtain ⟨-, -, -, hcon, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar A
  have hE := GlobalTheory.T.generic_torsion_unramified_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hG hdisc
  obtain ⟨hV1, hV2⟩ := GlobalTheory.T.cm_flag_unramified_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hdisc hE t
  have hT : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hO : ∀ q : Cpt 𝔐.ξ, (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → q ∈ overPrime 𝔐.ξ p :=
    fun q h => unit_of_place (A := A) (m := m) (O := O) hpm hpp h
  have hres : ∀ (L : Lat 𝔐.ξ 𝔐.Li), L.IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) →
      L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q} (labelRk D t) (𝔐.Vgen t) := by
    intro L hL q hq
    obtain ⟨U, hU, f, hf, hfr⟩ := hL q (hO q hq)
    exact ⟨U, hU, f, hf, fun q' hq' hq'U => hfr q' (hO q' hq') hq'U⟩
  have hdF := coordLat_family _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.dR t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV1)
  have hhF := coordLat_family _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.HT p t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV2)
  have hdL : ∀ c', mseg y c' ≠ 0 → LocFree (chartRing O (mseg y) c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') :=
    fun c' hc' => (coordLat_locFree _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.dR t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV1) c' hc').1
  have hhL : ∀ c', mseg y c' ≠ 0 → LocFree (chartRing O (mseg y) c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') :=
    fun c' hc' => (coordLat_locFree _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.HT p t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV2) c' hc').1
  obtain ⟨hdD, hdDL⟩ := GlobalTheory.T.dot_dual_lattice_family O Ω K J y _ _ hdF hdL
  obtain ⟨hhD, hhDL⟩ := GlobalTheory.T.dot_dual_lattice_family O Ω K J y _ _ hhF hhL
  have hpt : ∀ q : Cpt 𝔐.ξ, (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) →
      𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, algebraMap O Ω w • e ∈ 𝔐.dR t q := by
    intro q hq
    by_cases hf : InFibre 𝔐.ξ p q
    · exact GlobalTheory.T.cp_ratio_unramified_odd_prime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hp2 hdisc κ _ hκ hw hS q hf (hq w) t
    · have hall : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q := fun r hr => by
        by_cases hrp : r = p
        · exact hrp ▸ hf
        · exact hO q hq r hr hrp
      rw [hE t q hall]
      exact ⟨le_rfl, fun e he => (𝔐.dR t q).smul_mem (⟨_, hq w⟩ : regAt 𝔐.ξ q) he⟩
  refine ⟨hdF, hhF, hdD, hhD, fun c' hc' => ⟨hdL c' hc', hhL c' hc', hdDL c' hc', hhDL c' hc', ?_, ?_, ?_, ?_⟩⟩
  · exact coordLat_mono y (b t) c' fun q hq => (hpt q hq).1
  · exact coordLat_le_divLat y (b t) c' _ fun q hq => (hpt q hq).2
  · exact dotDual_anti _ (coordLat_mono y (b t) c' fun q hq => (hpt q hq).1)
  · exact dotDual_le_divLat _ _ (coordLat_le_divLat y (b t) c' _ fun q hq => (hpt q hq).2)

end GlobalTheory.CompanionTheory.Ar.Num.FamLat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeBoundStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_model_prime_bound : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ t : CMType H ⊕ CMType H, IsLatFamily O y (fun c' => coordLat O y (𝔐.dR t) (b t) c') ∧ IsLatFamily O y (fun c' => coordLat O y (𝔐.HT p t) (b t) c') ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ coordLat O y (𝔐.dR t) (b t) c' ≤ coordLat O y (𝔐.HT p t) (b t) c' ∧ coordLat O y (𝔐.HT p t) (b t) c' ≤ divLat (algebraMap O Ω w) (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c') ≤ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ≤ divLat (algebraMap O Ω w) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamLat.lat_main | exact GlobalTheory.CompanionTheory.Ar.Num.FamLat.lat_main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamLat.lat_main <;> assumption)
end
