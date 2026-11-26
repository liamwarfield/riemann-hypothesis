module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockComp
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSAux

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def BlockGenOfModel.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (k₀ : K),
    IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀ → BlockGen S y k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

def ModelOfBlockGen.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → BlockGen S y k₀ → IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase S y k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

def BlockGenTransfer.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (k₀ : K),
    BlockGen S y k₀ →
    ∀ (Ω' : Type) [Field Ω'] [Algebra S Ω'] (y' : (Σ k, ι k) → Ω'),
      (∀ k, ∃ i, y' ⟨k, i⟩ ≠ 0) → mIdealOver S y ≤ mIdealOver S y' → BlockGen S y' k₀

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechDDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace KHCechDDeg

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)]

theorem cellRes_mem_locPart {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {c : K → ℤ}
    {J I : ∀ k, Finset (ι k)} (h : KH.cellMon S J ≤ KH.cellMon S I) {x : LocalizedModule (KH.cellMon S J) M}
    (hx : x ∈ KH.locPart ι 𝓜 (KH.cellMon S J) c) :
    KH.cellRes S M J I x ∈ KH.locPart ι 𝓜 (KH.cellMon S I) c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    rw [GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellRes_mk h]
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep.mk_mem_locPart m ⟨t.1, h t.2⟩ a ht hm
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul s x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ s hx

theorem face_subset {K : Type} [DecidableEq K] {ι : K → Type} [∀ k, DecidableEq (ι k)]
    (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

end KHCechDDeg

theorem KHCechDDeg.full : KH.CechDDegStatement := by
  classical
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 c n φ hφ
  refine Submodule.mem_pi.mpr fun I _ => ?_
  simp only [KH.cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hI
  · change KH.faceSign I.1 k i • KH.cellRes S M _ I.1 (φ ⟨_, hI⟩) ∈ _
    refine zsmul_mem (KHCechDDeg.cellRes_mem_locPart ?_ (Submodule.mem_pi.mp hφ _ (Set.mem_univ _))) _
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.GenTwistGenerated.cellMon_mono
      (KHCechDDeg.face_subset I.1 k i)
  · rw [LinearMap.zero_apply]
    exact zero_mem _

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

theorem ModelChangeVeryAmple.proof (hGen : ModelChangeGen.Statement) : ModelChangeVeryAmple.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hy hy' hx β β' hs
  exact veryAmple_change hGen F Ω N K ι y k₀ e K' ι' y' k₀' e' hy hy' hx β β' hs

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHCechMapDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem KHCechMapDeg.full : KH.CechMapDegStatement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ N _ _ _ _ 𝓜 𝓝 g c n hg
  refine ⟨fun φ hφ => Submodule.mem_pi.mpr fun I _ => ?_, LinearMap.ext fun z => ?_⟩
  · exact KHTheoremS.locMap_mem_locPart hg (Submodule.mem_pi.mp hφ I (Set.mem_univ _))
  · exact KHTheoremS.cechD_cechMap g n z

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BlockDegLeTotalDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver)

noncomputable section

namespace ChartKernel

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type}

abbrev blockDeg (e : (Σ k, ι k) →₀ ℕ) : K →₀ ℕ := e.mapDomain Sigma.fst

theorem prod_block_pow {R : Type} [CommMonoid R] (e : (Σ k, ι k) →₀ ℕ) (v : K → R) :
    (e.prod fun p n => v p.1 ^ n) = ∏ k, v k ^ blockDeg e k := by
  have h := Finsupp.prod_mapDomain_index (f := Sigma.fst) (s := e) (h := fun k n => v k ^ n)
    (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  exact h.symm.trans (Finsupp.prod_fintype _ _ (fun _ => pow_zero _))


omit [Fintype K] in
theorem blockDeg_le_totalDegree (g : MvPolynomial (Σ k, ι k) S) :
    ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ g.totalDegree := by
  intro e he k
  refine le_trans ?_ (le_totalDegree he)
  rw [← Finsupp.sum_mapDomain_index (h := fun _ n => n) (fun _ => rfl) (fun _ _ _ => rfl)]
  by_cases hk : k ∈ (blockDeg e).support
  · exact Finset.single_le_sum (f := fun k => blockDeg e k) (fun _ _ => Nat.zero_le _) hk
  · rw [Finsupp.notMem_support_iff.mp hk]; exact Nat.zero_le _

def homog (c : ∀ k, ι k) (D : ℕ) (g : MvPolynomial (Σ k, ι k) S) : MvPolynomial (Σ k, ι k) S :=
  ∑ e ∈ g.support, monomial e (AddMonoidAlgebra.coeff g e) * ∏ k, X ⟨k, c k⟩ ^ (D - blockDeg e k)

variable {Ω : Type} [Field Ω] [Algebra S Ω]

theorem mConeMapOver_monomial (y : (Σ k, ι k) → Ω) (e : (Σ k, ι k) →₀ ℕ) (a : S) :
    mConeMapOver S y (monomial e a) = C (aeval y (monomial e a)) * ∏ k, X k ^ blockDeg e k := by
  simp only [mConeMapOver, aeval_monomial, mul_pow, Finsupp.prod_mul]
  rw [prod_block_pow e (fun k => (X k : MvPolynomial K Ω))]
  simp only [Finsupp.prod, map_mul, map_prod, map_pow, MvPolynomial.algebraMap_apply]
  ring

theorem mConeMapOver_homog (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {D : ℕ} {g : MvPolynomial (Σ k, ι k) S}
    (hD : ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ D) :
    mConeMapOver S y (homog c D g) = C (aeval y (homog c D g)) * ∏ k, X k ^ D := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [homog, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e he => ?_
  have hX : ∏ k, (X k : MvPolynomial K Ω) ^ D =
      (∏ k, X k ^ blockDeg e k) * ∏ k, X k ^ (D - blockDeg e k) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← pow_add, Nat.add_sub_cancel' (hD e he k)]
  rw [map_mul, mConeMapOver_monomial, hX]
  simp only [map_mul, map_prod, map_pow, mConeMapOver, aeval_X, mul_pow, Finset.prod_mul_distrib]
  ring

theorem aeval_homog (w : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hw : ∀ k, w ⟨k, c k⟩ ≠ 0) {D : ℕ}
    {g : MvPolynomial (Σ k, ι k) S} (hD : ∀ e ∈ g.support, ∀ k, blockDeg e k ≤ D) :
    aeval w (homog c D g) = (∏ k, w ⟨k, c k⟩ ^ D) * aeval (fun p => w p / w ⟨p.1, c p.1⟩) g := by
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [homog, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hP : ∏ k, w ⟨k, c k⟩ ^ D =
      (∏ k, w ⟨k, c k⟩ ^ (D - blockDeg e k)) * ∏ k, w ⟨k, c k⟩ ^ blockDeg e k := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← pow_add, Nat.sub_add_cancel (hD e he k)]
  have hne : ∏ k, w ⟨k, c k⟩ ^ blockDeg e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hw k)
  have hq : (e.prod fun p n => (w p / w ⟨p.1, c p.1⟩) ^ n) =
      (e.prod fun p n => w p ^ n) / ∏ k, w ⟨k, c k⟩ ^ blockDeg e k := by
    rw [← prod_block_pow e (fun k => w ⟨k, c k⟩)]
    simp only [Finsupp.prod, div_pow, Finset.prod_div_distrib]
  rw [map_mul, aeval_monomial, aeval_monomial, hq, hP]
  simp only [map_prod, map_pow, aeval_X]
  field_simp

end ChartKernel

theorem ChartKernel.proof : ChartKernel.Statement := by
  intro S _ K _ _ ι Ω _ _ y Ω' _ _ y' hle c hc g hg
  classical
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    have hm : (X ⟨k, c k⟩ : MvPolynomial (Σ k, ι k) S) ∈ mIdealOver S y := by
      change mConeMapOver S y (X _) = 0
      simp [mConeMapOver, h0]
    have h' : mConeMapOver S y' (X ⟨k, c k⟩) = 0 := hle hm
    simpa [mConeMapOver, X_ne_zero] using h')
  have hD := ChartKernel.blockDeg_le_totalDegree g
  have h1 : aeval y (ChartKernel.homog c g.totalDegree g) = 0 := by
    rw [ChartKernel.aeval_homog y hyc hD, hg, mul_zero]
  have h2 : ChartKernel.homog c g.totalDegree g ∈ mIdealOver S y := by
    change mConeMapOver S y _ = 0
    rw [ChartKernel.mConeMapOver_homog y c hD, h1, map_zero, zero_mul]
  have h3 : mConeMapOver S y' (ChartKernel.homog c g.totalDegree g) = 0 := hle h2
  rw [ChartKernel.mConeMapOver_homog y' c hD] at h3
  have h4 : aeval y' (ChartKernel.homog c g.totalDegree g) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact C_eq_zero.mp h
    · exact absurd h (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero k))
  rw [ChartKernel.aeval_homog y' hc hD] at h4
  exact (mul_eq_zero.mp h4).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemChartOfMemSecOver
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver GeneratesOver)

namespace ModelChangeGen

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]

def fracRing (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] : Subring Ω where
  carrier := {u | ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    simp only [MulMemClass.coe_mul]
    rw [div_mul_div_comm]
  one_mem' := ⟨1, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have h0 : ∀ d : A, d ∉ p → (d : Ω) ≠ 0 := fun d hd h =>
      hd (by rw [show d = 0 from Subtype.ext h]; exact p.zero_mem)
    refine ⟨a * b' + b * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    simp only [AddMemClass.coe_add, MulMemClass.coe_mul]
    rw [div_add_div _ _ (h0 b hb) (h0 b' hb')]
  zero_mem' := ⟨0, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by simp only [NegMemClass.coe_neg]; ring⟩

theorem mem_locIn (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] (a : A) :
    (a : Ω) ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨a, 1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩

theorem inv_mem_locIn (A : Subalgebra F Ω) (p : Ideal A) (a : A) (ha : a ∉ p) :
    (a : Ω)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
  Subring.subset_closure ⟨1, a, ha, by simp⟩

theorem inv_not_mem_locIn (A : Subalgebra F Ω) (p : Ideal A) [hp : p.IsPrime] (a : A) (ha : a ∈ p)
    (ha0 : (a : Ω) ≠ 0) : (a : Ω)⁻¹ ∉ IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
  intro hmem
  have hle : IndefiniteRowSideFullHecke.Kleiman2.locIn A p ≤ fracRing A p := Subring.closure_le.mpr fun u hu => hu
  obtain ⟨a', b, hb, hab⟩ := hle hmem
  have hb0 : (b : Ω) ≠ 0 := fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact p.zero_mem)
  have hba : b = a * a' := by
    apply Subtype.ext
    simp only [MulMemClass.coe_mul]
    field_simp at hab
    linear_combination hab
  exact hb (hba ▸ p.mul_mem_right a' ha)

theorem mem_chart_of_mem_secOver {K : Type} [Fintype K] {ι : K → Type} {y : (Σ k, ι k) → Ω} {δ : K → ℤ}
    {s : Ω} (hs : s ∈ secOver F y δ) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    s * ∏ k, y ⟨k, c k⟩ ^ (-δ k) ∈ chartRingOver F y c := by
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply] at hs
  exact hs c hc

theorem prod_twist {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} (y : (Σ k, ι k) → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (β : K → ℤ) (k₀ : K) (m : ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (∏ k, y ⟨k, c k⟩ ^ (-β k)) * (y ⟨k₀, c k₀⟩ ^ m)⁻¹ := by
  have h1 : ∀ k, y ⟨k, c k⟩ ^ (-(β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      y ⟨k, c k⟩ ^ (-β k) * y ⟨k, c k⟩ ^ (-((m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) := by
    intro k
    rw [← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]
    ring
  rw [Finset.prod_congr rfl (fun k _ => h1 k), Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single k₀]
  · simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, zpow_neg]
  · intro k _ hk
    simp [IndefiniteRowSideFullHecke.Kleiman2.baseDeg, hk]
  · intro h
    exact absurd (Finset.mem_univ k₀) h

theorem exists_not_mem {A : Subalgebra F Ω} (p : Ideal A) [hp : p.IsPrime] {n : ℕ} (t : Fin n → Ω)
    (ht : ∀ j, t j ∈ A) (u : Fin n → Ω) (hu : ∀ j, u j ∈ A) (hsum : ∑ j, u j * t j = 1) :
    ∃ j, (⟨t j, ht j⟩ : A) ∉ p := by
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hmem : (∑ j, (⟨u j, hu j⟩ : A) * ⟨t j, ht j⟩) ∈ p :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hcon j)
  have h1 : (∑ j, (⟨u j, hu j⟩ : A) * ⟨t j, ht j⟩) = 1 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, OneMemClass.coe_one]
    exact hsum
  exact hp.ne_top ((Ideal.eq_top_iff_one _).mpr (h1 ▸ hmem))

theorem gen_of_gen {N : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {y : (Σ k, ι k) → Ω} {k₀ : K} {e : ι k₀ ≃ Fin (N + 1)}
    {K' : Type} [Fintype K'] [DecidableEq K'] {ι' : K' → Type}
    {y' : (Σ k, ι' k) → Ω} {k₀' : K'} {e' : ι' k₀' ≃ Fin (N + 1)}
    (hpts : IndefiniteRowSideFullHecke.Kleiman2.modelPts F y' ⊆ IndefiniteRowSideFullHecke.Kleiman2.modelPts F y)
    (hx : IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm = IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀' ∘ e'.symm)
    {β : K → ℤ} {β' : K' → ℤ} (m : ℕ)
    (hs : secOver F y' (β' + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀') ≤
      secOver F y (β + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀))
    (hgen' : IndefiniteRowSideFullHecke.Kleiman2.IsGenerated F y' (β' + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀'))
    {n : ℕ} {h : Fin n → Ω} (hh : ∀ j, h j ∈ secOver F y β) (hh' : ∀ j, h j ∈ secOver F y' β')
    (hg : GeneratesOver F y β h) : GeneratesOver F y' β' h := by
  intro c' hc'
  set g' := ∏ k, y' ⟨k, c' k⟩ ^ (-β' k) with hg'def
  have ht : ∀ j, h j * g' ∈ chartRingOver F y' c' := fun j => mem_chart_of_mem_secOver (hh' j) c' hc'
  let t : Fin n → chartRingOver F y' c' := fun j => ⟨h j * g', ht j⟩
  by_cases htop : Ideal.span (Set.range t) = ⊤
  · obtain ⟨u, hu⟩ := (Ideal.mem_span_range_iff_exists_fun).mp ((Ideal.eq_top_iff_one _).mp htop)
    refine ⟨fun j => u j, fun j => (u j).2, ?_⟩
    have := congrArg Subtype.val hu
    simpa [t] using this
  exfalso
  obtain ⟨p', hp'max, hle⟩ := Ideal.exists_le_maximal _ htop
  have hp' : p'.IsPrime := hp'max.isPrime
  obtain ⟨c, hc, p, hp, hzeq⟩ := hpts ⟨c', hc', p', hp', rfl⟩

  obtain ⟨r, sv, hsv, hsgen⟩ := hgen'
  obtain ⟨v, hv, hvsum⟩ := hsgen c' hc'
  simp only [prod_twist y' c' hc' β' k₀' m] at hvsum
  have hsv' : ∀ l, sv l * (g' * (y' ⟨k₀', c' k₀'⟩ ^ m)⁻¹) ∈ chartRingOver F y' c' := fun l => by
    have := mem_chart_of_mem_secOver (hsv l) c' hc'
    rwa [prod_twist y' c' hc' β' k₀' m] at this
  obtain ⟨l, hl⟩ := exists_not_mem p' _ hsv' v hv hvsum

  set g := ∏ k, y ⟨k, c k⟩ ^ (-β k) with hgdef
  obtain ⟨u, hu, husum⟩ := hg c hc
  obtain ⟨j, hj⟩ := exists_not_mem p _ (fun j => mem_chart_of_mem_secOver (hh j) c hc) u hu husum
  have hw : sv l * (g * (y ⟨k₀, c k₀⟩ ^ m)⁻¹) ∈ chartRingOver F y c := by
    have := mem_chart_of_mem_secOver (hs (hsv l)) c hc
    rwa [prod_twist y c hc β k₀ m] at this

  have hxa : y ⟨k₀, c k₀⟩ = y' ⟨k₀', e'.symm (e (c k₀))⟩ := by
    have := congrFun hx (e (c k₀))
    simpa [IndefiniteRowSideFullHecke.Kleiman2.blockVec] using this
  have hratio : y ⟨k₀, c k₀⟩ / y' ⟨k₀', c' k₀'⟩ ∈ chartRingOver F y' c' := by
    rw [hxa]
    exact Algebra.subset_adjoin ⟨⟨k₀', e'.symm (e (c k₀))⟩, rfl⟩

  have hne : ∀ {A : Subalgebra F Ω} {q : Ideal A} (a : A), a ∉ q → (a : Ω) ≠ 0 := fun a ha h0 =>
    ha (by rw [show a = 0 from Subtype.ext h0]; exact Submodule.zero_mem _)
  have hjne := hne _ hj
  have hlne := hne _ hl
  have hg'ne : g' ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc' k)
  have hgne : g ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  have hxa0 : y ⟨k₀, c k₀⟩ ≠ 0 := hc k₀
  have hxb0 : y' ⟨k₀', c' k₀'⟩ ≠ 0 := hc' k₀'
  have hhj : h j ≠ 0 := fun h0 => hjne (by simp [h0])
  have hsl : sv l ≠ 0 := fun h0 => hlne (by simp [h0])

  have hmemp : t j ∈ p' := hle (Ideal.subset_span ⟨j, rfl⟩)
  have hkey : (h j * g')⁻¹ =
      (h j * g)⁻¹ * (sv l * (g * (y ⟨k₀, c k₀⟩ ^ m)⁻¹)) *
        (sv l * (g' * (y' ⟨k₀', c' k₀'⟩ ^ m)⁻¹))⁻¹ * (y ⟨k₀, c k₀⟩ / y' ⟨k₀', c' k₀'⟩) ^ m := by
    rw [div_pow]
    field_simp
  apply inv_not_mem_locIn _ p' (t j) hmemp (mul_ne_zero hhj hg'ne)
  change (h j * g')⁻¹ ∈ _
  rw [hkey]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) (pow_mem ?_ m)
  · rw [hzeq]; exact inv_mem_locIn _ p _ hj
  · rw [hzeq]; exact mem_locIn _ p ⟨_, hw⟩
  · exact inv_mem_locIn _ p' _ hl
  · exact mem_locIn _ p' ⟨_, hratio⟩

end ModelChangeGen


open ModelChangeGen in
theorem ModelChangeGen.proof (hT : ModelTwistGenerated.Statement) : ModelChangeGen.Statement := by
  intro F _ Ω _ _ N K _ _ ι _ y k₀ e K' _ _ ι' _ y' k₀' e' hy hy' hx β β' hs n h hh
  have hpts := modelPts_eq_of_base F y k₀ e y' k₀' e' hy hy' hx
  have h0 : secOver F y β = secOver F y' β' := by simpa using hs 0
  have hh' : ∀ j, h j ∈ secOver F y' β' := fun j => h0 ▸ hh j
  obtain ⟨c₀, hc₀⟩ := hT F K ι Ω y k₀ inferInstance hy β
  obtain ⟨c₀', hc₀'⟩ := hT F K' ι' Ω y' k₀' inferInstance hy' β'
  have hm := hc₀ (c₀.toNat : ℕ) (Int.self_le_toNat c₀)
  have hm' := hc₀' (c₀'.toNat : ℕ) (Int.self_le_toNat c₀')
  constructor
  · exact gen_of_gen (e := e) (e' := e') hpts.ge hx c₀'.toNat (hs _).ge hm' hh hh'
  · exact gen_of_gen (e := e') (e' := e) hpts.le hx.symm c₀.toNat (hs _).le hm hh' hh

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremS
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace KHTheoremS

def FinVanAt (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (n : ℕ) : Prop :=
  ∀ (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N]
    (𝓝 : (K → ℤ) → Submodule S N), Module.Finite (MRingOver S ι) N → KH.IsMGraded S ι 𝓝 →
    (∀ c : K → ℤ, Module.Finite S (KH.cechHc ι 𝓝 c n)) ∧
    (1 ≤ n → ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → Subsingleton (KH.cechHc ι 𝓝 c n))

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem finite_of_subsingleton (X : Type) [AddCommGroup X] [Module S X] (h : Subsingleton X) :
    Module.Finite S X :=
  Module.finite_def.2 (by rw [Subsingleton.elim (⊤ : Submodule S X) ⊥]; exact Submodule.fg_bot)

theorem add_nonneg_of_le (e c : K → ℤ) (h : ∀ k, ∑ l, |e l| ≤ c k) (k : K) : 0 ≤ c k + e k := by
  have h1 : |e k| ≤ ∑ l, |e l| := Finset.single_le_sum (fun l _ => abs_nonneg (e l)) (Finset.mem_univ k)
  have h2 := neg_abs_le (e k)
  have h3 := h k
  linarith

theorem finVanAt_top (n : ℕ) (hn : ∑ k, (Fintype.card (ι k) - 1) < n) : FinVanAt S K ι n := by
  intro N _ _ _ _ 𝓝 _ _
  have h := fun c => KHCechTop.full S K ι N 𝓝 c n hn
  exact ⟨fun c => finite_of_subsingleton _ (h c), fun _ => ⟨0, fun c _ => h c⟩⟩

theorem finVanAt_step (hFree : KH.TheoremSFreeStatement) (hSES : KH.CechSESStatement)
    (hPF : KH.PrimeFiltStatement) (hS : IsNoetherianRing S) (n : ℕ) (ih : FinVanAt S K ι (n + 1)) :
    FinVanAt S K ι n := by
  intro N _ _ _ _ 𝓝 hfin hgr
  refine devissage hPF hS (fun (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N] (𝓝 : (K → ℤ) → Submodule S N) => (∀ c : K → ℤ, Module.Finite S (KH.cechHc ι 𝓝 c n)) ∧
    (1 ≤ n → ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → Subsingleton (KH.cechHc ι 𝓝 c n)))
    ⟨fun c => finite_of_subsingleton _ (cechHc_punit c n), fun _ => ⟨0, fun c _ => cechHc_punit c n⟩⟩
    ?_ ?_ N 𝓝 hfin hgr
  · intro M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h hg' hg hg'' hgg hhg hinj hsurj hex ⟨f', v'⟩ ⟨f'', v''⟩
    have hs := hSES S K ι M' M M'' 𝓜' 𝓜 𝓜'' g h hg' hg hg'' hgg hhg hinj hsurj hex
    refine ⟨fun c => (hs c n).2.2.1 hS (f' c) (f'' c), fun hn => ?_⟩
    obtain ⟨c₁, h₁⟩ := v' hn
    obtain ⟨c₂, h₂⟩ := v'' hn
    exact ⟨max c₁ c₂, fun c hc => (hs c n).1 (h₁ c fun k => le_of_max_le_left (hc k))
      (h₂ c fun k => le_of_max_le_right (hc k))⟩
  · intro 𝔭 _ hhom e
    obtain ⟨hgN, hgF, hgQ, hgi, hgq, hinj, hsurj, hex⟩ := quotSES 𝔭 hhom e
    have hs := hSES S K ι (idealSub 𝔭) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) (MRingOver S ι ⧸ 𝔭)
      _ (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (fun d => KH.quotPart S 𝔭 (d + e))
      (idealSub 𝔭).subtype (quotMap 𝔭) hgN hgF hgQ hgi hgq hinj hsurj hex
    obtain ⟨fN, vN⟩ := ih (idealSub 𝔭) _ (idealSub_finite hS 𝔭) hgN
    refine ⟨fun c => (hs c n).2.2.2.1 hS ((hFree S K ι e).1 c n) (fN c), fun hn => ?_⟩
    obtain ⟨c₁, h₁⟩ := vN (Nat.le_succ_of_le hn)
    refine ⟨max c₁ (∑ l, |e l|), fun c hc => (hs c n).2.1 ?_ (h₁ c fun k => le_of_max_le_left (hc k))⟩
    exact (hFree S K ι e).2.1 c n hn
      (add_nonneg_of_le e c fun k => le_of_max_le_right (hc k))

theorem finVanAt_all (hFree : KH.TheoremSFreeStatement) (hSES : KH.CechSESStatement)
    (hPF : KH.PrimeFiltStatement) (hS : IsNoetherianRing S) (n : ℕ) : FinVanAt S K ι n := by
  have key : ∀ t n : ℕ, ∑ k, (Fintype.card (ι k) - 1) < n + t → FinVanAt S K ι n := by
    intro t
    induction t with
    | zero => exact fun n h => finVanAt_top n h
    | succ t ih => exact fun n h => finVanAt_step hFree hSES hPF hS n (ih (n + 1) (by omega))
  exact key (∑ k, (Fintype.card (ι k) - 1) + 1) n (by omega)

theorem onto (hFree : KH.TheoremSFreeStatement) (hSES : KH.CechSESStatement)
    (hPF : KH.PrimeFiltStatement) (hS : IsNoetherianRing S)
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (hfin : Module.Finite (MRingOver S ι) M) (hgr : KH.IsMGraded S ι 𝓜) :
    ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) → ∀ z ∈ KH.cechZc ι 𝓜 c 0,
      ∃ m ∈ 𝓜 c, ∀ I, z I = LocalizedModule.mk m 1 := by
  refine devissage hPF hS (fun (N : Type) [AddCommGroup N] [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N] (𝓝 : (K → ℤ) → Submodule S N) => ∃ c₀ : ℤ, ∀ c : K → ℤ, (∀ k, c₀ ≤ c k) →
    ∀ z ∈ KH.cechZc ι 𝓝 c 0, ∃ m ∈ 𝓝 c, ∀ I, z I = LocalizedModule.mk m 1)
    ⟨0, fun _ _ z _ => ⟨0, Submodule.zero_mem _, fun _ => Subsingleton.elim (α := LocalizedModule _ PUnit) _ _⟩⟩
    ?_ ?_ M 𝓜 hfin hgr
  · intro M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h hg' hg hg'' hgg hhg hinj hsurj hex ⟨a, ha⟩ ⟨b, hb⟩
    have hs := hSES S K ι M' M M'' 𝓜' 𝓜 𝓜'' g h hg' hg hg'' hgg hhg hinj hsurj hex
    refine ⟨max a b, fun c hc z hz => ?_⟩
    obtain ⟨m'', hm'', hz''⟩ := hb c (fun k => le_of_max_le_right (hc k)) _ (cechMap_mem_cechZc hhg hz)
    obtain ⟨m, hm, rfl⟩ := exists_mem_of_surjective hg hg'' hhg hsurj hm''
    have hw : z - (fun _ => LocalizedModule.mk m 1) ∈ KH.cechZc ι 𝓜 c 0 := sub_mem hz (const_mem_cechZc hm)
    have hw0 : KH.cechMap S ι h 0 (z - fun _ => LocalizedModule.mk m 1) = 0 := by
      funext I
      rw [map_sub, Pi.sub_apply, hz'' I]
      show LocalizedModule.mk (h m) 1 - lmap (KH.cellMon S I.1) h (LocalizedModule.mk m 1) = 0
      rw [lmap_mk, sub_self]
    obtain ⟨z', hz', hgz'⟩ := (hs c 0).2.2.2.2.2 _ hw hw0
    obtain ⟨m', hm', hz'I⟩ := ha c (fun k => le_of_max_le_left (hc k)) z' hz'
    refine ⟨g m' + m, add_mem (hgg c m' hm') hm, fun I => ?_⟩
    have e1 : z I - LocalizedModule.mk m 1 = LocalizedModule.mk (g m') 1 := by
      have := congrFun hgz' I
      rw [Pi.sub_apply] at this
      rw [← this]
      show lmap (KH.cellMon S I.1) g (z' I) = _
      rw [hz'I I, lmap_mk]
    calc z I = (z I - LocalizedModule.mk m 1) + LocalizedModule.mk m 1 := (sub_add_cancel _ _).symm
      _ = LocalizedModule.mk (g m') 1 + LocalizedModule.mk m 1 := by rw [e1]
      _ = LocalizedModule.mk (g m' + m) 1 := by rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
  · intro 𝔭 _ hhom e
    obtain ⟨hgN, hgF, hgQ, hgi, hgq, hinj, hsurj, hex⟩ := quotSES 𝔭 hhom e
    have hs := hSES S K ι (idealSub 𝔭) (MRingOver S ι ⧸ (⊥ : Ideal (MRingOver S ι))) (MRingOver S ι ⧸ 𝔭)
      _ (fun d => KH.quotPart S (⊥ : Ideal (MRingOver S ι)) (d + e)) (fun d => KH.quotPart S 𝔭 (d + e))
      (idealSub 𝔭).subtype (quotMap 𝔭) hgN hgF hgQ hgi hgq hinj hsurj hex
    obtain ⟨c₁, h₁⟩ := (finVanAt_all hFree hSES hPF hS 1 (idealSub 𝔭) _ (idealSub_finite hS 𝔭) hgN).2 le_rfl
    refine ⟨max c₁ (∑ l, |e l|), fun c hc z hz => ?_⟩
    obtain ⟨zF, hzF, rfl⟩ := (hs c 0).2.2.2.2.1 (h₁ c fun k => le_of_max_le_left (hc k)) z hz
    obtain ⟨f, hf, hfI⟩ := (hFree S K ι e).2.2 c (add_nonneg_of_le e c fun k => le_of_max_le_right (hc k)) zF hzF
    exact ⟨quotMap 𝔭 f, hgq c f hf, fun I => by
      show lmap (KH.cellMon S I.1) (quotMap 𝔭) (zF I) = _
      rw [hfI I, lmap_mk]⟩

end KHTheoremS

theorem KHTheoremS.proof (hFree : KH.TheoremSFreeStatement) (hSES : KH.CechSESStatement)
    (hPF : KH.PrimeFiltStatement) : KH.TheoremSStatement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 hS hfin hgr
  have hFV := fun n => KHTheoremS.finVanAt_all (ι := ι) hFree hSES hPF hS n M 𝓜 hfin hgr
  obtain ⟨c₃, h₃⟩ := KHTheoremS.onto hFree hSES hPF hS M 𝓜 hfin hgr
  refine ⟨fun c n => (hFV n).1 c, ?_, ⟨c₃, h₃⟩, ?_⟩
  ·
    have hb : ∀ B : ℕ, ∃ c₀ : ℤ, ∀ (c : K → ℤ) (n : ℕ), 1 ≤ n → n ≤ B → (∀ k, c₀ ≤ c k) →
        Subsingleton (KH.cechHc ι 𝓜 c n) := by
      intro B
      induction B with
      | zero => exact ⟨0, fun c n h1 h2 _ => absurd h2 (by omega)⟩
      | succ B ih =>
        obtain ⟨c₀, h₀⟩ := ih
        obtain ⟨c₁, h₁⟩ := (hFV (B + 1)).2 (by omega)
        refine ⟨max c₀ c₁, fun c n h1 h2 hc => ?_⟩
        rcases Nat.lt_or_ge n (B + 1) with h | h
        · exact h₀ c n h1 (by omega) fun k => le_of_max_le_left (hc k)
        · rw [show n = B + 1 by omega]
          exact h₁ c fun k => le_of_max_le_right (hc k)
    obtain ⟨c₀, h₀⟩ := hb (∑ k, (Fintype.card (ι k) - 1))
    refine ⟨c₀, fun c n h1 hc => ?_⟩
    rcases Nat.lt_or_ge (∑ k, (Fintype.card (ι k) - 1)) n with h | h
    · exact KHCechTop.full S K ι M 𝓜 c n h
    · exact h₀ c n h1 h hc
  ·

    intro d
    have : IsNoetherianRing (MRingOver S ι) := inferInstance
    let c₁ : ℕ := (c₃ + ∑ k, |d k|).toNat
    let diag : M →ₗ[MRingOver S ι] KH.CechC S ι M 0 :=
      LinearMap.pi fun I => LocalizedModule.mkLinearMap (KH.cellMon S I.1) M
    let Z : ℕ → Submodule S (KH.CechC S ι M 0) := fun c => KH.cechZc ι 𝓜 (d + fun _ => (c : ℤ)) 0
    have hZfg : ∀ c, (Submodule.span (MRingOver S ι) (Z c : Set (KH.CechC S ι M 0))).FG := by
      intro c
      have h0 : (KH.cechBc ι 𝓜 (d + fun _ => (c : ℤ)) 0).comap (Z c).subtype = ⊥ := by
        show (⊥ : Submodule S _).comap (Z c).subtype = ⊥
        rw [Submodule.comap_bot, Submodule.ker_subtype]
      have hfinZ : Module.Finite S (Z c) := by
        have := (hFV 0).1 (d + fun _ => (c : ℤ))
        exact Module.Finite.equiv (Submodule.quotEquivOfEqBot _ h0)
      obtain ⟨s, hs⟩ := Module.Finite.iff_fg.mp hfinZ
      refine ⟨s, ?_⟩
      rw [← hs, Submodule.span_span_of_tower]
    have hle : Submodule.span (MRingOver S ι) (⋃ c : ℕ, (Z c : Set (KH.CechC S ι M 0))) ≤
        (⨆ c : Fin c₁, Submodule.span (MRingOver S ι) (Z c : Set (KH.CechC S ι M 0))) ⊔ LinearMap.range diag := by
      rw [Submodule.span_le]
      intro z hz
      obtain ⟨c, hzc⟩ := Set.mem_iUnion.mp hz
      rcases Nat.lt_or_ge c c₁ with h | h
      · exact Submodule.mem_sup_left (Submodule.mem_iSup_of_mem (⟨c, h⟩ : Fin c₁) (Submodule.subset_span hzc))
      · refine Submodule.mem_sup_right ?_
        have hc : ∀ k, c₃ ≤ d k + (c : ℤ) := by
          intro k
          have h1 : |d k| ≤ ∑ l, |d l| := Finset.single_le_sum (fun l _ => abs_nonneg (d l)) (Finset.mem_univ k)
          have h2 := neg_abs_le (d k)
          have h3 : c₃ + ∑ l, |d l| ≤ (c : ℤ) := by
            have := Int.self_le_toNat (c₃ + ∑ l, |d l|)
            have h4 : ((c₁ : ℕ) : ℤ) ≤ (c : ℤ) := by exact_mod_cast h
            simp only [c₁] at h4
            linarith
          linarith
        obtain ⟨m, -, hm⟩ := h₃ _ (fun k => hc k) z hzc
        exact ⟨m, funext fun I => (hm I).symm⟩
    refine Submodule.FG.of_le (Submodule.FG.sup (Submodule.fg_iSup
      (fun c : Fin c₁ => Submodule.span (MRingOver S ι) (Z c : Set (KH.CechC S ι M 0))) fun c => hZfg c) ?_) hle
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map diag

end

end GroundTheory.Heights₂.Heights.Kleiman
end
