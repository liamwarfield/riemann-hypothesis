module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGraphChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistGenerated

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenSESStep

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem isMultiHomog_mul {p q : MRingOver S ι} {a b : K → ℕ} (hp : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a)
    (hq : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog q b) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (p * q) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hp m₁ h₁ k, hq m₂ h₂ k]

theorem isMultiHomog_X (k : K) (i : ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X ⟨k, i⟩ : MRingOver S ι) (fun l => if l = k then 1 else 0) := by
  classical
  intro m hm l
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  by_cases hl : l = k
  · subst hl
    simp [Finsupp.single_apply]
  · have : ∀ j : ι l, (Finsupp.single (⟨k, i⟩ : Σ k, ι k) 1) ⟨l, j⟩ = 0 := by
      intro j
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hl (congrArg Sigma.fst h).symm
    simp [this, hl]

theorem cellMon_homog {I : ∀ k, Finset (ι k)} {u : MRingOver S ι} (hu : u ∈ KH.cellMon S I) :
    ∃ e : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u e := by
  induction hu using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, -, rfl⟩ := hf
    exact ⟨_, isMultiHomog_X k i⟩
  | one => exact ⟨0, isMultiHomog_one_zero⟩
  | mul f f' _ _ hf hf' =>
    obtain ⟨a, ha⟩ := hf
    obtain ⟨b, hb⟩ := hf'
    exact ⟨a + b, isMultiHomog_mul ha hb⟩

section Loc

variable {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M}

theorem mk_mem_locPart {T : Submonoid (MRingOver S ι)} {c : K → ℤ} (m : M) (t : T) (a : K → ℕ)
    (ht : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (t : MRingOver S ι) a) (hm : m ∈ 𝓜 (c + fun k => (a k : ℤ))) :
    LocalizedModule.mk m t ∈ KH.locPart ι 𝓜 T c :=
  Submodule.subset_span ⟨m, t, a, ht, hm, rfl⟩

theorem locPart_normal (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {x : LocalizedModule T M} (hx : x ∈ KH.locPart ι 𝓜 T c) :
    ∃ (m : M) (t : T) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (t : MRingOver S ι) a ∧
      m ∈ 𝓜 (c + fun k => (a k : ℤ)) ∧ x = LocalizedModule.mk m t := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, 1, 0, isMultiHomog_one_zero, zero_mem _, (LocalizedModule.zero_mk 1).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    obtain ⟨m', t', a', ht', hm', rfl⟩ := hy
    have e : ∀ a a' : K → ℕ, (c + fun k => ((a + a') k : ℤ)) =
        (c + fun k => (a k : ℤ)) + fun k => (a' k : ℤ) := by
      intro a a'
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    refine ⟨t' • m + t • m', t * t', a + a', isMultiHomog_mul ht ht', add_mem ?_ ?_,
      LocalizedModule.mk_add_mk⟩
    · rw [Submonoid.smul_def, e]
      exact h𝓜.2 _ _ _ _ ht' hm
    · rw [Submonoid.smul_def, add_comm a a', e]
      exact h𝓜.2 _ _ _ _ ht hm'
  | smul s x _ hx =>
    obtain ⟨m, t, a, ht, hm, rfl⟩ := hx
    exact ⟨s • m, t, a, ht, Submodule.smul_mem _ s hm, LocalizedModule.smul'_mk s m t⟩

theorem smul_mem_locPart (h𝓜 : KH.IsMGraded S ι 𝓜) {T : Submonoid (MRingOver S ι)} {c : K → ℤ}
    {p : MRingOver S ι} {a : K → ℕ} (hp : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a) {x : LocalizedModule T M}
    (hx : x ∈ KH.locPart ι 𝓜 T c) : p • x ∈ KH.locPart ι 𝓜 T (c + fun k => (a k : ℤ)) := by
  obtain ⟨m, t, b, ht, hm, rfl⟩ := locPart_normal h𝓜 hx
  rw [LocalizedModule.smul'_mk]
  refine mk_mem_locPart _ t b ht ?_
  have e : ((c + fun k => (a k : ℤ)) + fun k => (b k : ℤ)) =
      (c + fun k => (b k : ℤ)) + fun k => (a k : ℤ) := by
    funext k
    simp only [Pi.add_apply]
    ring
  rw [e]
  exact h𝓜.2 _ _ _ _ hp hm

abbrev locMap {N : Type*} [AddCommGroup N] [Module (MRingOver S ι) N] (T : Submonoid (MRingOver S ι))
    (f : M →ₗ[MRingOver S ι] N) : LocalizedModule T M →ₗ[MRingOver S ι] LocalizedModule T N :=
  IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M) (LocalizedModule.mkLinearMap T N) f

theorem locMap_mk {N : Type*} [AddCommGroup N] [Module (MRingOver S ι) N] {T : Submonoid (MRingOver S ι)}
    (f : M →ₗ[MRingOver S ι] N) (m : M) (t : T) :
    locMap T f (LocalizedModule.mk m t) = LocalizedModule.mk (f m) t := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']

theorem mem_of_map_mem {M' : Type*} [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] {𝓜' : (K → ℤ) → Submodule S M'} (h𝓜' : KH.IsMGraded S ι 𝓜')
    (h𝓜 : KH.IsMGraded S ι 𝓜) {g : M' →ₗ[MRingOver S ι] M} (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g)
    (hinj : Function.Injective g) {c : K → ℤ} {m' : M'} (hm : g m' ∈ 𝓜 c) : m' ∈ 𝓜' c := by
  classical
  have key : ∃ y ∈ 𝓜' c, g m' - g y ∈ ⨆ (j) (_ : j ≠ c), 𝓜 j := by
    have hx : m' ∈ ⨆ j, 𝓜' j := by
      rw [h𝓜'.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun x => ∃ y ∈ 𝓜' c, g x - g y ∈ ⨆ (j) (_ : j ≠ c), 𝓜 j)
      𝓜' hx ?_ ?_ ?_
    · intro j x hx
      by_cases hj : j = c
      · subst hj
        exact ⟨x, hx, by rw [sub_self]; exact zero_mem _⟩
      · refine ⟨0, zero_mem _, ?_⟩
        rw [map_zero, sub_zero]
        exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hg j x hx))
    · exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    · intro x₁ x₂ h₁ h₂
      obtain ⟨y₁, hy₁, e₁⟩ := h₁
      obtain ⟨y₂, hy₂, e₂⟩ := h₂
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
      have : g (x₁ + x₂) - g (y₁ + y₂) = (g x₁ - g y₁) + (g x₂ - g y₂) := by
        simp only [map_add (f := _)]
        abel
      rw [this]
      exact add_mem e₁ e₂
  obtain ⟨y, hy, hd⟩ := key
  have hc : g m' - g y ∈ 𝓜 c := sub_mem hm (hg c y hy)
  have h0 : g m' - g y = 0 := Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep c) _ hc hd
  rw [sub_eq_zero] at h0
  rw [hinj h0]
  exact hy

end Loc

theorem proof (hSES : KH.CechSESStatement) (hMap : KH.CechMapDegStatement) : GenSESStep.Statement := by
  intro S _ K _ _ ι _ _ M' _ _ _ _ M _ _ _ _ M'' _ _ _ _ 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex d
    hH1 hgen' hgen'' I x hx

  obtain ⟨m₀, t₀, a₀, ht₀, hm₀, rfl⟩ := locPart_normal h𝓜 hx
  have hx'' : LocalizedModule.mk (h m₀) t₀ ∈ KH.locPart ι 𝓜'' (KH.cellMon S I.1) d :=
    mk_mem_locPart _ _ a₀ ht₀ (hh _ _ hm₀)
  obtain ⟨t₁, a₁, r, p, z'', ht₁T, ht₁, hp, hz'', e₁⟩ := hgen'' I _ hx''

  have hlift := fun j => (hSES S K ι M' M M'' 𝓜' 𝓜 𝓜'' g h h𝓜' h𝓜 h𝓜'' hg hh hinj hsurj hex d
    0).2.2.2.2.1 hH1 (z'' j) (hz'' j)
  choose z hz hzmap using hlift
  have hzI : ∀ j, z j I ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d :=
    fun j => Submodule.mem_pi.mp (hz j).1 I (Set.mem_univ _)
  have hzh : ∀ j, locMap (KH.cellMon S I.1) h (z j I) = z'' j I := fun j => congrFun (hzmap j) I

  obtain ⟨y, hy_def⟩ : ∃ y, y = t₁ • LocalizedModule.mk m₀ t₀ - ∑ j, p j • z j I := ⟨_, rfl⟩
  have hLy : locMap (KH.cellMon S I.1) h y = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy_def, map_sub, map_smul, map_sum, locMap_mk, e₁, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hzh]
  have hyloc : y ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) (d + fun k => (a₁ k : ℤ)) := by
    rw [hy_def]
    exact sub_mem (smul_mem_locPart h𝓜 ht₁ hx)
      (Submodule.sum_mem _ fun j _ => smul_mem_locPart h𝓜 (hp j) (hzI j))
  obtain ⟨m, s, b, hs, hm, hys⟩ := locPart_normal h𝓜 hyloc

  have h0 : LocalizedModule.mk (h m) s = 0 := by rw [← locMap_mk, ← hys]; exact hLy
  rw [← LocalizedModule.zero_mk (1 : KH.cellMon S I.1), LocalizedModule.mk_eq] at h0
  obtain ⟨u, hu⟩ := h0
  rw [one_smul, smul_zero, smul_zero] at hu
  have hker : u • m ∈ LinearMap.ker h := by
    rw [LinearMap.mem_ker, Submonoid.smul_def, map_smul, ← Submonoid.smul_def]
    exact hu
  rw [← hex] at hker
  obtain ⟨m', hm'⟩ := hker
  obtain ⟨e, hue⟩ := cellMon_homog u.2
  have hm'deg : m' ∈ 𝓜' (((d + fun k => (a₁ k : ℤ)) + fun k => (b k : ℤ)) + fun k => (e k : ℤ)) := by
    refine mem_of_map_mem h𝓜' h𝓜 hg hinj ?_
    rw [hm', Submonoid.smul_def]
    exact h𝓜.2 _ _ _ _ hue hm

  let v : KH.cellMon S I.1 := ⟨t₁, ht₁T⟩ * u * s
  have hv : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (v : MRingOver S ι) (a₁ + e + b) := isMultiHomog_mul (isMultiHomog_mul ht₁ hue) hs
  have hy'' : LocalizedModule.mk m' v ∈ KH.locPart ι 𝓜' (KH.cellMon S I.1) d := by
    refine mk_mem_locPart _ v _ hv ?_
    have edeg : (d + fun k => ((a₁ + e + b) k : ℤ)) =
        ((d + fun k => (a₁ k : ℤ)) + fun k => (b k : ℤ)) + fun k => (e k : ℤ) := by
      funext k
      simp only [Pi.add_apply, Nat.cast_add]
      ring
    rw [edeg]
    exact hm'deg
  obtain ⟨t₂, a₂, r', p', z', ht₂T, ht₂, hp', hz', e₂⟩ := hgen' I _ hy''

  have hw : ∀ l, KH.cechMap S ι g 0 (z' l) ∈ KH.cechZc ι 𝓜 d 0 := by
    intro l
    obtain ⟨h1, h2⟩ := hMap S K ι M' M 𝓜' 𝓜 g d 0 hg
    refine ⟨h1 _ (hz' l).1, LinearMap.mem_ker.mpr ?_⟩
    rw [← LinearMap.comp_apply, h2, LinearMap.comp_apply, LinearMap.mem_ker.mp (hz' l).2, map_zero]
  have hgv : (t₁ : MRingOver S ι) • locMap (KH.cellMon S I.1) g (LocalizedModule.mk m' v) = y := by
    rw [locMap_mk, LocalizedModule.smul'_mk, hm', hys]
    have : (t₁ : MRingOver S ι) • (u • m) = ((⟨t₁, ht₁T⟩ * u : KH.cellMon S I.1) • m) := by
      rw [Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_mul, mul_smul]
    rw [this]
    exact LocalizedModule.mk_cancel_common_left _ _ _
  have hgy : t₂ • y = t₁ • ∑ l, p' l • KH.cechMap S ι g 0 (z' l) I := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hgv, ← mul_smul, mul_comm, mul_smul, ← map_smul, e₂, map_sum]
    refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
    rw [map_smul]
    rfl
  refine ⟨t₂ * t₁, a₂ + a₁, r + r', Fin.append (fun j => t₂ * p j) (fun l => t₁ * p' l),
    Fin.append z (fun l => KH.cechMap S ι g 0 (z' l)), mul_mem ht₂T ht₁T, isMultiHomog_mul ht₂ ht₁,
    fun j => ?_, fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
      exact isMultiHomog_mul ht₂ (hp j)
    · rw [Fin.append_right, add_comm]
      exact isMultiHomog_mul ht₁ (hp' l)
  · refine Fin.addCases (fun j => ?_) (fun l => ?_) j
    · rw [Fin.append_left]
      exact hz j
    · rw [Fin.append_right]
      exact hw l
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have hyeq : t₁ • LocalizedModule.mk m₀ t₀ = y + ∑ j, p j • z j I := by
      rw [hy_def, sub_add_cancel]
    rw [mul_smul, hyeq, smul_add, hgy, Finset.smul_sum, Finset.smul_sum, add_comm]
    simp only [smul_smul]

end GenSESStep

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SegreArithmetic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]


omit [DecidableEq K] in
theorem segreCoords_div (y : (Σ k, ι k) → Ω) (f c : (k : K) → ι k) :
    segreCoords y ⟨(), f⟩ / segreCoords y ⟨(), c⟩ = ∏ k, y ⟨k, f k⟩ / y ⟨k, c k⟩ := by
  simp only [segreCoords, Finset.prod_div_distrib]

theorem ratio_eq_segre (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ =
      segreCoords y ⟨(), Function.update c k i⟩ / segreCoords y ⟨(), c⟩ := by
  rw [segreCoords_div, Finset.prod_eq_single k]
  · rw [Function.update_self]
  · intro j _ hj
    rw [Function.update_of_ne hj]
    exact div_self (hc j)
  · intro h
    exact absurd (Finset.mem_univ k) h


omit [Fintype K] [DecidableEq K] in
theorem charZero_of_horizontal (y : (Σ k, ι k) → Ω)
    (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) (A := Ω) ?_
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro n hn
  have hmem : n ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes,
      MvPolynomial.algebraMap_apply, C_eq_zero]
    exact hn
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from h] at hmem
  exact (Ideal.mem_bot).mp hmem

end SegreArithmetic


open SegreArithmetic BlockImageArithmetic in
theorem SegreArith.proof : SegreArith.Statement := by
  intro K _ _ ι _ Ω _ y D hY
  classical
  obtain ⟨hK, ⟨_, _, hrel⟩, hhor, hdim⟩ := hY
  have : CharZero Ω := charZero_of_horizontal y hhor
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hnz
  set x := segreCoords y with hx
  let c' : ∀ u, GlobalTheory ((k : K) → ι k) u := fun _ ↦ c
  have hx0 : x ⟨(), c⟩ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  have hc' : ∀ u, x ⟨u, c' u⟩ ≠ 0 := fun _ ↦ hx0
  set Fy := CoordinateConeArithVar.ratioField y c with hFy
  set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory ((k : K) → ι k)) x c' with hFx
  have hLx : Fx ≤ Fy := by
    rw [hFx, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨u, f⟩, rfl⟩
    show x ⟨u, f⟩ / x ⟨u, c⟩ ∈ Fy
    rw [hx, segreCoords_div]
    exact prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, f k⟩, rfl⟩
  have hLy : Fy ≤ Fx := by
    rw [hFy, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx
    rw [ratio_eq_segre y c hc k i]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨(), Function.update c k i⟩, rfl⟩
  have hLeq : Fy = Fx := le_antisymm hLy hLx
  have hdy := ringKrullDim_eq y c hc
  rw [hdim] at hdy
  rw [coordIdeal_eq_mCoordIdeal]
  refine ⟨⟨()⟩, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal x,
    CoordinateConeArithVar.relevant x c' hc'⟩, CoordinateConeArithVar.horizontal x, ?_⟩
  rw [ringKrullDim_eq x c' hc']
  rw [← hFy, hLeq] at hdy
  generalize (Algebra.trdeg ℤ Fx).toENat = t at hdy ⊢
  have h1 : ((D + 1 + Fintype.card K : ℕ) : ℕ∞) = t + Fintype.card K + 1 := by exact_mod_cast hdy
  induction t using ENat.recTopCoe with
  | top => simp at h1
  | coe t =>
    have h2 : D + 1 + Fintype.card K = t + Fintype.card K + 1 := by exact_mod_cast h1
    have h3 : t = D := by omega
    subst h3
    rw [Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem TwoBlockFnField.ratio_mem {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (p q : Ix κ) : x p / x q ∈ blockFnField (ι := GlobalTheory κ) x :=
  IntermediateField.subset_adjoin ℚ _ ⟨p, q, Subsingleton.elim _ _, rfl⟩

theorem TwoBlockFnField.matAct_le {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (A : Matrix (Ix κ) (Ix κ) ℚ) :
    blockFnField (ι := GlobalTheory κ) (matAct A x) ≤ blockFnField (ι := GlobalTheory κ) x := by
  rw [blockFnField, IntermediateField.adjoin_le_iff]
  rintro t ⟨p, q, -, rfl⟩
  by_cases h0 : ∀ j, x j = 0
  · have : matAct A x p = 0 := by simp [matAct, h0]
    rw [this, zero_div]
    exact zero_mem _
  · obtain ⟨c, hc⟩ := not_forall.mp h0
    have key : ∀ i, matAct A x i / x c ∈ blockFnField (ι := GlobalTheory κ) x := by
      intro i
      have : matAct A x i / x c = ∑ j, (A i j : Ω) * (x j / x c) := by
        simp only [matAct, Finset.sum_div, mul_div_assoc]
      rw [this]
      refine sum_mem fun j _ => mul_mem ?_ (TwoBlockFnField.ratio_mem x j c)
      simp
    have : matAct A x p / matAct A x q = (matAct A x p / x c) / (matAct A x q / x c) := by
      rw [div_div_div_cancel_right₀ hc]
    rw [this]
    exact div_mem (key p) (key q)

theorem TwoBlockFnField.matAct_eq {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (hB : IsInvMat B) :
    blockFnField (ι := GlobalTheory κ) (matAct B x) = blockFnField (ι := GlobalTheory κ) x := by
  classical
  obtain ⟨B', -, h⟩ := isInvMat_mul hB
  refine le_antisymm (TwoBlockFnField.matAct_le x B) ?_
  have := TwoBlockFnField.matAct_le (matAct B x) B'
  rwa [matAct_matAct h] at this

theorem TwoBlockFnField.proof : TwoBlockFnField.Statement := by
  intro Ω _ _ κ _ x B hB
  have hE := TwoBlockFnField.matAct_eq x B hB
  refine ⟨le_antisymm ?_ ?_, hE⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    obtain ⟨b, i⟩ := p
    obtain ⟨b', j⟩ := q
    simp only at hpq
    subst hpq
    by_cases hb : b = 0
    · subst hb
      simpa [pair] using TwoBlockFnField.ratio_mem x ⟨(), i⟩ ⟨(), j⟩
    · simp only [pair, hb, if_false]
      rw [← hE]
      exact TwoBlockFnField.ratio_mem (matAct B x) ⟨(), i⟩ ⟨(), j⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨u, i⟩, ⟨u', j⟩, -, rfl⟩
    cases u; cases u'
    refine IntermediateField.subset_adjoin ℚ _ ⟨⟨0, i⟩, ⟨0, j⟩, rfl, ?_⟩
    simp [pair]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

section Shift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
  {y : (Σ k, ι k) → Ω}


omit [Fintype K] in
theorem shift_succ_sub_one (b : K → ℤ) (j : ℕ) :
    (b + fun _ => ((j + 1 : ℕ) : ℤ)) - 1 = b + fun _ => (j : ℤ) := by
  funext k
  simp only [Pi.sub_apply, Pi.add_apply, Pi.one_apply]
  push_cast
  ring


omit [∀ k, Fintype (ι k)] in
theorem pow_mul_mem_chartLatQ (c : ∀ k, ι k) (b : K → ℤ) {s : Ω} (hs : s ∈ chartLatQ y b 1) (j : ℕ) :
    (∏ k, y ⟨k, c k⟩) ^ j * s ∈ chartLatQ y (b + fun _ => (j : ℤ)) 1 := by
  induction j with
  | zero =>
    rw [pow_zero, one_mul]
    have h0 : (b + fun _ => ((0 : ℕ) : ℤ)) = b := by funext k; simp
    rw [h0]
    exact hs
  | succ j ih =>
    rw [← shift_succ_sub_one] at ih
    have h := mul_mem_chartLatQ (c := c) (b + fun _ => ((j + 1 : ℕ) : ℤ)) ih
    rwa [← mul_assoc, ← pow_succ'] at h

theorem finiteDimensional_chartLatQ (hfin : SectionLatticeFinite.Statement) (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (b : K → ℤ) : FiniteDimensional ℚ (chartLatQ y b 1) := by
  classical
  obtain ⟨S, hS⟩ := hfin K ι Ω y b 1 hy
  let T : Finset Ω := S.image Subtype.val
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℚ (T : Set Ω)) fun s hs => ?_
  obtain ⟨N, hN, hNs⟩ := ChartDenominator.proof K ι Ω y b 1 s hs
  have ht : (⟨(N : Ω) * s, hNs⟩ : chartLat y b 1) ∈ AddSubsemigroup.closure (S : Set (chartLat y b 1)) := by
    rw [hS]
    trivial
  have hQ : (N : Ω) * s ∈ Submodule.span ℚ (T : Set Ω) := by
    have hall : ∀ x : chartLat y b 1, x ∈ AddSubsemigroup.closure (S : Set (chartLat y b 1)) → (x : Ω) ∈ Submodule.span ℚ (T : Set Ω) := by
      intro x hx
      induction hx using AddSubsemigroup.closure_induction with
      | mem x hx =>
        apply Submodule.subset_span
        exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      | add x z hx hz ihx ihz =>
        exact Submodule.add_mem _ ihx ihz
    exact hall _ ht
  have hN0 : (N : Ω) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs' : s = ((N : ℚ)⁻¹) • ((N : Ω) * s) := by
    rw [Rat.smul_def]
    push_cast
    field_simp
  rw [hs']
  exact Submodule.smul_mem _ _ hQ

theorem finrank_shift_le (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (b : K → ℤ) (j : ℕ) :
    Module.finrank ℚ (chartLatQ y (b + fun _ => (j : ℤ)) 1) ≤ Module.finrank ℚ (chartLatQ y b 1) +
      ∑ i ∈ Finset.range j, Module.finrank ℚ (chartLatQ y (b + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
        chartDivSec y c (b + fun _ => ((i + 1 : ℕ) : ℤ))) := by
  induction j with
  | zero =>
    have h0 : (b + fun _ => ((0 : ℕ) : ℤ)) = b := by funext k; simp
    rw [h0]
    simp
  | succ j ih =>
    have h := finrank_chartLatQ_le hc (b + fun _ => ((j + 1 : ℕ) : ℤ))
    rw [shift_succ_sub_one] at h
    rw [Finset.sum_range_succ]
    omega

end Shift

theorem ShiftSectionBound.proof (hfin : SectionLatticeFinite.Statement) (hQ : ShiftQuotientBound.Statement) :
    ShiftSectionBound.Statement := by
  intro K _ ι _ Ω _ _ y D a m hD hV hB
  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker]
    simp [mConeMap, h0]
  choose c hc using hy
  have hC := fun i : ℕ => hQ K ι Ω y D a (fun _ => ((i + 1 : ℕ) : ℤ)) c hD hV hB hc
  choose C hC using hC
  refine ⟨∑ i ∈ Finset.range m, C i,
    ((Filter.eventually_all_finset (Finset.range m)).mpr fun i _ => hC i).mono fun n hn => ⟨?_, ?_⟩⟩
  ·
    have := finiteDimensional_chartLatQ hfin (fun k => ⟨c k, hc k⟩) ((n : ℤ) • a + fun _ => (m : ℤ))
    have hh : (∏ k, y ⟨k, c k⟩) ^ m ≠ 0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun k _ => hc k)
    let φ : chartLatQ y ((n : ℤ) • a) 1 →ₗ[ℚ] chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1 :=
      { toFun := fun s => ⟨(∏ k, y ⟨k, c k⟩) ^ m * s, pow_mul_mem_chartLatQ c _ s.2 m⟩
        map_add' := fun s t => Subtype.ext (mul_add _ _ _)
        map_smul' := fun r s => Subtype.ext (mul_smul_comm r _ (s : Ω)) }
    have hinj : Function.Injective φ := fun s t hst =>
      Subtype.ext (mul_left_cancel₀ hh (congrArg Subtype.val hst))
    exact_mod_cast LinearMap.finrank_le_finrank_of_injective hinj
  · have h := finrank_shift_le c hc ((n : ℤ) • a) m
    have h' : (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => (m : ℤ)) 1) : ℝ) ≤
        (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a) 1) : ℝ) +
          ∑ i ∈ Finset.range m, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
            chartDivSec y c ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ))) : ℝ) := by
      exact_mod_cast h
    have hs : ∑ i ∈ Finset.range m, (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ)) 1 ⧸
          chartDivSec y c ((n : ℤ) • a + fun _ => ((i + 1 : ℕ) : ℤ))) : ℝ) ≤
        (∑ i ∈ Finset.range m, C i) * (n : ℝ) ^ (D - 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => hn i hi
    linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMonomialShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace MonomialShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem exists_chart {y : (Σ k, ι k) → Ω} {d : ℕ} (hY : IsArithVar (mCoordIdeal y) d) :
    ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
  have hrel := hY.2.1.2.2
  refine ⟨fun k => (hrel k).choose, fun k h0 => (hrel k).choose_spec ?_⟩
  change _ ∈ RingHom.ker _
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem norm_prod_le {P : Ideal (MRing ι)} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {a : K → ℕ} (hM : MonomialsBounded P A a)
    (c : ∀ k, ι k) (j n : ℕ) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ ≤ A.h z ^ j * (fsH ι).h z ^ n := by
  classical
  have e1 : ‖∏ k, z ⟨k, c k⟩ ^ (j * a k + n)‖ =
      (∏ k, ‖z ⟨k, c k⟩‖ ^ a k) ^ j * (∏ k, ‖z ⟨k, c k⟩‖) ^ n := by
    rw [norm_prod, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow]
    ring

  let μ : (Σ k, ι k) →₀ ℕ := Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  have hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k := by
    intro k
    simp [μ]
  have hmon : ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [μ, pow_ite]
  have hA : ∏ k, ‖z ⟨k, c k⟩‖ ^ a k ≤ A.h z := by
    have := hM z hz μ hμ
    rw [hmon, norm_prod] at this
    simpa [norm_pow] using this
  have hH : ∏ k, ‖z ⟨k, c k⟩‖ ≤ (fsH ι).h z := by
    have hfs : (fsH ι).h z = ∏ k, Real.sqrt (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
      rw [fsH, GroundTheory.Heights₂.Heights.Inter.ofMetrics_fs_h]
      simp
    rw [hfs]
    refine Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) fun k _ => Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ (c k))
  rw [e1]
  gcongr
  exact pow_nonneg (A.pos z hz.1).le _

theorem isSmoothHerm_zcomb_fsH {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (q : ℕ) :
    IsSmoothHerm (HermLine.zcomb A (fsH ι) q 1) := by
  have hH : IsSmoothHerm (fsH ι) := GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs 1
  have hfun : (HermLine.zcomb A (fsH ι) q 1).h = fun z => A.h z ^ q * (fsH ι).h z := by
    funext z
    change A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) = _
    rw [zpow_natCast, zpow_one]
  unfold IsSmoothHerm at hA hH ⊢
  rw [hfun]
  exact (hA.pow q).mul hH

theorem proof (hPack : PackingStatement) : MonomialShift.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q τ n hY hBir ha hP0 hsemi hM hq hτ
  classical
  obtain ⟨c, hc⟩ := exists_chart hY

  obtain ⟨e, he⟩ : ∃ e : K → ℕ, e = fun k => (q * n - τ) * a k + n := ⟨_, rfl⟩
  have hBa : ∀ k, (HermLine.zcomb A (fsH ι) q 1).a k = (q : ℤ) * a k + 1 := by
    intro k
    simp [HermLine.zcomb, fsH, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics, ha]
  have hdeg : ∀ k, (n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k = τ * A.a k + e k := by
    intro k
    rw [hBa, he]
    simp only [ha]
    push_cast [Nat.cast_sub hτ]
    ring

  obtain ⟨mv, hmv⟩ : ∃ mv : Ω, mv = ∏ k, y ⟨k, c k⟩ ^ e k := ⟨_, rfl⟩
  have hmv0 : mv ≠ 0 := by
    rw [hmv]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  have hmvx : aeval y (xpow c e) = mv := by
    simp [hmv, xpow]

  have hlat : ∀ s ∈ chartLatNm y A.a τ, mv * s ∈ chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n := by
    intro s hs c' hc'
    have h1 := hs c' hc'
    have h2 : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ integralClosure (chartRingZ y c') Ω := by
      have hmem : ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k ∈ chartRingZ y c' :=
        Subalgebra.prod_mem _ fun k _ =>
          pow_mem (Algebra.subset_adjoin
            (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c' p.1⟩) ⟨k, c k⟩)) _
      exact (integralClosure (chartRingZ y c') Ω).algebraMap_mem ⟨_, hmem⟩
    have hsplit : ∀ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k)) * (y ⟨k, c' k⟩ ^ e k)⁻¹ := by
      intro k
      rw [hdeg k, neg_add, zpow_add₀ (hc' k), zpow_neg (y _) ((e k : ℕ) : ℤ), zpow_natCast]
    have key : mv * s * ∏ k, y ⟨k, c' k⟩ ^ (-((n : ℤ) * (HermLine.zcomb A (fsH ι) q 1).a k)) =
        (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, (y ⟨k, c k⟩ / y ⟨k, c' k⟩) ^ e k := by
      simp only [hsplit, div_eq_mul_inv, mul_pow, inv_pow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hmv]
      ring
    rw [key]
    exact mul_mem h1 h2

  have hsmall : ∀ s, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (mv * s) := by
    intro s hs dg dh g h z hg hh hd hgh hz
    have hmh := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (isMultiHomog_xpow c e) hh
    have hb := hs dg (e + dh) g (xpow c e * h) z hg hmh
      (fun k => by have := hd k; have := hdeg k; simp only [Pi.add_apply]; push_cast; linarith)
      (by rw [hgh, map_mul, hmvx]; ring) hz
    have hApos : 0 < A.h z := A.pos z hz.1
    have hxz : eval z (map (Int.castRingHom ℂ) (xpow c e)) = ∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n) := by
      simp [xpow, he]
    have hBh : (HermLine.zcomb A (fsH ι) q 1).h z = A.h z ^ ((q : ℕ) : ℤ) * (fsH ι).h z ^ (1 : ℤ) := rfl
    calc ‖eval z (map (Int.castRingHom ℂ) g)‖
        ≤ ‖eval z (map (Int.castRingHom ℂ) (xpow c e * h))‖ * A.h z ^ τ := hb
      _ = ‖∏ k, z ⟨k, c k⟩ ^ ((q * n - τ) * a k + n)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          rw [map_mul, eval_mul, norm_mul, hxz]
      _ ≤ (A.h z ^ (q * n - τ) * (fsH ι).h z ^ n) * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
          gcongr
          exact norm_prod_le hM c (q * n - τ) n hz
      _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (HermLine.zcomb A (fsH ι) q 1).h z ^ n := by
          rw [hBh, zpow_natCast, zpow_one, mul_pow, ← pow_mul,
            show A.h z ^ (q * n) = A.h z ^ (q * n - τ) * A.h z ^ τ by rw [← pow_add, Nat.sub_add_cancel hτ]]
          ring

  let f : {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} →
      {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
        IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} :=
    fun s => ⟨⟨mv * s.1, hlat s.1 s.1.2⟩, hsmall s.1 s.2⟩
  have hinj : Function.Injective f := by
    intro s t hst
    have h := congrArg (fun u => ((u.1 : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n) : Ω)) hst
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hmv0 h))
  have hfin := (hPack K ι Ω y D (HermLine.zcomb A (fsH ι) q 1)
    (chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a) hY hBir (isSmoothHerm_zcomb_fsH hsemi.1 q)
    (fun _ => le_rfl)).1 n
  have : Finite {t : chartLatNm y (HermLine.zcomb A (fsH ι) q 1).a n //
      IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) q 1) n (t : Ω)} := hfin.to_subtype
  have hcard := Nat.card_le_card_of_injective f hinj
  unfold smallSectionCount
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

end MonomialShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedRestrict.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V W : Ideal (MRingOver S ι)) (a : K → ℤ),
    V ≤ W → KH.GeneratedV S V a → KH.GeneratedV S W a

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerHeightsirational
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerHeightsirational.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, w j ∈ chartLat y a 1) →
    KH.GeneratesOn y a w → 0 < genDeg (mCoordIdeal y) D a →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (N : ℕ) (v : Fin N → Ω), AddSubgroup.closure (Set.range v) = chartLat y a m →
      BlockBirational (addBlock y v) (none : Option K)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelChartPoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelChartPoly.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (R : Subalgebra ℤ Ω)
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k),
    ∀ σ ∈ Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩),
      ∃ N : ℕ, σ * (∏ k, y ⟨k, c k⟩) ^ N ∈ relSecM R y (fun _ => N)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsVeroneseGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace Veronese

def forms (D : ℕ) : Ix (Idx D) → MRing (GlobalTheory (Fin (D + 1))) :=
  fun q => X ⟨(), q.2.1.1⟩ * X ⟨(), q.2.1.2⟩

end Veronese

def VeroneseGraphImage.Statement : Prop :=
  ∀ D : ℕ, imageZ (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D)))
      (graphIdeal ⊥ (Veronese.forms D)) = coordIdeal ℤ (Veronese.x D)

def VeroneseGraphDeg.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (graphIdeal ⊥ (Veronese.forms D)))
      (J : IFamily G.Φ (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) (Sum.inr : Unit → Unit ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedNonzeroSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def GeneratedNonzeroSection.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (n : K → ℤ),
    KH.GeneratedV ℚ (KH.genIdeal y) n → ∃ s ∈ chartLat y n 1, s ≠ 0

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerBlockArith.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (m N : ℕ) (v : Fin N → Ω),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, v j ∈ chartLat y a m) →
    KH.GeneratesOn y (fun k => (m : ℤ) * a k) v → IsArithVar (mCoordIdeal (addBlock y v)) (D + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
