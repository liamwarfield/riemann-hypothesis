module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ADensStC
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsConjInvariantHZcomb
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsFinite

variable {K : Type} [Fintype K] {ι : K → Type} [∀ κ, Fintype (ι κ)] {Ω : Type} [Field Ω]

noncomputable def expo (d : K → ℕ) : K →₀ ℕ := Finsupp.equivFunOnFinite.symm d

@[simp] theorem coe_expo (d : K → ℕ) : ⇑(expo d) = d := Finsupp.coe_equivFunOnFinite_symm d

theorem mapDomain_fst_apply (μ : (Σ κ, ι κ) →₀ ℕ) (κ : K) :
    μ.mapDomain Sigma.fst κ = ∑ i, μ ⟨κ, i⟩ := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_sigma]
  simp [Finsupp.single_apply]


omit [Fintype K] [∀ κ, Fintype (ι κ)] in
theorem mConeMap_monomial (y : (Σ κ, ι κ) → Ω) (μ : (Σ κ, ι κ) →₀ ℕ) (r : ℤ) :
    mConeMap y (monomial μ r) = monomial (μ.mapDomain Sigma.fst) (aeval y (monomial μ r)) := by
  rw [mConeMap, aeval_monomial, aeval_monomial, monomial_eq,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
    MvPolynomial.algebraMap_apply]
  ring

theorem mConeMap_of_homog (y : (Σ κ, ι κ) → Ω) {g : MRing ι} {d : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d) :
    mConeMap y g = monomial (expo d) (aeval y g) := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [mConeMap_monomial]
  have hμd : μ.mapDomain Sigma.fst = expo d := by
    ext κ
    rw [mapDomain_fst_apply, coe_expo, hg μ hμ κ]
  rw [hμd]

def formRing (y : (Σ κ, ι κ) → Ω) : Subalgebra ℤ (MvPolynomial K Ω) where
  carrier := {F | ∀ m : K →₀ ℕ, AddMonoidAlgebra.coeff F m ∈ secM y ⇑m}
  mul_mem' := by
    classical
    intro F G hF hG m
    rw [coeff_mul]
    refine sum_mem fun x hx => ?_
    have hm : ⇑x.1 + ⇑x.2 = ⇑m := by rw [← Finsupp.coe_add, (Finset.HasAntidiagonal.mem_antidiagonal.mp hx)]
    rw [← hm]
    exact secM_mul_mem y (hF x.1) (hG x.2)
  add_mem' := by
    intro F G hF hG m
    rw [MvPolynomial.coeff_add]
    exact add_mem (hF m) (hG m)
  algebraMap_mem' := by
    classical
    intro n m
    rw [MvPolynomial.algebraMap_apply, coeff_C]
    split_ifs with h
    · subst h
      have h1 : (1 : Ω) ∈ secM y ⇑(0 : K →₀ ℕ) :=
        Submodule.subset_span ⟨1, ProjLine.isMultiHomog_one, map_one _⟩
      have := zsmul_mem h1 n
      simpa using this
    · exact zero_mem _

theorem mConeMap_mem_formRing (y : (Σ κ, ι κ) → Ω) (f : MRing ι) : mConeMap y f ∈ formRing y := by
  classical
  induction f using MvPolynomial.induction_on with
  | C n =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact Subalgebra.algebraMap_mem _ n
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hp fun m => ?_
    rw [mConeMap, aeval_X, coeff_C_mul, coeff_X]
    split_ifs with h
    · subst h
      refine Submodule.subset_span ⟨X q, ?_, by simp⟩
      convert ProjLine.isMultiHomog_X (ι := ι) q using 1
      funext κ
      simp [Finsupp.single_apply, eq_comm]
    · simp

theorem monomial_mem_range (y : (Σ κ, ι κ) → Ω) {d : K → ℕ} {v : Ω} (hv : v ∈ secM y d) :
    monomial (expo d) v ∈ (mConeMap y).range := by
  change v ∈ Submodule.span ℤ _ at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, hg, rfl⟩ := hx
    exact ⟨g, mConeMap_of_homog y hg⟩
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul n x _ hx => rw [map_zsmul]; exact zsmul_mem hx n

theorem proof (h : KH.CondStatement) : NmSectionsFinite.Statement := by
  unfold NmSectionsFinite.Statement
  intro K _ ι _ Ω _ y a ha hy hbir τ₂
  classical
  obtain ⟨k, c, -, hc0, hc⟩ := h K ι Ω y a ha hy hbir
  set R := (mConeMap y).range
  have : IsNoetherianRing R :=
    isNoetherianRing_of_surjective (MRing ι) R (mConeMap y).rangeRestrict.toRingHom
      (mConeMap y).rangeRestrict_surjective

  set G : Set (MvPolynomial K Ω) := {F | ∃ τ, τ₂ ≤ τ ∧ ∃ s ∈ chartLatNm y (fun κ => (a κ : ℤ)) τ,
    F = monomial (expo fun κ => τ * a κ) s}
  set u : MvPolynomial K Ω := monomial (expo fun κ => k * a κ) (aeval y c)
  have hinj : Function.Injective (LinearMap.mulLeft R u) := by
    intro F F' hF
    simp only [LinearMap.mulLeft_apply] at hF
    exact mul_left_cancel₀ (by simpa [u] using hc0) hF
  have hmap : (Submodule.span R G).map (LinearMap.mulLeft R u) ≤ Submodule.span R {1} := by
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨F, ⟨τ, -, s, hs, rfl⟩, rfl⟩
    rw [LinearMap.mulLeft_apply, monomial_mul]
    have hdeg : expo (fun κ => k * a κ) + expo (fun κ => τ * a κ) = expo fun κ => (τ + k) * a κ := by
      ext κ; simp; ring
    rw [hdeg]
    obtain ⟨g, hg⟩ := monomial_mem_range y (hc τ s hs)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    exact ⟨⟨_, g, rfl⟩, by rw [Subalgebra.smul_def, smul_eq_mul, mul_one]; exact hg⟩
  have hfg : (Submodule.span R G).FG := by
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have := isNoetherian_of_fg_of_noetherian (Submodule.span R {(1 : MvPolynomial K Ω)})
      (Submodule.fg_span_singleton 1)
    exact isNoetherian_submodule.mp inferInstance _ hmap
  obtain ⟨t, htG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  choose d hd e he hte using fun j : t => htG j.2
  refine ⟨t, inferInstance, d, e, max τ₂ (Finset.univ.sup d), fun j => ⟨hd j,
    le_max_of_le_right (Finset.le_sup (Finset.mem_univ j)), he j⟩, ?_⟩
  intro τ hτ s hs
  have hdτ : ∀ j, d j ≤ τ := fun j =>
    le_trans (le_max_of_le_right (Finset.le_sup (Finset.mem_univ j))) hτ
  have hmem : monomial (expo fun κ => τ * a κ) s ∈ Submodule.span R (t : Set (MvPolynomial K Ω)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨τ, le_trans (le_max_left _ _) hτ, s, hs, rfl⟩
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hmem
  have hR : ∀ F, ((f F : R) : MvPolynomial K Ω) ∈ formRing y := by
    intro F
    obtain ⟨g, hg⟩ := (f F).2
    rw [← hg]
    exact mConeMap_mem_formRing y g
  refine ⟨fun j => AddMonoidAlgebra.coeff ((f j : R) : MvPolynomial K Ω) (expo fun κ => (τ - d j) * a κ), fun j => ?_, ?_⟩
  · simpa using hR j (expo fun κ => (τ - d j) * a κ)
  · have hc' := congrArg (AddMonoidAlgebra.coeff · (expo fun κ => τ * a κ)) hf
    rw [coeff_monomial, if_pos rfl] at hc'
    rw [← hc', coeff_sum, ← Finset.sum_coe_sort t]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul]
    set p := ((f j : R) : MvPolynomial K Ω)
    rw [hte j]
    rw [coeff_mul_monomial', if_pos]
    · congr 2
      ext κ
      simp [Nat.sub_mul]
    · intro κ
      simpa using Nat.mul_le_mul_right (a κ) (hdτ j)

end NmSectionsFinite

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGradedSubquot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GradedSubquot

set_option linter.unusedSectionVars false

theorem iSupIndep_comap {R N M : Type*} [Ring R] [AddCommGroup N] [AddCommGroup M] [Module R N] [Module R M]
    {κ : Type*} {p : κ → Submodule R M} (hp : iSupIndep p) (g : N →ₗ[R] M) (hg : Function.Injective g) :
    iSupIndep fun i => (p i).comap g := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ i), (p j).comap g) ≤ (⨆ (j) (_ : j ≠ i), p j).comap g :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j hj)
  have h0 := (Submodule.disjoint_def.mp (hp i)) (g x) (Submodule.mem_comap.mp hx) (Submodule.mem_comap.mp (hle hx'))
  exact hg (by rw [h0, map_zero])

theorem iSupIndep_map_of_ker_le {R N Q : Type*} [Ring R] [AddCommGroup N] [AddCommGroup Q] [Module R N]
    [Module R Q] {κ : Type*} {p : κ → Submodule R N} (hp : iSupIndep p) (f : N →ₗ[R] Q)
    (hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ p c)) :
    iSupIndep fun i => (p i).map f := by
  rw [iSupIndep_def] at hp ⊢
  intro i
  rw [Submodule.disjoint_def]
  intro y hy hy'
  obtain ⟨x, hx, rfl⟩ := hy
  have hy2 : f x ∈ (⨆ (j) (_ : j ≠ i), p j).map f := by
    simpa only [Submodule.map_iSup] using hy'
  obtain ⟨z, hz, hzx⟩ := hy2
  have hk : x - z ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  have hk' := hL hk
  rw [iSup_split_single (fun c => LinearMap.ker f ⊓ p c) i, Submodule.mem_sup] at hk'
  obtain ⟨l, hl, w, hw, hlw⟩ := hk'
  have hw1 : w ∈ ⨆ (j) (_ : j ≠ i), p j :=
    (show (⨆ (j) (_ : j ≠ i), LinearMap.ker f ⊓ p j) ≤ ⨆ (j) (_ : j ≠ i), p j from
      iSup₂_mono fun j _ => inf_le_right) hw
  have hxl : x - l ∈ p i := sub_mem hx (Submodule.mem_inf.mp hl).2
  have hxl' : x - l ∈ ⨆ (j) (_ : j ≠ i), p j := by
    have e : x - l = z + w := by
      calc x - l = (x - z) - l + z := by abel
        _ = z + w := by rw [← hlw]; abel
    rw [e]
    exact Submodule.add_mem _ hz hw1
  have h0 := (Submodule.disjoint_def.mp (hp i)) (x - l) hxl hxl'
  rw [sub_eq_zero.mp h0]
  exact LinearMap.mem_ker.mp (Submodule.mem_inf.mp hl).1

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]

theorem isMultiHomog_monomial (d : (Σ k, ι k) →₀ ℕ) (r : S) (a : K → ℕ)
    (hd : ∀ k, ∑ i, d ⟨k, i⟩ = a k) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial d r : MRingOver S ι) a := by
  classical
  intro m hm k
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)]
  exact hd k


variable (S ι) in
def monTimes (H : Set M) : Set M :=
  {y | ∃ (u : (Σ k, ι k) →₀ ℕ) (h : M), h ∈ H ∧ y = (monomial u (1 : S) : MRingOver S ι) • h}

theorem monTimes_subset_span (H : Set M) : monTimes S ι H ⊆ Submodule.span (MRingOver S ι) H := by
  rintro _ ⟨u, h, hh, rfl⟩
  exact Submodule.smul_mem _ _ (Submodule.subset_span hh)

theorem span_monTimes_le (H : Set M) :
    Submodule.span S (monTimes S ι H) ≤ (Submodule.span (MRingOver S ι) H).restrictScalars S :=
  Submodule.span_le.mpr (monTimes_subset_span H)

theorem monomial_smul_mem (H : Set M) (u : (Σ k, ι k) →₀ ℕ) {y : M}
    (hy : y ∈ Submodule.span S (monTimes S ι H)) :
    (monomial u (1 : S) : MRingOver S ι) • y ∈ Submodule.span S (monTimes S ι H) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, h, hh, rfl⟩ := hx
    refine Submodule.subset_span ⟨u + v, h, hh, ?_⟩
    rw [smul_smul, monomial_mul, one_mul]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [smul_add]; exact Submodule.add_mem _ hx hz
  | smul s x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ s hx

theorem span_le_span_monTimes (H : Set M) :
    (Submodule.span (MRingOver S ι) H).restrictScalars S ≤ Submodule.span S (monTimes S ι H) := by
  let T : Submodule (MRingOver S ι) M :=
    { carrier := Submodule.span S (monTimes S ι H)
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro p y hy
        refine MvPolynomial.induction_on' p (fun u a => ?_) (fun p q hp hq => ?_)
        · have e : (monomial u a : MRingOver S ι) = a • monomial u (1 : S) := by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
          rw [e, smul_assoc]
          exact Submodule.smul_mem _ a (monomial_smul_mem H u hy)
        · rw [add_smul]
          exact Submodule.add_mem _ hp hq }
  have hT : Submodule.span (MRingOver S ι) H ≤ T := by
    rw [Submodule.span_le]
    intro h hh
    have e : h = (monomial 0 (1 : S) : MRingOver S ι) • h := by
      rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_smul]
    exact Submodule.subset_span ⟨0, h, hh, e⟩
  exact fun x hx => hT hx

theorem monTimes_homog {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {y : M} (hy : y ∈ monTimes S ι H) : ∃ c, y ∈ 𝓜 c := by
  obtain ⟨u, h, hh, rfl⟩ := hy
  obtain ⟨c, hc⟩ := hH h hh
  exact ⟨_, hM.2 (fun k => ∑ i, u ⟨k, i⟩) c _ h (isMultiHomog_monomial u 1 _ fun _ => rfl) hc⟩

theorem mem_iSup_inf {𝓜 : (K → ℤ) → Submodule S M} (hM : KH.IsMGraded S ι 𝓜) {H : Set M}
    (hH : ∀ x ∈ H, ∃ c, x ∈ 𝓜 c) {N : Submodule (MRingOver S ι) M}
    (hHN : Submodule.span (MRingOver S ι) H ≤ N) (x : N) (hx : (x : M) ∈ Submodule.span (MRingOver S ι) H) :
    x ∈ ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
  obtain ⟨x, hxN⟩ := x
  have hmem : ∀ y ∈ Submodule.span S (monTimes S ι H), ∀ hy : y ∈ N, (⟨y, hy⟩ : N) ∈
      ⨆ c, ((Submodule.span (MRingOver S ι) H).comap N.subtype).restrictScalars S ⊓ subGrading 𝓜 N c := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro _
      obtain ⟨c, hc⟩ := monTimes_homog hM hH hy
      exact Submodule.mem_iSup_of_mem c (Submodule.mem_inf.mpr ⟨monTimes_subset_span H hy, hc⟩)
    | zero => intro _; exact Submodule.zero_mem _
    | add y z hy hz ihy ihz =>
      intro _
      exact Submodule.add_mem _ (ihy (hHN (span_monTimes_le H hy))) (ihz (hHN (span_monTimes_le H hz)))
    | smul s y hy ihy =>
      intro _
      exact Submodule.smul_mem _ s (ihy (hHN (span_monTimes_le H hy)))
  exact hmem x (span_le_span_monTimes H hx) hxN

end GradedSubquot


open GradedSubquot in
theorem GradedSubquot.proof : GradedSubquot.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 G H hM hG hH hGH

  have hind : iSupIndep (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) :=
    iSupIndep_comap hM.1.submodule_iSupIndep ((Submodule.span (MRingOver S ι) H).subtype.restrictScalars S)
      (fun a b h => Subtype.ext h)
  have hsup : ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    exact (show (⨆ c, ((Submodule.span (MRingOver S ι) H).comap (Submodule.span (MRingOver S ι) H).subtype).restrictScalars S ⊓
        subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) ≤ ⨆ c, subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c from
      iSup_mono fun c => inf_le_right) (mem_iSup_inf hM hH le_rfl x x.2)
  refine ⟨⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind hsup,
    fun a c p m hp hm => hM.2 a c p (m : M) hp hm⟩, ?_⟩

  set L := (Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype with hLdef
  set f := L.mkQ.restrictScalars S with hfdef
  have hker : LinearMap.ker f = L.restrictScalars S := by
    ext x
    simp [hfdef]
  have hL : LinearMap.ker f ≤ ⨆ c, (LinearMap.ker f ⊓ subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c) := by
    rw [hker]
    intro x hx
    exact mem_iSup_inf hM hG hGH x hx
  have hind2 := iSupIndep_map_of_ker_le hind f hL
  have hsup2 : ⨆ c, quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) L c = ⊤ := by
    change ⨆ c, (subGrading 𝓜 (Submodule.span (MRingOver S ι) H) c).map f = ⊤
    rw [← Submodule.map_iSup, hsup, Submodule.map_top, LinearMap.range_eq_top]
    exact Submodule.mkQ_surjective L
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind2 hsup2, ?_⟩
  rintro a c p _ hp ⟨x, hx, rfl⟩
  exact ⟨p • x, hM.2 a c p (x : M) hp hx, L.mkQ.map_smul p x⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.InverseDerivativeContinuity
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

namespace G1

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem geoNum_nonneg : ∀ (n : ℕ) (V : Ideal (MRing ι)) (b : Fin n → K → ℤ),
    (∀ j k, 0 ≤ b j k) → 0 ≤ geoNum n V b
  | 0, V, b, _ => by
    unfold geoNum
    split_ifs <;> positivity
  | n + 1, V, b, hb => by
    rw [geoNum]
    split_ifs with h
    · refine Finset.sum_nonneg fun k _ => mul_nonneg (hb _ k) ?_
      exact finsum_nonneg fun W => finsum_nonneg fun _ =>
        mul_nonneg (Nat.cast_nonneg _) (geoNum_nonneg n W (Fin.init b) fun j k => hb _ k)
    · exact le_rfl

theorem finsum_nonpos' {α : Sort*} {g : α → ℝ} (h : ∀ x, g x ≤ 0) : ∑ᶠ x, g x ≤ 0 := by
  have h0 : 0 ≤ ∑ᶠ x, -g x := finsum_nonneg fun x => neg_nonneg.2 (h x)
  rw [finsum_neg_distrib] at h0
  exact neg_nonneg.1 h0

theorem mcPts_anti {P W : Ideal (MRing ι)} (h : P ≤ W) : mcPts W ⊆ mcPts P :=
  fun _ hz => ⟨hz.1, fun f hf => hz.2 f (h hf)⟩

theorem isOpen_blocksNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [e]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem exists_monomial_not_mem {P : Ideal (MRing ι)} (hP : IsMultiProjPrime P) (a : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = a k) ∧ monomial μ (1 : ℤ) ∉ P := by
  classical
  choose c hc using hP.2.2
  let μ : (Σ k, ι k) →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun p => if p.2 = c p.1 then a p.1 else 0
  refine ⟨μ, fun k => ?_, ?_⟩
  · simp [μ]
  · intro hmem
    have := hP.1
    rw [monomial_eq, C_1, one_mul, Finsupp.prod] at hmem
    obtain ⟨p, hp, hpP⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
    have hX := hP.1.mem_of_pow_mem _ hpP
    have hμp : μ p ≠ 0 := Finsupp.mem_support_iff.1 hp
    obtain ⟨k, j⟩ := p
    by_cases hj : j = c k
    · subst hj
      exact hc k hX
    · exact hμp (by simp [μ, hj])

theorem isMultiHomog_monomial {μ : (Σ k, ι k) →₀ ℕ} {a : K → ℕ} (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = a k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (monomial μ (1 : ℤ)) a := by
  intro m hm k
  rw [Finset.mem_singleton.1 (support_monomial_subset hm)]
  exact hμ k

theorem eval_monomial_one (μ : (Σ k, ι k) →₀ ℕ) (z : (Σ k, ι k) → ℂ) :
    eval z (map (Int.castRingHom ℂ) (monomial μ (1 : ℤ))) = ∏ p, z p ^ μ p := by
  rw [map_monomial, eval_monomial, map_one, one_mul, Finsupp.prod_fintype]
  intro p
  simp

theorem isConeTangent_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {e : ℕ}
    {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y)
    (hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P) (ξ : Fin e → ℂ) :
    IsConeTangent (Int.castRingHom ℂ) P0 (γ y) (fderiv ℂ γ y ξ) := by
  intro f hf
  set F := map (Int.castRingHom ℂ) f
  have hzero : (fun w => eval w F) ∘ γ =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
    filter_upwards [hpts] with w hw
    exact hw.2 f (hP0 hf)
  have hd := (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_hasFDerivAt_eval F (γ y)).comp y
    hγ.differentiableAt.hasFDerivAt
  have h0 : HasFDerivAt ((fun w => eval w F) ∘ γ) (0 : (Fin e → ℂ) →L[ℂ] ℂ) y :=
    (hasFDerivAt_const (0 : ℂ) y).congr_of_eventuallyEq hzero
  have := congrArg (fun L => L ξ) (hd.unique h0)
  simpa [ContinuousLinearMap.sum_apply, smul_eq_mul] using this

theorem maDensity_nonneg_of_sheet {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun _ y' => Real.log (A.h (γ y'))) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 A.h (γ y) :=
    (hsp.1.contDiffAt (isOpen_blocksNonzero.mem_nhds hy.1)).of_le (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (A.h z)) (γ y) := hh.log (A.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (A.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2 fun ξ => ?_
  have hl := ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (A.h z)) ξ hA hlog
  change 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (A.h z)) ∘ γ) y ξ
  rw [hl]
  exact hsp.2 _ hy _ (isConeTangent_of_sheet hP0 hA hpts ξ)

theorem arInt_nonpos {P0 P : Ideal (MRing ι)} (hP0 : P0 ≤ P) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hsp : IsSemipositiveRel P0 P A) {s : MRing ι}
    (hs : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z) (e : ℕ) :
    arInt P s A (fun _ : Fin e => A) ≤ 0 := by
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    refine integral_nonpos fun y => ?_
    have key : ∀ w, sheetDensity P hΨ.choose (fun (_ : Fin e) z => Real.log (A.h z))
        (logNorm A s) y w ≤ 0 := by
      intro w
      unfold sheetDensity
      split_ifs with hγ
      · have hsh := hγ.choose_spec
        have hz : hγ.choose y ∈ mcPts P := hsh.2.self_of_nhds.2.1
        have hpos := A.pos _ hz.1
        have hg : logNorm A s (hγ.choose y) ≤ 0 :=
          Real.log_nonpos (div_nonneg (norm_nonneg _) hpos.le)
            ((div_le_one hpos).2 (hs _ hz))
        exact mul_nonpos_of_nonpos_of_nonneg hg (maDensity_nonneg_of_sheet hP0 hsp hsh)
      · exact le_rfl
    exact finsum_nonpos' fun w => finsum_nonpos' fun _ => key w
  · exact le_rfl

theorem nonneg_of_family (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ)
    (hI : IsIntersectionFamily I) (a : K → ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hA : A.a = fun k => (a k : ℤ))
    (P0 : Ideal (MRing ι)) (n : ℕ) :
    ∀ P : Ideal (MRing ι), IsArithVar P n → P0 ≤ P → IsSemipositiveRel P0 P A →
      MonomialsBounded P A a → 0 ≤ I P n (fun _ => A) := by
  induction n with
  | zero =>
    intro P hP
    exact (GroundTheory.Heights₂.Heights.Inter.arithVarZero K ι P hP).elim
  | succ m ih =>
    intro P hP hP0 hsp hmb
    obtain ⟨μ, hμ, hμP⟩ := exists_monomial_not_mem hP.2.1 a
    set s : MRing ι := monomial μ (1 : ℤ) with hsdef
    have hsa : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a := isMultiHomog_monomial hμ
    have hAa : ∀ k, A.a k = a k := fun k => by rw [hA]
    have hsmall : ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) s)‖ ≤ A.h z := by
      intro z hz
      rw [hsdef, eval_monomial_one]
      exact hmb z hz μ hμ
    have hR := hI.2.2 P m (fun _ => A) A s a hP (fun _ => hsp.1) hsp.1 hAa hsa hμP
    have hconst : (Fin.snoc (fun _ : Fin m => A) A : Fin (m + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) = fun _ => A := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [hconst] at hR
    rw [hR, recR]
    refine sub_nonneg.2 (le_trans (arInt_nonpos hP0 hsp hsmall m)
      (finsum_nonneg fun W => finsum_nonneg fun hW => mul_nonneg (Nat.cast_nonneg _) ?_))
    have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
    split_ifs with hH
    · have hWar := (divSuppArith K ι P m A s W hP ⟨a, hAa, hsa, hμP⟩ hW).1 hH
      exact ih W hWar (hP0.trans hPW) ⟨hsp.1, fun z hz w hw => hsp.2 z (mcPts_anti hPW hz) w hw⟩
        (fun z hz μ' hμ' => hmb z (mcPts_anti hPW hz) μ' hμ')
    · refine mul_nonneg (Int.cast_nonneg (geoNum_nonneg m W _ fun j k => ?_))
        (Real.log_natCast_nonneg _)
      simp [hA]

end G1

theorem G1.proof : G1.Statement := by
  intro K _ ι _ Ω _ y D a A P0 II _ hII hP _ hA hP0 hsp hmb _
  exact G1.nonneg_of_family (II K ι) (hII K ι) a A hA P0 (D + 1) _ hP hP0 hsp hmb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageArithmetic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem ringKrullDim_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (CoordinateConeArithVar.ratioField y c)).toENat + Fintype.card K + 1 : ℕ∞) :
        WithBot ℕ∞) := by
  have hhor := CoordinateConeArithVar.horizontal y
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have htr := ConeTrdeg.proof K ι (CoordinateConeArithVar.ratioField y c)
    (CoordinateConeArithVar.ratioPtL y c) (CoordinateConeArithVar.birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [CoordinateConeArithVar.ratioPtL, CoordinateConeArithVar.ratioPt, hc] at h1⟩)
    (by rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL y c hc] at htr
  rw [IntDomainDim.proof (MRing ι ⧸ mCoordIdeal y)
    (CoordinateConeArithVar.algebraMap_injective _ hhor), htr]
  simp only [map_add (f := _), map_natCast]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem div_mem_of_sum (F : IntermediateField ℚ Ω) {A B : Type} [Fintype B] (u : A → Ω) (v : B → Ω)
    (L : Matrix A B ℤ) (hu : ∀ a, u a = ∑ b, (L a b : Ω) * v b) (b₀ : B)
    (hF : ∀ b, v b / v b₀ ∈ F) (a : A) : u a / v b₀ ∈ F := by
  rw [hu, Finset.sum_div]
  refine sum_mem fun b _ ↦ ?_
  rw [mul_div_assoc]
  exact mul_mem (intCast_mem F _) (hF b)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ratio_mem_of_sum (F : IntermediateField ℚ Ω) {A B : Type} [Fintype B] (u : A → Ω) (v : B → Ω)
    (L : Matrix A B ℤ) (hu : ∀ a, u a = ∑ b, (L a b : Ω) * v b) (b₀ : B) (hv : v b₀ ≠ 0)
    (hF : ∀ b, v b / v b₀ ∈ F) (a a' : A) : u a / u a' ∈ F := by
  rw [← div_div_div_cancel_right₀ hv (u a) (u a')]
  exact div_mem (div_mem_of_sum F u v L hu b₀ hF a) (div_mem_of_sum F u v L hu b₀ hF a')


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)


omit [Fintype K] [CharZero Ω] in
theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X p : MRing ι) (fun k ↦ if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k', i'⟩ := p
  by_cases h : k = k'
  · subst h
    rw [Finset.sum_eq_single i']
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [h]


omit [CharZero Ω] in
theorem aeval_mul_pow_of_block (y w : (Σ k, ι k) → Ω) (k₀ : K) (z : Ω)
    (hw : ∀ i, w ⟨k₀, i⟩ * z = y ⟨k₀, i⟩) {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (hd : ∀ k, k ≠ k₀ → d k = 0) : aeval w f * z ^ d k₀ = aeval y f := by
  classical
  conv_rhs => rw [f.as_sum]
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  have hsum : ∑ p, m p = d k₀ := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single k₀]
    · exact hf m hm k₀
    · intro k _ hk
      rw [hf m hm k, hd k hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hzero : ∀ p : Σ k, ι k, p.1 ≠ k₀ → m p = 0 := by
    intro p hp
    have h1 := hf m hm p.1
    rw [hd _ hp] at h1
    exact (Finset.sum_eq_zero_iff.mp h1) p.2 (Finset.mem_univ _)
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [← mul_pow]
  by_cases hp : p.1 = k₀
  · obtain ⟨k, i⟩ := p
    simp only at hp
    subst hp
    rw [hw i]
  · rw [hzero p hp, pow_zero, pow_zero]

end BlockImageArithmetic


open BlockImageArithmetic in
theorem BlockImageArith.proof : BlockImageArith.Statement := by
  intro D K _ _ ι _ Ω _ _ y k₀ r M N x hY hbir hB _
  classical
  obtain ⟨hK, ⟨_, _, hrel⟩, _, hdim⟩ := hY
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hnz
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hc k₀
    rw [hB.2 (c k₀)]
    simp [h]
  let c' : ∀ k, GlobalTheory (Fin r) k := fun _ ↦ j₀.2
  have hc' : ∀ k, x ⟨k, c' k⟩ ≠ 0 := fun _ ↦ hj₀
  set Fy := CoordinateConeArithVar.ratioField y c with hFy
  set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory (Fin r)) x c' with hFx
  have hxF : ∀ j, x j / x j₀ ∈ Fx := fun j ↦ IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
  have hLx : Fx ≤ Fy := by
    rw [hFx, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact ratio_mem_of_sum Fy x (fun i ↦ y ⟨k₀, i⟩) M hB.1 (c k₀) (hc k₀)
      (fun i ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k₀, i⟩, rfl⟩) p ⟨p.1, c' p.1⟩
  have hLy : Fy ≤ Fx := by
    rw [hFy, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx
    have hyF : ∀ i, y ⟨k₀, i⟩ / x j₀ ∈ Fx := fun i ↦
      div_mem_of_sum Fx (fun i ↦ y ⟨k₀, i⟩) x N hB.2 j₀ hxF i
    let w : (Σ k, ι k) → Ω := fun p ↦ if p.1 = k₀ then y p / x j₀ else 0
    have hwF : ∀ p, w p ∈ Fx := by
      rintro ⟨k', i'⟩
      by_cases h : k' = k₀
      · subst h
        simp only [w, ite_true]
        exact hyF i'
      · simp only [w, h, ite_false]
        exact zero_mem _
    have hw : ∀ i, w ⟨k₀, i⟩ * x j₀ = y ⟨k₀, i⟩ := fun i ↦ by
      simp only [w, ite_true]
      exact div_mul_cancel₀ _ hj₀
    obtain ⟨n, g', h', hg', hh', hh0, heq⟩ := hbir _ (X ⟨k, i⟩) (X ⟨k, c k⟩)
      (isMultiHomog_X_single ⟨k, i⟩) (isMultiHomog_X_single ⟨k, c k⟩)
      (by rw [aeval_X]; exact hc k)
    rw [aeval_X, aeval_X] at heq
    have hd : ∀ k', k' ≠ k₀ → blockDeg k₀ n k' = 0 := fun k' hk' ↦ by simp [blockDeg, hk']
    have e1 := aeval_mul_pow_of_block y w k₀ (x j₀) hw hg' hd
    have e2 := aeval_mul_pow_of_block y w k₀ (x j₀) hw hh' hd
    have hwh : aeval w h' ≠ 0 := fun h0 ↦ hh0 (by rw [← e2, h0, zero_mul])
    have hrat : y ⟨k, i⟩ / y ⟨k, c k⟩ = aeval w g' / aeval w h' := by
      rw [div_eq_div_iff (hc k) hwh]
      apply mul_right_cancel₀ (pow_ne_zero (blockDeg k₀ n k₀) hj₀)
      linear_combination heq + y ⟨k, i⟩ * e2 - y ⟨k, c k⟩ * e1
    rw [hrat]
    exact div_mem (aeval_mem Fx w hwF g') (aeval_mem Fx w hwF h')
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

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Module.finrank ℤ (AddSubgroup.toIntSubmodule (chartLat y a n)) = Module.finrank ℚ (chartLatQ y a n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockFnField
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def TwoBlockFnField.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsInvMat B →
      blockFnField (ι := FinTwoTypeFamily κ) (pair x (matAct B x)) = blockFnField (ι := GlobalTheory κ) x ∧
        blockFnField (ι := GlobalTheory κ) (matAct B x) = blockFnField (ι := GlobalTheory κ) x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockStepBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockStepBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    ∃ K : ℝ, ∀ a b : ℕ, |twoBlockStep x (matAct B x) a b| ≤ K * ((a + b : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedSectionStep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def MixedSectionStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P P0 : Ideal (MRing ι)) (d : ℕ)
    (M H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem),
    IsIntersectionSystem II → 2 ≤ d → IsArithVar P d → P0 ≤ P →
    IsSemipositiveRel P0 P M → NefOnFibres P M.a → IsConjInvariantH M →
    (∀ W, IsArithVar W 1 → P ≤ W → 0 ≤ II K ι W 1 ![M]) →
    (H.a = fun _ => (1 : ℤ)) → IsSemipositiveRel P0 P H → MonomialsBounded P H (fun _ => 1) → IsConjInvariantH H →
    MixedKleiman.AtDim (d - 1) →
    ∀ q p : ℕ, 1 ≤ p → 0 < II K ι P d (fun _ => HermLine.zcomb M H (q : ℤ) (p : ℤ)) →
      0 ≤ II K ι P d (fun j : Fin d => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (M : Fin D → ConeMetric ℂ (Ix κ)) (m₁ : ConeMetric ℂ (Ix κ)),
    (∀ j, IsSmoothMetric (M j)) → IsSmoothMetric m₁ →
    ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (fun j z => Real.log ((M j).ρ z)) (logRatio d.m m₁) =
      mInt d.R.A (fun j => resPot d (M j)) (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
