module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGenLocal
section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartNakayamaGenAgree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def chart (c : ∀ k, ι k) : KH.Cell K ι 0 :=
  ⟨fun k => {c k}, fun k => Finset.singleton_nonempty _, by simp⟩

theorem eq_chart (J : KH.Cell K ι 0) : J = chart (fun k => (J.2.1 k).choose) := by
  apply Subtype.ext
  funext k
  have h0 : (J.1 k).card - 1 = 0 := (Finset.sum_eq_zero_iff.mp J.2.2) k (Finset.mem_univ k)
  have h1 : (J.1 k).card = 1 := by have := Finset.card_pos.mpr (J.2.1 k); omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
  have hc : (J.2.1 k).choose ∈ J.1 k := (J.2.1 k).choose_spec
  show J.1 k = {(J.2.1 k).choose}
  generalize (J.2.1 k).choose = x at hc ⊢
  rw [ha, Finset.mem_singleton] at hc
  rw [ha, hc]

def chartMon (c : ∀ k, ι k) (e : K → ℕ) : MRingOver S ι :=
  ∏ k, (X ⟨k, c k⟩ : MRingOver S ι) ^ e k

theorem chartMon_add (c : ∀ k, ι k) (e f : K → ℕ) :
    chartMon (S := S) c (e + f) = chartMon c e * chartMon c f := by
  simp only [chartMon, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem chartMon_zero (c : ∀ k, ι k) : chartMon (S := S) c 0 = 1 := by
  simp [chartMon]

theorem chartMon_mem (c : ∀ k, ι k) (e : K → ℕ) : chartMon (S := S) c e ∈ KH.cellMon S (chart c).1 :=
  Submonoid.prod_mem _ fun k _ =>
    Submonoid.pow_mem _ (by
      apply Submonoid.subset_closure
      exact ⟨k, c k, Finset.mem_singleton_self _, rfl⟩) _

theorem isMultiHomog_pow {p : MRingOver S ι} {a : K → ℕ} (hp : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a) (n : ℕ) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (p ^ n) (n • a) := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    exact isMultiHomog_one_zero
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact GenSESStep.isMultiHomog_mul ih hp

theorem isMultiHomog_prod {β : Type} (s : Finset β) (f : β → MRingOver S ι) (a : β → K → ℕ)
    (h : ∀ i ∈ s, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f i) (a i)) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ i ∈ s, f i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Finset.sum_empty]
    exact isMultiHomog_one_zero
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact GenSESStep.isMultiHomog_mul (h b (Finset.mem_insert_self b s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isMultiHomog_chartMon (c : ∀ k, ι k) (e : K → ℕ) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (chartMon (S := S) c e) e := by
  classical
  have h := isMultiHomog_prod (S := S) Finset.univ (fun k => (X ⟨k, c k⟩ : MRingOver S ι) ^ e k)
    (fun k => e k • fun l => if l = k then 1 else 0)
    (fun k _ => isMultiHomog_pow (GenSESStep.isMultiHomog_X k (c k)) (e k))
  have he : (∑ k, e k • fun l : K => if l = k then (1 : ℕ) else 0) = e := by
    funext l
    simp [Finset.sum_apply]
  rw [he] at h
  exact h

theorem exists_chartMon {c : ∀ k, ι k} {v : MRingOver S ι} (hv : v ∈ KH.cellMon S (chart c).1) :
    ∃ e, v = chartMon c e := by
  classical
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    have hik : i = c k := Finset.mem_singleton.mp hi
    subst hik
    refine ⟨Pi.single k 1, ?_⟩
    rw [chartMon, Finset.prod_eq_single k]
    · simp
    · intro l _ hl
      simp [hl]
    · intro h
      exact absurd (Finset.mem_univ k) h
  | one => exact ⟨0, (chartMon_zero c).symm⟩
  | mul f g _ _ hf hg =>
    obtain ⟨e, rfl⟩ := hf
    obtain ⟨e', rfl⟩ := hg
    exact ⟨e + e', (chartMon_add c e e').symm⟩

theorem cellMon_notMem {P : Ideal (MRingOver S ι)} (hP : P.IsPrime) {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P) {v : MRingOver S ι}
    (hv : v ∈ KH.cellMon S (chart c).1) : v ∉ P := by
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    have hik : i = c k := Finset.mem_singleton.mp hi
    subst hik
    exact hc k
  | one => exact fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  | mul f g _ _ hf hg => exact fun h => (hP.mem_or_mem h).elim hf hg

theorem dvd_of_mem_pair {c c' : ∀ k, ι k} {v : MRingOver S ι}
    (hv : v ∈ KH.cellMon S (fun k => ({c k, c' k} : Finset (ι k)))) :
    ∃ e : ℕ, v ∣ chartMon c (fun _ => e) * chartMon c' (fun _ => e) := by
  classical
  induction hv using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    refine ⟨1, ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h : (X ⟨k, c k⟩ : MRingOver S ι) ∣ chartMon c (fun _ => 1) := by
        simpa [chartMon] using
          Finset.dvd_prod_of_mem (fun l => (X ⟨l, c l⟩ : MRingOver S ι)) (Finset.mem_univ k)
      exact h.mul_right _
    · rw [Finset.mem_singleton.mp hi]
      have h : (X ⟨k, c' k⟩ : MRingOver S ι) ∣ chartMon c' (fun _ => 1) := by
        simpa [chartMon] using
          Finset.dvd_prod_of_mem (fun l => (X ⟨l, c' l⟩ : MRingOver S ι)) (Finset.mem_univ k)
      exact h.mul_left _
  | one => exact ⟨0, one_dvd _⟩
  | mul f g _ _ hf hg =>
    obtain ⟨e, he⟩ := hf
    obtain ⟨e', he'⟩ := hg
    refine ⟨e + e', ?_⟩
    have h : chartMon (S := S) c (fun _ => e + e') * chartMon c' (fun _ => e + e') =
        (chartMon c (fun _ => e) * chartMon c' (fun _ => e)) *
          (chartMon c (fun _ => e') * chartMon c' (fun _ => e')) := by
      rw [show (fun _ : K => e + e') = (fun _ => e) + (fun _ => e') from rfl, chartMon_add, chartMon_add]
      ring
    rw [h]
    exact mul_dvd_mul he he'

def pairCell (c : ∀ k, ι k) (k : K) (j : ι k) (hj : j ≠ c k) : KH.Cell K ι 1 :=
  ⟨Function.update (fun l => ({c l} : Finset (ι l))) k {c k, j}, fun l => by
      by_cases hl : l = k
      · subst hl
        simp
      · simp [Function.update_of_ne hl], by
      rw [Finset.sum_eq_single k]
      · simp [Finset.card_pair hj.symm]
      · intro l _ hl
        simp [Function.update_of_ne hl]
      · simp⟩

theorem res_eq_of_pair {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] (c : ∀ k, ι k) (k : K)
    (j : ι k) (hj : j ≠ c k) (f : KH.CechC S ι M 0) (hf : KH.cechD S ι M 0 f = 0) :
    KH.cellRes S M (chart c).1 (pairCell c k j hj).1 (f (chart c)) =
      KH.cellRes S M (chart (Function.update c k j)).1 (pairCell c k j hj).1
        (f (chart (Function.update c k j))) := by
  classical
  have h := congrFun hf (pairCell c k j hj)
  have hIk : (pairCell c k j hj).1 k = {c k, j} := by simp [pairCell]
  have hIl : ∀ l, l ≠ k → (pairCell c k j hj).1 l = {c l} := fun l hl => by
    simp [pairCell, Function.update_of_ne hl]
  generalize pairCell c k j hj = I at h hIk hIl ⊢
  have hne : ∀ l, (I.1 l).Nonempty := I.2.1
  have hxy : c k ≠ j := hj.symm
  have hx : c k ∈ I.1 k := by rw [hIk]; simp
  have hy : j ∈ I.1 k := by rw [hIk]; simp
  have hcard₀ : (I.1 k).card = 2 := by rw [hIk]; exact Finset.card_pair hxy
  have hother : ∀ l, l ≠ k → (I.1 l).card = 1 := fun l hl => by rw [hIl l hl]; rfl
  have hface : ∀ i ∈ I.1 k, (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, hcard₀]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k
      · subst hl; rw [Function.update_self]; exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]; exact hne l
    · by_cases hl : l = k
      · subst hl; rw [Function.update_self, hc]; rfl
      · rw [Function.update_of_ne hl, hother l hl]; rfl
  have hsign : KH.faceSign I.1 k j = -KH.faceSign I.1 k (c k) := by
    unfold KH.faceSign
    rcases lt_or_gt_of_ne hxy with h' | h'
    · have e₁ : ((I.1 k).filter (· < c k)).card = 0 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h'.not_gt]
      have e₂ : ((I.1 k).filter (· < j)).card = 1 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h']
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
    · have e₁ : ((I.1 k).filter (· < c k)).card = 1 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h']
      have e₂ : ((I.1 k).filter (· < j)).card = 0 := by
        rw [hIk]; simp [Finset.filter_insert, Finset.filter_singleton, h'.not_gt]
      rw [e₁, e₂, add_comm 1, pow_succ, zero_add]; ring
  have key : ∀ (c₀ : ∀ k, ι k) (a : ∀ l, Finset (ι l)) (p : (∀ l, (a l).Nonempty) ∧ ∑ l, ((a l).card - 1) = 0),
      a = (chart c₀).1 →
      KH.cellRes S M a I.1 (f ⟨a, p⟩) = KH.cellRes S M (chart c₀).1 I.1 (f (chart c₀)) := by
    rintro c₀ a p rfl
    rfl
  have f₁ : Function.update I.1 k ((I.1 k).erase (c k)) = (chart (Function.update c k j)).1 := by
    funext l
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, hIk]
      simp [chart, hxy]
    · rw [Function.update_of_ne hl, hIl l hl]
      simp [chart, Function.update_of_ne hl]
  have f₂ : Function.update I.1 k ((I.1 k).erase j) = (chart c).1 := by
    funext l
    by_cases hl : l = k
    · subst hl
      rw [Function.update_self, hIk]
      ext x
      simp only [chart, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact h2
        · exact absurd h2 h1
      · rintro rfl
        exact ⟨hxy, Or.inl rfl⟩
    · rw [Function.update_of_ne hl, hIl l hl]
      rfl
  change (∑ l : K, ∑ i ∈ I.1 l, _ :
    KH.CechC S ι M 0 →ₗ[MRingOver S ι] LocalizedModule (KH.cellMon S I.1) M) f = 0 at h
  rw [Finset.sum_eq_single k, Finset.sum_eq_add_of_mem (c k) j hx hy hxy, dite_eq_left (hface (c k) hx),
    dite_eq_left (hface j hy)] at h
  · rw [hsign, LinearMap.add_apply] at h
    change KH.faceSign I.1 k (c k) • (KH.cellRes S M _ I.1 (f _)) +
      (-KH.faceSign I.1 k (c k)) • (KH.cellRes S M _ I.1 (f _)) = 0 at h
    rw [key _ _ _ f₁, key _ _ _ f₂, neg_smul, ← sub_eq_add_neg] at h
    have h' := sub_eq_zero.mp h
    have hs2 : KH.faceSign I.1 k (c k) * KH.faceSign I.1 k (c k) = 1 := by
      unfold KH.faceSign
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have h'' := congrArg (fun x => KH.faceSign I.1 k (c k) • x) h'
    simp only [smul_smul, hs2, one_smul] at h''
    exact h''.symm
  · intro i hi _
    have : i = c k ∨ i = j := by rw [hIk] at hi; simpa using hi
    tauto
  · intro l _ hl
    refine Finset.sum_eq_zero fun i hi => dif_neg fun h' => ?_
    have := h'.1 l
    rw [Function.update_self, ← Finset.card_pos, Finset.card_erase_of_mem hi, hother l hl] at this
    omega
  · intro h'
    exact absurd (Finset.mem_univ k) h'

theorem cellRes_comp {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] {J P U : ∀ k, Finset (ι k)}
    (h₁ : ∀ k, J k ⊆ P k) (h₂ : ∀ k, P k ⊆ U k) (w : LocalizedModule (KH.cellMon S J) M) :
    KH.cellRes S M P U (KH.cellRes S M J P w) = KH.cellRes S M J U w := by
  induction w using LocalizedModule.induction_on with
  | h m t =>
    rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₁),
      GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono h₂),
      GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono fun k => (h₁ k).trans (h₂ k))]

theorem res_agree {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (z : KH.CechC S ι M 0)
    (hz : KH.cechD S ι M 0 z = 0) (c c' : ∀ k, ι k) (U : ∀ k, Finset (ι k)) (hc : ∀ k, c k ∈ U k)
    (hc' : ∀ k, c' k ∈ U k) :
    KH.cellRes S M (chart c).1 U (z (chart c)) = KH.cellRes S M (chart c').1 U (z (chart c')) := by
  classical
  suffices H : ∀ s : Finset K, ∀ c : ∀ k, ι k, (∀ k, c k ∈ U k) → (∀ l ∉ s, c l = c' l) →
      KH.cellRes S M (chart c).1 U (z (chart c)) = KH.cellRes S M (chart c').1 U (z (chart c')) from
    H Finset.univ c hc fun l hl => (hl (Finset.mem_univ l)).elim
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro c _ h
    have e : c = c' := funext fun l => h l (Finset.notMem_empty l)
    subst e
    rfl
  | insert k s _ ih =>
    intro c hcU h
    have hc₂U : ∀ l, Function.update c k (c' k) l ∈ U l := by
      intro l
      by_cases hl : l = k
      · subst hl
        rw [Function.update_self]
        exact hc' l
      · rw [Function.update_of_ne hl]
        exact hcU l
    have hrest : ∀ l ∉ s, Function.update c k (c' k) l = c' l := by
      intro l hl
      by_cases hlk : l = k
      · subst hlk
        rw [Function.update_self]
      · rw [Function.update_of_ne hlk]
        exact h l (by simp [hlk, hl])
    rw [← ih _ hc₂U hrest]
    by_cases hj : c' k = c k
    · have e : Function.update c k (c' k) = c := by rw [hj, Function.update_eq_self]
      rw [e]
    · have hPU : ∀ l, (pairCell c k (c' k) hj).1 l ⊆ U l := by
        intro l
        by_cases hl : l = k
        · subst hl
          simp only [pairCell, Function.update_self]
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact hcU _
          · exact hc' _
        · simp only [pairCell, Function.update_of_ne hl]
          intro x hx
          rw [Finset.mem_singleton.mp hx]
          exact hcU l
      have h₁ : ∀ l, (chart c).1 l ⊆ (pairCell c k (c' k) hj).1 l := by
        intro l
        by_cases hl : l = k
        · subst hl
          simp [chart, pairCell]
        · simp [chart, pairCell, Function.update_of_ne hl]
      have h₂ : ∀ l, (chart (Function.update c k (c' k))).1 l ⊆ (pairCell c k (c' k) hj).1 l := by
        intro l
        by_cases hl : l = k
        · subst hl
          simp [chart, pairCell]
        · simp [chart, pairCell, Function.update_of_ne hl]
      rw [← cellRes_comp h₁ hPU, ← cellRes_comp h₂ hPU, res_eq_of_pair c k (c' k) hj z hz]

end ChartNakayamaGen

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

def mdeg (μ : (Σ k, ι k) →₀ ℕ) : K → ℤ := fun k => ((∑ i, μ ⟨k, i⟩ : ℕ) : ℤ)

def comp (g : K → ℤ) (b : MRingOver S ι) : MRingOver S ι :=
  ∑ μ ∈ b.support.filter (fun μ => mdeg μ = g), monomial μ (AddMonoidAlgebra.coeff b μ)

theorem mdeg_of_mem_support_comp {g : K → ℤ} {b : MRingOver S ι} {μ : (Σ k, ι k) →₀ ℕ}
    (hμ : μ ∈ (comp g b).support) : mdeg μ = g := by
  unfold comp at hμ
  obtain ⟨ν, hν, hμν⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hμ)
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hμν)]
  exact (Finset.mem_filter.mp hν).2

theorem isMultiHomog_comp_mul {g : K → ℤ} {b w : MRingOver S ι} {ω a : K → ℕ} (hw : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog w ω)
    (h : ∀ k, g k + ω k = a k) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (comp g b * w) a := by
  intro m hm k
  obtain ⟨m₁, h₁, m₂, h₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  have e₁ := congrFun (mdeg_of_mem_support_comp h₁) k
  have e₂ := hw m₂ h₂ k
  have e₃ := h k
  simp only [mdeg] at e₁
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  omega

theorem isMultiHomog_comp {g : K → ℤ} {b : MRingOver S ι} {a : K → ℕ} (h : ∀ k, g k = a k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (comp g b) a := by
  have := isMultiHomog_comp_mul (b := b) (isMultiHomog_one_zero (S := S) (ι := ι)) (g := g) (a := a)
    fun k => by simp [h k]
  rwa [mul_one] at this

theorem sum_comp (b : MRingOver S ι) : ∑ g ∈ b.support.image mdeg, comp g b = b := by
  unfold comp
  rw [Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem mdeg hμ)]
  exact b.support_sum_monomial_coeff

theorem exists_comp_notMem {P : Ideal (MRingOver S ι)} {b : MRingOver S ι} (hb : b ∉ P) :
    ∃ δ : K → ℕ, comp (fun k => (δ k : ℤ)) b ∉ P := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hb
  rw [← sum_comp b]
  refine Ideal.sum_mem _ fun g hg => ?_
  obtain ⟨μ, -, rfl⟩ := Finset.mem_image.mp hg
  exact h (fun k => ∑ i, μ ⟨k, i⟩)

theorem comp_add_rest (g : K → ℤ) (b : MRingOver S ι) :
    comp g b + ∑ μ ∈ b.support.filter (fun μ => ¬ mdeg μ = g), monomial μ (AddMonoidAlgebra.coeff b μ) = b := by
  unfold comp
  rw [Finset.sum_filter_add_sum_filter_not]
  exact b.support_sum_monomial_coeff

section Graded

variable {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

theorem monomial_smul_mem (h𝓜 : KH.IsMGraded S ι 𝓜) {e : K → ℤ} {m : M} (hm : m ∈ 𝓜 e)
    (μ : (Σ k, ι k) →₀ ℕ) (r : S) : (monomial μ r : MRingOver S ι) • m ∈ 𝓜 (e + mdeg μ) :=
  h𝓜.2 (fun k => ∑ i, μ ⟨k, i⟩) e _ m (GenTwistGenerated.isMultiHomog_monomial μ r _ fun _ => rfl) hm

theorem comp_smul_mem (h𝓜 : KH.IsMGraded S ι 𝓜) {e g : K → ℤ} {m : M} (hm : m ∈ 𝓜 e)
    (b : MRingOver S ι) : comp g b • m ∈ 𝓜 (e + g) := by
  unfold comp
  rw [Finset.sum_smul]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have := monomial_smul_mem h𝓜 hm μ (AddMonoidAlgebra.coeff b μ)
  rwa [(Finset.mem_filter.mp hμ).2] at this

theorem smul_sub_comp_mem (h𝓜 : KH.IsMGraded S ι 𝓜) {e G : K → ℤ} {m : M} (hm : m ∈ 𝓜 e)
    (b : MRingOver S ι) : b • m - comp (G - e) b • m ∈ ⨆ (g) (_ : g ≠ G), 𝓜 g := by
  rw [← sub_smul, ← eq_sub_of_add_eq' (comp_add_rest (G - e) b), Finset.sum_smul]
  refine Submodule.sum_mem _ fun μ hμ => ?_
  have hne : e + mdeg μ ≠ G := fun h => (Finset.mem_filter.mp hμ).2 (eq_sub_of_add_eq' h)
  exact Submodule.mem_iSup_of_mem (e + mdeg μ)
    (Submodule.mem_iSup_of_mem hne (monomial_smul_mem h𝓜 hm μ _))

theorem comp_relation (h𝓜 : KH.IsMGraded S ι 𝓜) {E F G : K → ℤ} {n : ℕ} {q : MRingOver S ι} {m₀ : M}
    (hm₀ : m₀ ∈ 𝓜 E) {b : Fin n → MRingOver S ι} {m₁ : Fin n → M} (hm₁ : ∀ i, m₁ i ∈ 𝓜 F)
    (h : q • m₀ = ∑ i, b i • m₁ i) :
    comp (G - E) q • m₀ = ∑ i, comp (G - F) (b i) • m₁ i := by
  have hX : comp (G - E) q • m₀ - ∑ i, comp (G - F) (b i) • m₁ i ∈ 𝓜 G := by
    refine sub_mem ?_ (Submodule.sum_mem _ fun i _ => ?_)
    · have := comp_smul_mem h𝓜 hm₀ q (g := G - E)
      rwa [add_sub_cancel] at this
    · have := comp_smul_mem h𝓜 (hm₁ i) (b i) (g := G - F)
      rwa [add_sub_cancel] at this
  have hR : comp (G - E) q • m₀ - ∑ i, comp (G - F) (b i) • m₁ i ∈ ⨆ (g) (_ : g ≠ G), 𝓜 g := by
    have e : comp (G - E) q • m₀ - ∑ i, comp (G - F) (b i) • m₁ i =
        -((q • m₀ - comp (G - E) q • m₀) - ∑ i, (b i • m₁ i - comp (G - F) (b i) • m₁ i)) := by
      rw [Finset.sum_sub_distrib, ← h]
      abel
    rw [e]
    exact neg_mem (sub_mem (smul_sub_comp_mem h𝓜 hm₀ q)
      (Submodule.sum_mem _ fun i _ => smul_sub_comp_mem h𝓜 (hm₁ i) (b i)))
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep G) _ hX hR)

end Graded

theorem smul_mk_cancel {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    (w : MRingOver S ι) (y : M) (s : T) :
    (w * s) • LocalizedModule.mk y s = LocalizedModule.mk (w • y) 1 := by
  rw [LocalizedModule.smul'_mk, mul_comm, mul_smul, ← Submonoid.smul_def, LocalizedModule.mk_cancel]

theorem sum_mk_one {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    {n : ℕ} (y : Fin n → M) : ∑ i, LocalizedModule.mk (y i) (1 : T) = LocalizedModule.mk (∑ i, y i) 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← LocalizedModule.mkLinearMap_apply, map_sum]

theorem exists_smul_mem_span_of_mem_span {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M]
    [Module (MRingOver S ι) M] {Z : Set (LocalizedModule T M)} {w : LocalizedModule T M}
    (hw : w ∈ Submodule.span (Localization T) Z) :
    ∃ v ∈ T, v • w ∈ Submodule.span (MRingOver S ι) Z := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, T.one_mem, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, T.one_mem, by rw [smul_zero]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv, hvx⟩ := hx
    obtain ⟨v', hv', hvy⟩ := hy
    refine ⟨v * v', T.mul_mem hv hv', ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ hvx
    · rw [mul_smul]
      exact Submodule.smul_mem _ _ hvy
  | smul l x _ hx =>
    obtain ⟨v, hv, hvx⟩ := hx
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective T l
    refine ⟨s * v, T.mul_mem s.2 hv, ?_⟩
    have key : ((s : MRingOver S ι) * v) • (IsLocalization.mk' (Localization T) b s • x) = b • (v • x) := by
      rw [← algebraMap_smul (Localization T) ((s : MRingOver S ι) * v), ← algebraMap_smul (Localization T) b,
        ← algebraMap_smul (Localization T) v, smul_smul, smul_smul, map_mul, mul_right_comm,
        IsLocalization.mk'_spec']
    rw [key]
    exact Submodule.smul_mem _ b hvx

theorem chart_nakayama {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {P : Ideal (MRingOver S ι)} {d : K → ℤ}
    (hS : IsNoetherianRing S) (hM : Module.Finite (MRingOver S ι) M) (h𝓜 : KH.IsMGraded S ι 𝓜)
    (hP : P.IsPrime) (c : ∀ k, ι k) (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P)
    (hgen : ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z (chart c) ∈ locIdealPart 𝓜 (KH.cellMon S (chart c).1) P d) :
    ∃ (f₀ : MRingOver S ι) (δ₀ : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f₀ δ₀ ∧ f₀ ∉ P ∧
      ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ)
        (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
        t ∈ KH.cellMon S (chart c).1 ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a ∧ (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (p j) (a + δ₀)) ∧
        (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f₀ * t) • x = ∑ j, p j • z j (chart c) := by
  have := hS
  have := hM
  set T := KH.cellMon S (chart c).1 with hT
  have : IsNoetherianRing (Localization T) := IsLocalization.isNoetherianRing T _ inferInstance
  set Z : Set (LocalizedModule T M) := {w | ∃ z ∈ KH.cechZc ι 𝓜 d 0, w = z (chart c)} with hZ
  set N : Submodule (Localization T) (LocalizedModule T M) := Submodule.span _ Z with hN
  set 𝔮 : Ideal (Localization T) := P.map (algebraMap (MRingOver S ι) (Localization T)) with h𝔮
  have hdisj : ∀ v ∈ T, v ∉ P := fun v hv => cellMon_notMem hP hc hv

  have hideal : ∀ w ∈ locIdealPart 𝓜 T P d,
      w ∈ 𝔮 • (⊤ : Submodule (Localization T) (LocalizedModule T M)) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨p, a, y, hp, -, -, rfl⟩ := hw
      rw [← algebraMap_smul (Localization T) p y]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hp) Submodule.mem_top
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul s x _ hx =>
      have e : s • x = (algebraMap (MRingOver S ι) (Localization T) (C s : MRingOver S ι)) • x := by
        induction x using LocalizedModule.induction_on with
        | h m t =>
          rw [algebraMap_smul, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, ← MvPolynomial.algebraMap_eq,
            algebraMap_smul]
      rw [e]
      exact Submodule.smul_mem _ _ hx

  have hmk1 : ∀ m : M, LocalizedModule.mk m (1 : T) ∈ N ⊔ 𝔮 • ⊤ := by
    intro m
    have hm : m ∈ ⨆ e, 𝓜 e := by
      rw [h𝓜.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun m => LocalizedModule.mk m (1 : T) ∈ N ⊔ 𝔮 • ⊤) 𝓜 hm
      ?_ ?_ ?_
    · intro e m hm
      obtain ⟨gp, gn, hg⟩ : ∃ gp gn : K → ℕ, e + (fun k => (gn k : ℤ)) = d + fun k => (gp k : ℤ) :=
        ⟨fun k => (e k - d k).toNat, fun k => (-(e k - d k)).toNat, funext fun k => by
          simp only [Pi.add_apply]
          linarith [Int.toNat_sub_toNat_neg (e k - d k)]⟩
      have hx : LocalizedModule.mk (chartMon (S := S) c gn • m) (⟨chartMon (S := S) c gp, chartMon_mem c gp⟩ : T) ∈
          KH.locPart ι 𝓜 T d := by
        refine GenSESStep.mk_mem_locPart _ _ gp (isMultiHomog_chartMon c gp) ?_
        rw [← hg]
        exact h𝓜.2 _ _ _ _ (isMultiHomog_chartMon c gn) hm
      obtain ⟨z, hz, hxz⟩ := hgen _ hx
      have hx' : LocalizedModule.mk (chartMon (S := S) c gn • m) (⟨chartMon (S := S) c gp, chartMon_mem c gp⟩ : T) ∈
          N ⊔ 𝔮 • ⊤ := by
        rw [← sub_add_cancel (LocalizedModule.mk _ _) (z (chart c))]
        exact add_mem (Submodule.mem_sup_right (hideal _ hxz))
          (Submodule.mem_sup_left (Submodule.subset_span ⟨z, hz, rfl⟩))
      have e : LocalizedModule.mk m (1 : T) =
          Localization.mk (chartMon (S := S) c gp) (⟨chartMon (S := S) c gn, chartMon_mem c gn⟩ : T) •
            LocalizedModule.mk (chartMon (S := S) c gn • m) (⟨chartMon (S := S) c gp, chartMon_mem c gp⟩ : T) := by
        rw [LocalizedModule.mk_smul_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, mul_comm]
      rw [e]
      exact Submodule.smul_mem _ _ hx'
    · rw [LocalizedModule.zero_mk]
      exact zero_mem _
    · intro x y hx hy
      have e : LocalizedModule.mk (x + y) (1 : T) = LocalizedModule.mk x 1 + LocalizedModule.mk y 1 := by
        rw [LocalizedModule.mk_add_mk, one_smul, one_smul, mul_one]
      rw [e]
      exact add_mem hx hy
  have htop : (⊤ : Submodule (Localization T) (LocalizedModule T M)) ≤ N ⊔ 𝔮 • ⊤ := by
    intro w _
    induction w using LocalizedModule.induction_on with
    | h m s =>
      have e : LocalizedModule.mk m s =
          Localization.mk (1 : MRingOver S ι) s • LocalizedModule.mk m (1 : T) := by
        rw [LocalizedModule.mk_smul_mk, one_smul, mul_one]
      rw [e]
      exact Submodule.smul_mem _ _ (hmk1 m)

  obtain ⟨r, hr1, hrN⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup (I := 𝔮) (N := N)
    (N' := ⊤) (P := ⊤) Module.Finite.fg_top le_rfl htop
  obtain ⟨⟨q, s⟩, rfl⟩ := IsLocalization.mk'_surjective T r
  have hqs : q - (s : MRingOver S ι) ∈ P := by
    have h1 : algebraMap (MRingOver S ι) (Localization T) (q - s) ∈ 𝔮 := by
      have := 𝔮.mul_mem_left (algebraMap (MRingOver S ι) (Localization T) (s : MRingOver S ι)) hr1
      rwa [mul_sub, IsLocalization.mk'_spec', mul_one, ← map_sub] at this
    have hc' := IsLocalization.under_map_of_isPrime_disjoint T (Localization T) hP
      (Set.disjoint_left.mpr fun v hv hvP => hdisj v hv hvP)
    rw [← hc']
    exact h1
  have hq : q ∉ P := fun hq => hdisj s s.2 (by simpa using P.sub_mem hq hqs)
  obtain ⟨δ₀, hδ⟩ := exists_comp_notMem hq
  refine ⟨comp (fun k => (δ₀ k : ℤ)) q, δ₀, isMultiHomog_comp fun _ => rfl, hδ, fun x hx => ?_⟩

  have hrx : IsLocalization.mk' (Localization T) q s • x ∈ N :=
    hrN (Submodule.smul_mem_pointwise_smul x _ ⊤ Submodule.mem_top)
  obtain ⟨v, hv, hvx⟩ := exists_smul_mem_span_of_mem_span hrx
  have hqx : (v * q) • x ∈ Submodule.span (MRingOver S ι) Z := by
    have h := Submodule.smul_mem _ (s : MRingOver S ι) hvx
    have e : (s : MRingOver S ι) • v • IsLocalization.mk' (Localization T) q s • x = (v * q) • x := by
      rw [← algebraMap_smul (Localization T) (s : MRingOver S ι), ← algebraMap_smul (Localization T) v,
        ← algebraMap_smul (Localization T) (v * q), smul_smul, smul_smul, map_mul, mul_right_comm,
        IsLocalization.mk'_spec', mul_comm]
    rwa [e] at h
  obtain ⟨n, b, g, hsum⟩ := Submodule.mem_span_set'.mp hqx
  choose z hz hzg using fun i => (g i).2
  have hzI : ∀ i, z i (chart c) ∈ KH.locPart ι 𝓜 T d :=
    fun i => Submodule.mem_pi.mp (hz i).1 (chart c) (Set.mem_univ _)
  choose mi ti ai hti hmi hzeq using fun i => GenSESStep.locPart_normal h𝓜 (hzI i)
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx
  obtain ⟨γ, hγ⟩ := GenSESStep.cellMon_homog hv

  set u : MRingOver S ι := ∏ j, (ti j : MRingOver S ι) with hu
  have huT : u ∈ T := Submonoid.prod_mem _ fun j _ => (ti j).2
  have hu_homog : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog u (∑ j, ai j) := isMultiHomog_prod _ _ _ fun j _ => hti j
  have hui_homog : ∀ i, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι))
      (∑ j ∈ Finset.univ.erase i, ai j) := fun i => isMultiHomog_prod _ _ _ fun j _ => hti j
  have hper : ∀ i, u • LocalizedModule.mk (mi i) (ti i) =
      LocalizedModule.mk ((∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) • mi i) 1 := by
    intro i
    rw [hu, ← Finset.prod_erase_mul Finset.univ (fun j => (ti j : MRingOver S ι)) (Finset.mem_univ i),
      smul_mk_cancel]
  have h3 : LocalizedModule.mk ((u * (v * q)) • m) t =
      LocalizedModule.mk (∑ i, b i • (∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) • mi i) (1 : T) := by
    have h : u • (∑ i, b i • (g i : LocalizedModule T M)) = u • ((v * q) • LocalizedModule.mk m t) := by
      rw [hsum]
    rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk, smul_smul, Finset.smul_sum] at h
    rw [← h, ← sum_mk_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hzg i, hzeq i, smul_comm, hper i, LocalizedModule.smul'_mk]
  obtain ⟨v', hv'⟩ := LocalizedModule.mk_eq.mp h3
  simp only [one_smul, Submonoid.smul_def] at hv'
  obtain ⟨γ', hγ'⟩ := GenSESStep.cellMon_homog v'.2

  have hrel : q • (((v' : MRingOver S ι) * u * v) • m) =
      ∑ i, b i • (((v' : MRingOver S ι) * t * ∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) • mi i) := by
    have e₁ : q • (((v' : MRingOver S ι) * u * v) • m) = (v' : MRingOver S ι) • (u * (v * q)) • m := by
      simp only [smul_smul]
      congr 1
      ring
    rw [e₁, hv', Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_smul]
    congr 1
    ring
  have hm₀ : ((v' : MRingOver S ι) * u * v) • m ∈
      𝓜 ((d + fun k => (a k : ℤ)) + fun k => ((γ' + ∑ j, ai j + γ) k : ℤ)) :=
    h𝓜.2 _ _ _ _ (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul hγ' hu_homog) hγ) hm
  have hm₁ : ∀ i, ((v' : MRingOver S ι) * t * ∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) • mi i ∈
      𝓜 (d + fun k => ((γ' + a + ∑ j, ai j) k : ℤ)) := by
    intro i
    have h := h𝓜.2 _ _ _ _ (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul hγ' ht) (hui_homog i))
      (hmi i)
    have e : ((d + fun k => (ai i k : ℤ)) + fun k => ((γ' + a + ∑ j ∈ Finset.univ.erase i, ai j) k : ℤ)) =
        d + fun k => ((γ' + a + ∑ j, ai j) k : ℤ) := by
      funext k
      have := congrFun (Finset.sum_erase_add Finset.univ ai (Finset.mem_univ i)) k
      simp only [Pi.add_apply] at this ⊢
      push_cast
      omega
    rwa [e] at h
  have hcomp := comp_relation h𝓜
    (G := ((d + fun k => (a k : ℤ)) + fun k => ((γ' + ∑ j, ai j + γ) k : ℤ)) + fun k => (δ₀ k : ℤ))
    hm₀ hm₁ hrel
  rw [add_sub_cancel_left] at hcomp
  refine ⟨(v' : MRingOver S ι) * u * v * t, γ' + ∑ j, ai j + γ + a, n,
    fun i => comp ((((d + fun k => (a k : ℤ)) + fun k => ((γ' + ∑ j, ai j + γ) k : ℤ)) +
      fun k => (δ₀ k : ℤ)) - (d + fun k => ((γ' + a + ∑ j, ai j) k : ℤ))) (b i) *
        ((v' : MRingOver S ι) * t * (∏ j ∈ Finset.univ.erase i, (ti j : MRingOver S ι)) * ti i),
    z, T.mul_mem (T.mul_mem (T.mul_mem v'.2 huT) hv) t.2,
    GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul hγ' hu_homog) hγ) ht,
    fun i => ?_, fun i => hz i, ?_⟩
  · refine isMultiHomog_comp_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul
      (GenSESStep.isMultiHomog_mul hγ' ht) (hui_homog i)) (hti i)) fun k => ?_
    have := congrFun (Finset.sum_erase_add Finset.univ ai (Finset.mem_univ i)) k
    simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
    push_cast
    omega
  · rw [← mul_assoc, smul_mk_cancel, mul_smul, hcomp, ← sum_mk_one]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [hzeq i, ← mul_assoc, smul_mk_cancel]
    congr 1
    exact (mul_smul _ _ _).symm

end ChartNakayamaGen

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartNakayamaGen

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]

theorem homog_unique {p : MRingOver S ι} {a b : K → ℕ} (ha : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p a) (hb : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p b)
    (h0 : p ≠ 0) : a = b := by
  obtain ⟨μ, hμ⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp h0)
  funext k
  exact (ha μ hμ k).symm.trans (hb μ hμ k)

theorem chartMon_ne_zero [Nontrivial S] (c : ∀ k, ι k) (e : K → ℕ) : chartMon (S := S) c e ≠ 0 := by
  have h : chartMon (S := S) c e = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (e k)) 1 := by
    rw [MvPolynomial.monomial_sum_one, chartMon]
    exact Finset.prod_congr rfl fun k _ => MvPolynomial.X_pow_eq_monomial
  rw [h, Ne, MvPolynomial.monomial_eq_zero]
  exact one_ne_zero

theorem chartMon_one_pow (c : ∀ k, ι k) (n : ℕ) :
    chartMon (S := S) c (fun _ => 1) ^ n = chartMon c (fun _ => n) := by
  simp only [chartMon, pow_one, ← Finset.prod_pow]

theorem smul_mk_cancel' {T : Submonoid (MRingOver S ι)} {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M]
    (w : MRingOver S ι) (y : M) {s : MRingOver S ι} (hs : s ∈ T) :
    (w * s) • LocalizedModule.mk y (⟨s, hs⟩ : T) = LocalizedModule.mk (w • y) 1 :=
  smul_mk_cancel w y ⟨s, hs⟩

theorem exists_kill_of_res_eq_zero {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (c c' : ∀ k, ι k)
    (w : LocalizedModule (KH.cellMon S (chart c').1) M)
    (hw : KH.cellRes S M (chart c').1 (fun k => ({c k, c' k} : Finset (ι k))) w = 0) :
    ∃ e : ℕ, chartMon (S := S) c (fun _ => e) • w = 0 := by
  induction w using LocalizedModule.induction_on with
  | h m s =>
    have hsub : ∀ k, (chart c').1 k ⊆ ({c k, c' k} : Finset (ι k)) := fun k => by simp [chart]
    rw [GenTwistGenerated.cellRes_mk (GenTwistGenerated.cellMon_mono hsub)] at hw
    obtain ⟨v, hv⟩ := LocalizedModule.mk_eq.mp
      (hw.trans (LocalizedModule.zero_mk (1 : KH.cellMon S (fun k => ({c k, c' k} : Finset (ι k))))).symm)
    simp only [one_smul, smul_zero] at hv
    obtain ⟨e, w', hw'⟩ := dvd_of_mem_pair v.2
    have hz : (chartMon (S := S) c (fun _ => e) * chartMon c' (fun _ => e)) • m = 0 := by
      rw [hw', mul_comm, mul_smul, ← Submonoid.smul_def, hv, smul_zero]
    refine ⟨e, ?_⟩
    rw [LocalizedModule.smul'_mk, ← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
    refine ⟨⟨chartMon c' (fun _ => e), chartMon_mem c' _⟩, ?_⟩
    show chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • chartMon (S := S) c (fun _ => e) • m =
      chartMon (S := S) c' (fun _ => e) • (s : MRingOver S ι) • (0 : M)
    rw [smul_zero, smul_zero, smul_comm (chartMon c' (fun _ => e)) (s : MRingOver S ι),
      smul_smul (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)) m,
      mul_comm (chartMon c' (fun _ => e)) (chartMon c (fun _ => e)), hz, smul_zero]

theorem genNear_of_chart [Nontrivial S] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
    [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M} {d : K → ℤ} (h𝓜 : KH.IsMGraded S ι 𝓜)
    (c : ∀ k, ι k) {f₀ : MRingOver S ι} {δ₀ : K → ℕ} (hf₀ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f₀ δ₀)
    (hloc : ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d, ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ)
        (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
        t ∈ KH.cellMon S (chart c).1 ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t a ∧ (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (p j) (a + δ₀)) ∧
        (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ (f₀ * t) • x = ∑ j, p j • z j (chart c)) :
    GenNear S ι 𝓜 d (f₀ * chartMon c (fun _ => 1)) (δ₀ + fun _ => 1) := by
  intro J
  obtain ⟨c', rfl⟩ : ∃ c', J = chart c' := ⟨_, eq_chart J⟩
  intro x hx
  obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hx

  have hy : LocalizedModule.mk m (⟨chartMon c a, chartMon_mem c a⟩ : KH.cellMon S (chart c).1) ∈
      KH.locPart ι 𝓜 (KH.cellMon S (chart c).1) d :=
    GenSESStep.mk_mem_locPart _ _ a (isMultiHomog_chartMon c a) hm
  obtain ⟨t₁, a₁, r, p, z, ht₁T, ht₁, hp, hz, he⟩ := hloc _ hy
  obtain ⟨α₁, rfl⟩ := exists_chartMon ht₁T
  obtain rfl : a₁ = α₁ := homog_unique ht₁ (isMultiHomog_chartMon c α₁) (chartMon_ne_zero c α₁)

  set U : ∀ k, Finset (ι k) := fun k => {c k, c' k} with hU
  have hsub : ∀ k, (chart c).1 k ⊆ U k := fun k => by simp [chart, hU]
  have hsub' : ∀ k, (chart c').1 k ⊆ U k := fun k => by simp [chart, hU]
  have hle := GenTwistGenerated.cellMon_mono (S := S) hsub
  have hle' := GenTwistGenerated.cellMon_mono (S := S) hsub'
  have hagree : ∀ j, KH.cellRes S M (chart c').1 U (z j (chart c')) =
      KH.cellRes S M (chart c).1 U (z j (chart c)) := fun j =>
    (res_agree (z j) (LinearMap.mem_ker.mp (hz j).2) c c' U (fun k => by simp [hU])
      (fun k => by simp [hU])).symm
  have hD : KH.cellRes S M (chart c').1 U ((f₀ * chartMon c a₁ * (t : MRingOver S ι)) • LocalizedModule.mk m t -
      ∑ j, (chartMon c a * p j) • z j (chart c')) = 0 := by
    have h2 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
        LocalizedModule.mk ((f₀ * chartMon c a₁) • m) 1 := by
      have e1 : KH.cellRes S M (chart c').1 U (∑ j, (chartMon c a * p j) • z j (chart c')) =
          chartMon (S := S) c a • KH.cellRes S M (chart c).1 U (∑ j, p j • z j (chart c)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, hagree j, map_smul, mul_smul]
      rw [e1, ← he, map_smul, GenTwistGenerated.cellRes_mk hle, smul_smul,
        mul_comm (chartMon (S := S) c a) (f₀ * chartMon c a₁)]
      exact smul_mk_cancel' _ _ _
    rw [map_sub, h2, map_smul, GenTwistGenerated.cellRes_mk hle', sub_eq_zero]
    exact smul_mk_cancel' _ _ _
  obtain ⟨e, he0⟩ := exists_kill_of_res_eq_zero c c' _ hD
  rw [smul_sub, sub_eq_zero] at he0

  set E : ℕ := ∑ k, a₁ k with hE
  have haE : ∀ k, a₁ k ≤ E := fun k =>
    Finset.single_le_sum (f := a₁) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hexp : (fun _ : K => e + E + 1) = (fun _ => 1) + (fun k => E - a₁ k) + (fun _ => e) + a₁ := by
    funext k
    simp only [Pi.add_apply]
    have := haE k
    omega
  have hring : (f₀ * chartMon c (fun _ => 1)) ^ (e + E + 1) * (t : MRingOver S ι) =
      (f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k)) *
        (chartMon c (fun _ => e) * (f₀ * chartMon c a₁ * (t : MRingOver S ι))) := by
    rw [mul_pow, chartMon_one_pow, hexp, chartMon_add, chartMon_add, chartMon_add]
    ring
  refine ⟨e + E + 1, t, a, r, fun j => f₀ ^ (e + E) * chartMon c (fun _ => 1) * chartMon c (fun k => E - a₁ k) *
    chartMon c (fun _ => e) * chartMon c a * p j, z, t.2, ht, fun j => ?_, hz, ?_⟩
  · have h := GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul
      (GenSESStep.isMultiHomog_mul (GenSESStep.isMultiHomog_mul (isMultiHomog_pow hf₀ (e + E))
        (isMultiHomog_chartMon c (fun _ => 1))) (isMultiHomog_chartMon c (fun k => E - a₁ k)))
        (isMultiHomog_chartMon c (fun _ => e))) (isMultiHomog_chartMon c a)) (hp j)
    convert h using 1
    funext k
    simp only [Pi.add_apply, Pi.mul_apply, Pi.natCast_apply, Pi.one_apply, nsmul_eq_mul]
    have := haE k
    zify [this] at *
    ring
  · rw [hring, mul_smul, mul_smul (chartMon (S := S) c (fun _ => e)), he0, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    dsimp only
    simp only [smul_smul]
    congr 1
    ring

end ChartNakayamaGen

theorem ChartNakayamaGen.proof : ChartNakayamaGen.Statement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ 𝓜 P d hS hM h𝓜 hP _ I hI hgen
  obtain ⟨c, rfl⟩ : ∃ c, I = ChartNakayamaGen.chart c := ⟨_, ChartNakayamaGen.eq_chart I⟩
  have h1 : (1 : S) ≠ 0 := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by
    have e : (1 : MRingOver S ι) = 0 := by rw [← C_1, h, C_0]
    rw [e]
    exact P.zero_mem))
  have : Nontrivial S := nontrivial_of_ne 1 0 h1
  have hc : ∀ k, (X ⟨k, c k⟩ : MRingOver S ι) ∉ P := fun k => hI k (c k) (Finset.mem_singleton_self _)
  obtain ⟨f₀, δ₀, hf₀, hf₀P, hloc⟩ := ChartNakayamaGen.chart_nakayama hS hM h𝓜 hP c hc hgen
  refine ⟨f₀ * ChartNakayamaGen.chartMon c (fun _ => 1), δ₀ + fun _ => 1,
    GenSESStep.isMultiHomog_mul hf₀ (ChartNakayamaGen.isMultiHomog_chartMon c _), fun h => ?_,
    ChartNakayamaGen.genNear_of_chart h𝓜 c hf₀ hloc⟩
  rcases hP.mem_or_mem h with h | h
  · exact hf₀P h
  · exact ChartNakayamaGen.cellMon_notMem hP hc (ChartNakayamaGen.chartMon_mem c _) h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
