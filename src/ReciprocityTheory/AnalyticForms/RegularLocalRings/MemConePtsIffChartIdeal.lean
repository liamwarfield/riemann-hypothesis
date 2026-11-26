module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRat
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.AnChart
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
namespace ReciprocityTheory.AnForm.R

open MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def IsMultiHomogIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Prop :=
  ∃ S : Set (MvPolynomial (Σ k, ι k) ℂ), (∀ f ∈ S, ∃ a, IsMultiHomog f a) ∧ P = Ideal.span S

def IsRelevant (W : Ideal (MvPolynomial (Σ k, ι k) ℂ)) : Prop :=
  ∀ k, ∃ i, (X ⟨k, i⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ W

def chartIdeal (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    Ideal (MvPolynomial (Σ k, ι k) ℂ) :=
  P ⊔ Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ))

abbrev chartRing (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) : Type :=
  MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p

theorem eval_smul_of_isMultiHomog {f : MvPolynomial (Σ k, ι k) ℂ} {a : K → ℕ}
    (hf : IsMultiHomog f a) (c : K → ℂ) (y : (Σ k, ι k) → ℂ) :
    eval (fun q => c q.1 * y q) f = (∏ k, c k ^ a k) * eval y f := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hc : ∏ q : (Σ k, ι k), c q.1 ^ d q = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  have key : ∏ q, (c q.1 * y q) ^ d q = (∏ k, c k ^ a k) * ∏ q, y q ^ d q := by
    rw [← hc, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun q _ => mul_pow _ _ _)
  linear_combination (AddMonoidAlgebra.coeff f d) * key

theorem eval_eq_zero_of_smul {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (c : K → ℂ) (y : (Σ k, ι k) → ℂ) (hy : ∀ f ∈ P, eval y f = 0) :
    ∀ f ∈ P, eval (fun q => c q.1 * y q) f = 0 := by
  obtain ⟨S, hS, rfl⟩ := hP
  intro f hf
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, ha⟩ := hS g hg
    rw [eval_smul_of_isMultiHomog ha, hy g (Ideal.subset_span hg), mul_zero]
  | zero => simp
  | add g h _ _ hg hh => rw [map_add (f := _), hg, hh, add_zero]
  | smul a g _ hg => rw [smul_eq_mul, map_mul, hg, mul_zero]

theorem mem_conePts_iff_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    z ∈ conePts P ↔ ∀ h ∈ chartIdeal P p, eval (affCoord p z) h = 0 := by
  have haff : affCoord p z = fun q => (z ⟨q.1, p q.1⟩)⁻¹ * z q := by
    funext q
    show z q / z ⟨q.1, p q.1⟩ = _
    rw [div_eq_inv_mul]
  unfold conePts
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨-, hzP⟩
    have hle : chartIdeal P p ≤ RingHom.ker (eval (affCoord p z)) := by
      refine sup_le ?_ ?_
      · intro f hf
        rw [RingHom.mem_ker, haff]
        exact eval_eq_zero_of_smul hP (fun k => (z ⟨k, p k⟩)⁻¹) z hzP f hf
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, eval_X, map_one]
        show z ⟨k, p k⟩ / z ⟨k, p k⟩ - 1 = 0
        rw [div_self (hz k), sub_self]
    intro h hh
    exact hle hh
  · intro hch
    refine ⟨fun k => ⟨p k, hz k⟩, ?_⟩
    have hzeq : z = fun q => z ⟨q.1, p q.1⟩ * affCoord p z q := by
      funext q
      show z q = z ⟨q.1, p q.1⟩ * (z q / z ⟨q.1, p q.1⟩)
      have := hz q.1
      field_simp
    intro f hf
    rw [hzeq]
    exact eval_eq_zero_of_smul hP (fun k => z ⟨k, p k⟩) (affCoord p z)
      (fun g hg => hch g (Ideal.mem_sup_left hg)) f hf

theorem conePts_of_chartIdeal {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ) (hy : ∀ h ∈ chartIdeal P p, eval y h = 0) :
    y ∈ conePts P ∧ (∀ k, y ⟨k, p k⟩ = 1) ∧ affCoord p y = y := by
  have hle : Ideal.span (Set.range fun k => (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ)) ≤
      chartIdeal P p := le_sup_right
  have hleP : P ≤ chartIdeal P p := le_sup_left
  have h1 : ∀ k, y ⟨k, p k⟩ = 1 := by
    intro k
    have hmem : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p :=
      hle (Ideal.subset_span (Set.mem_range_self k))
    have := hy _ hmem
    rw [map_sub, eval_X, map_one, sub_eq_zero] at this
    exact this
  refine ⟨?_, h1, ?_⟩
  · unfold conePts
    rw [Set.mem_setOf_eq]
    exact ⟨fun k => ⟨p k, by rw [h1 k]; exact one_ne_zero⟩, fun f hf => hy f (hleP hf)⟩
  · funext q
    show y q / y ⟨q.1, p q.1⟩ = y q
    rw [h1 q.1, div_one]

theorem exists_chart (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ p : (k : K) → ι k, (∀ k, z ⟨k, p k⟩ ≠ 0) ∧ ∀ k i, ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, p k⟩‖ := by
  have hmax : ∀ k, ∃ i, ∀ j, ‖z ⟨k, j⟩‖ ≤ ‖z ⟨k, i⟩‖ := fun k => by
    obtain ⟨i0, _⟩ := hz k
    haveI : Nonempty (ι k) := ⟨i0⟩
    exact Finite.exists_max (fun j => ‖z ⟨k, j⟩‖)
  choose p hp using hmax
  refine ⟨p, fun k => ?_, fun k i => hp k i⟩
  obtain ⟨i0, hi0⟩ := hz k
  have h1 : 0 < ‖z ⟨k, i0⟩‖ := norm_pos_iff.mpr hi0
  have h2 := hp k i0
  intro h
  rw [h, norm_zero] at h2
  linarith

theorem affCoord_eq_of_sameOrbit (p : (k : K) → ι k) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  show c q.1 * z' q / (c q.1 * z' ⟨q.1, p q.1⟩) = z' q / z' ⟨q.1, p q.1⟩
  exact mul_div_mul_left (z' q) (z' ⟨q.1, p q.1⟩) (hc q.1)

theorem sameOrbit_affCoord (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    SameOrbit z (affCoord p z) := by
  refine ⟨fun k => z ⟨k, p k⟩, hz, ?_⟩
  funext q
  show z q = z ⟨q.1, p q.1⟩ * (z q / z ⟨q.1, p q.1⟩)
  have := hz q.1
  field_simp

end

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas
section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.AtlasA
namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

theorem analyticAt_eval_of_pi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {σ : Type*}
    {f : E → σ → ℂ} {z : E} (hf : ∀ l, AnalyticAt ℂ (f · l) z) (p : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun x => eval (f x) p) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact analyticAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p l hp =>
    simp only [map_mul, eval_X]
    exact hp.mul (hf l)

def AlgRes.GoodChart (R : AlgRes (ι := ι) P D e) (ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)) : Prop :=
  ∃ i, ψ.source ⊆ R.src i ∧
    (∃ r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ, ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y)) ∧
    ∃ g : (Fin e → ℂ) → Fin (R.amb i) → ℂ, AnalyticOnNhd ℂ g ψ.target ∧
      ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w

theorem AlgRes.analyticAt_coord_symm (R : AlgRes (ι := ι) P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} {i : Fin R.n} (hs : ψ.source ⊆ R.src i)
    {g : (Fin e → ℂ) → Fin (R.amb i) → ℂ} (hg : AnalyticOnNhd ℂ g ψ.target)
    (hgc : ∀ w ∈ ψ.target, R.coord i (ψ.symm w) = g w)
    (j : Fin R.n) (h : MvPolynomial (Fin (R.amb j)) ℂ) {w : Fin e → ℂ} (hw : w ∈ ψ.target)
    (hwj : ψ.symm w ∈ R.src j) :
    AnalyticAt ℂ (fun w => eval (R.coord j (ψ.symm w)) h) w := by
  have hwS : ψ.symm w ∈ ψ.source := ψ.map_target hw
  have hxi : ψ.symm w ∈ R.src i := hs hwS
  obtain ⟨q, F, hq0, hqF⟩ := R.trans i j (ψ.symm w) ⟨hxi, hwj⟩
  have hgw : AnalyticAt ℂ g w := hg w hw
  have hga : ∀ l, AnalyticAt ℂ (g · l) w := fun l =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (R.amb i) => ℂ) l).analyticAt (g w)).comp hgw
  have hFa : ∀ l, AnalyticAt ℂ (fun w' => eval (g w') (F l)) w := fun l =>
    analyticAt_eval_of_pi hga (F l)
  have hqa : AnalyticAt ℂ (fun w' => eval (g w') q) w := analyticAt_eval_of_pi hga q
  have hq0' : eval (g w) q ≠ 0 := by
    rw [← hgc w hw]
    exact hq0
  have hA : AnalyticAt ℂ (fun w' => eval (fun l => eval (g w') (F l) / eval (g w') q) h) w :=
    analyticAt_eval_of_pi (f := fun w' l => eval (g w') (F l) / eval (g w') q)
      (fun l => (hFa l).div hqa hq0') h
  refine hA.congr ?_
  have ht : ψ.target ∈ 𝓝 w := ψ.open_target.mem_nhds hw
  have hj : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ R.src j :=
    (ψ.continuousAt_symm hw).preimage_mem_nhds ((R.isOpen_alt_bis j).mem_nhds hwj)
  have hqne : ∀ᶠ w' in 𝓝 w, eval (g w') q ≠ 0 := hqa.continuousAt.eventually_ne hq0'
  filter_upwards [ht, hj, hqne] with w' h1 h2 h3
  have hsrc : ψ.symm w' ∈ R.src i := hs (ψ.map_target h1)
  have hcw : R.coord i (ψ.symm w') = g w' := hgc w' h1
  have hfun : (fun l => eval (g w') (F l) / eval (g w') q) = R.coord j (ψ.symm w') := by
    funext l
    have hl := hqF (ψ.symm w') ⟨hsrc, h2⟩ (by rw [hcw]; exact h3) l
    rw [hcw] at hl
    rw [div_eq_iff h3]
    exact hl.symm
  exact congrArg (fun v => eval v h) hfun

theorem AlgRes.analyticOnNhd_comp_symm (R : AlgRes (ι := ι) P D e)
    {ψ : OpenPartialHomeomorph R.M (Fin e → ℂ)} (hψ : R.GoodChart ψ) {m : ℕ}
    (f : R.M → Fin m → ℂ) (S : Set R.M) (hS : IsOpen S) (j : Fin R.n) (hSj : S ⊆ R.src j)
    (r : Fin m → MvPolynomial (Fin (R.amb j)) ℂ) (hf : ∀ y ∈ S, f y = evalFam r (R.coord j y)) :
    AnalyticOnNhd ℂ (f ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' S) := by
  obtain ⟨i, hsi, -, g, hg, hgc⟩ := hψ
  rintro w ⟨hw, hwS⟩
  have hwS' : ψ.symm w ∈ S := hwS
  have hev : (fun w' => evalFam r (R.coord j (ψ.symm w'))) =ᶠ[𝓝 w] (f ∘ ψ.symm) := by
    have hS' : ∀ᶠ w' in 𝓝 w, ψ.symm w' ∈ S :=
      (ψ.continuousAt_symm hw).preimage_mem_nhds (hS.mem_nhds hwS')
    filter_upwards [hS'] with w' h1
    exact (hf _ h1).symm
  refine AnalyticAt.congr ?_ hev
  rw [analyticAt_pi_iff]
  intro l
  exact R.analyticAt_coord_symm hsi hg hgc j (r l) hw (hSj hwS')

theorem AlgRes.exists_goodChart (R : AlgRes (ι := ι) P D e) (i : Fin R.n) (x : R.M) (hx : x ∈ R.src i)
    (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ)
    (hr : Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
      Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)))
    (O : Set R.M) (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), R.GoodChart ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y) := by
  have := R.regular i x hx
  obtain ⟨U, V, g, hU, hpU, hV, hg, hbij, hrg⟩ :=
    exists_holo_coords (R.ideal i) (R.coord i x) e (R.dim i x hx) r hr
  have hcont : ContinuousOn (R.coord i) (R.src i) := by
    rw [continuousOn_iff_continuous_domRestrict]; exact (R.isEmbedding i).continuous
  have hinj : Set.InjOn (R.coord i) (R.src i) := fun a ha b hb hab =>
    congrArg Subtype.val ((R.isEmbedding i).injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) hab)
  have hev : Continuous (evalFam r) := continuous_pi fun l => MvPolynomial.continuous_eval (p := r l)
  have hzero : ∀ y ∈ R.src i, R.coord i y ∈ zeroSet (R.ideal i) := by
    intro y hy
    have : R.coord i y ∈ R.coord i '' R.src i := ⟨y, hy, rfl⟩
    rw [R.image i] at this
    exact this
  have hex : ∀ w ∈ V, ∃ y ∈ R.src i, R.coord i y = g w := by
    intro w hw
    have h1 : g w ∈ zeroSet (R.ideal i) := (hbij.mapsTo hw).2
    have hmem : g w ∈ R.coord i '' R.src i := by rw [R.image i]; exact h1
    obtain ⟨y, hy, hyw⟩ := hmem
    exact ⟨y, hy, hyw⟩
  classical
  let inv : (Fin e → ℂ) → R.M := fun w =>
    if h : ∃ y ∈ R.src i, R.coord i y = g w then h.choose else x
  have hinv : ∀ w ∈ V, inv w ∈ R.src i ∧ R.coord i (inv w) = g w := by
    intro w hw
    have h := hex w hw
    simp only [inv, dif_pos h]
    exact h.choose_spec
  have hback : ∀ y ∈ R.src i, R.coord i y ∈ U → g (evalFam r (R.coord i y)) = R.coord i y := by
    intro y hy hyU
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hyU, hzero y hy⟩
    rw [← hgw, hrg w hw]
  let S : Set R.M := R.src i ∩ R.coord i ⁻¹' (U ∩ evalFam r ⁻¹' V)
  have hSo : IsOpen S := hcont.isOpen_inter_preimage (R.isOpen_alt_bis i) (hU.inter (hV.preimage hev))
  have hmapT : ∀ w ∈ V, inv w ∈ S := by
    intro w hw
    obtain ⟨h1, h2⟩ := hinv w hw
    refine ⟨h1, ?_⟩
    show R.coord i (inv w) ∈ U ∩ evalFam r ⁻¹' V
    rw [h2]
    refine ⟨(hbij.mapsTo hw).1, ?_⟩
    show evalFam r (g w) ∈ V
    rw [hrg w hw]
    exact hw
  have hcinv : ContinuousOn inv V := by
    rw [continuousOn_iff_continuous_domRestrict]
    let f : V → R.src i := fun w => ⟨inv w, (hinv w w.2).1⟩
    have hf : Continuous f := by
      rw [(R.isEmbedding i).continuous_iff]
      have : ((fun y : R.src i => R.coord i y) ∘ f) = fun w : V => g w :=
        funext fun w => (hinv w w.2).2
      rw [this]
      exact hg.continuousOn.domRestrict
    exact continuous_subtype_val.comp hf
  let ψ0 : OpenPartialHomeomorph R.M (Fin e → ℂ) :=
    { toFun := fun y => evalFam r (R.coord i y)
      invFun := inv
      source := S
      target := V
      map_source' := fun y hy => hy.2.2
      map_target' := fun w hw => hmapT w hw
      left_inv' := fun y hy => by
        obtain ⟨h1, h2⟩ := hinv _ hy.2.2
        exact hinj h1 hy.1 (h2.trans (hback y hy.1 hy.2.1))
      right_inv' := fun w hw => by
        obtain ⟨-, h2⟩ := hinv w hw
        show evalFam r (R.coord i (inv w)) = w
        rw [h2, hrg w hw]
      open_source := hSo
      open_target := hV
      continuousOn_toFun := (hev.comp_continuousOn hcont).mono fun y hy => hy.1
      continuousOn_invFun := hcinv }
  have hxS : x ∈ S := by
    obtain ⟨w, hw, hgw⟩ := hbij.surjOn ⟨hpU, hzero x hx⟩
    refine ⟨hx, hpU, ?_⟩
    show evalFam r (R.coord i x) ∈ V
    rw [← hgw, hrg w hw]
    exact hw
  refine ⟨ψ0.restrOpen O hO, ⟨i, fun y hy => hy.1.1, ⟨r, fun y _ => rfl⟩, g,
    hg.mono fun w hw => hw.1, fun w hw => (hinv w hw.1).2⟩, ⟨hxS, hxO⟩,
    fun y hy => ⟨hy.2, hy.1.1⟩, fun y _ => rfl⟩

end ReciprocityTheory.AnForm.R
end

namespace ReciprocityTheory.AnForm.R

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def AlgRes.IsGoodAtlas {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : AlgRes ι P D e)
    (A : FinHolAtlas e R.M) : Prop :=
      (∀ i (h : MvPolynomial (Fin (R.amb i)) ℂ),
        A.HoloOn (R.src i) fun x => eval (R.coord i x) h) ∧
      ∀ i, ∀ x ∈ R.src i, ∀ (r : Fin e → MvPolynomial (Fin (R.amb i)) ℂ),
        Ideal.span (Set.range fun l => algebraMap _ (locRing (R.ideal i) (R.coord i x)) (r l)) =
          Ideal.map (algebraMap _ (locRing (R.ideal i) (R.coord i x))) (ptIdeal (R.coord i x)) →
        ∀ O : Set R.M, IsOpen O → x ∈ O →
          ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
            ψ.source ⊆ O ∩ R.src i ∧ ∀ y ∈ ψ.source, ψ y = evalFam r (R.coord i y)

theorem AlgRes.exists_atlas {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ} (R : AlgRes ι P D e) :
    ∃ A : FinHolAtlas e R.M, R.IsGoodAtlas A := by
  have hloc : ∀ x : R.M, ∃ ψ : OpenPartialHomeomorph R.M (Fin e → ℂ),
      R.GoodChart ψ ∧ x ∈ ψ.source := by
    intro x
    obtain ⟨i, hx⟩ := R.cover x
    obtain ⟨ψ, hψ, hxψ, -⟩ := R.exists_goodChart i x hx (R.sncAt i x hx).r
      (R.sncAt i x hx).span_eq Set.univ isOpen_univ trivial
    exact ⟨ψ, hψ, hxψ⟩
  choose ψ hψ hxψ using hloc
  obtain ⟨t, -, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set R.M)).elim_nhds_subcover
    (fun x => (ψ x).source) (fun x _ => (ψ x).open_source.mem_nhds (hxψ x))
  let A : FinHolAtlas e R.M :=
    { n := t.card
      chart := fun j => ψ (t.equivFin.symm j).1
      cover := fun x => by
        obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
        exact ⟨t.equivFin ⟨z, hz⟩, by simpa using hxz⟩
      holo := fun j k => by
        obtain ⟨ik, hsk, ⟨rk, hrk⟩, -⟩ := hψ (t.equivFin.symm k).1
        exact R.analyticOnNhd_comp_symm (hψ _) _ _ (ψ (t.equivFin.symm k).1).open_source ik hsk
          rk hrk }
  have hgood : ∀ j, R.GoodChart (A.chart j) := fun j => hψ _
  refine ⟨A, fun i h j => ?_, fun i x hx r hr O hO hxO => ?_⟩
  · obtain ⟨i', hs, -, g, hg, hgc⟩ := hgood j
    rintro w ⟨hw, hwi⟩
    exact R.analyticAt_coord_symm hs hg hgc i h hw hwi
  · obtain ⟨φ, hφ, hxφ, hsub, hform⟩ := R.exists_goodChart i x hx r hr O hO hxO
    refine ⟨φ, fun j => ⟨?_, ?_⟩, hxφ, hsub, hform⟩
    · exact R.analyticOnNhd_comp_symm (hgood j) φ φ.source φ.open_source i
        (fun y hy => (hsub hy).2) r hform
    · obtain ⟨ij, hsj, ⟨rj, hrj⟩, -⟩ := hgood j
      exact R.analyticOnNhd_comp_symm hφ _ _ (A.chart j).open_source ij hsj rj hrj

end ReciprocityTheory.AnForm.R
end

section -- merged from ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjectiveLineMultihomogClassify
namespace ReciprocityTheory.AnForm.R

open MvPolynomial OnePoint Filter Topology

noncomputable section

theorem ptIdeal_isMaximal {n : ℕ} (p : Fin n → ℂ) : (ptIdeal p).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩

theorem sub_C_eval_mem_span {n : ℕ} (p : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    f - C (eval p f) ∈ Ideal.span (Set.range fun i => X i - C (p i)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add f g hf hg =>
    have : f + g - C (eval p (f + g)) = (f - C (eval p f)) + (g - C (eval p g)) := by
      simp only [map_add (f := _)]; ring
    rw [this]; exact add_mem hf hg
  | mul_X f i hf =>
    have : f * X i - C (eval p (f * X i)) =
        (f - C (eval p f)) * X i + C (eval p f) * (X i - C (p i)) := by
      simp only [map_mul, eval_X]; ring
    rw [this]
    exact add_mem (Ideal.mul_mem_right _ _ hf) (Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

theorem ptIdeal_eq_span {n : ℕ} (p : Fin n → ℂ) :
    ptIdeal p = Ideal.span (Set.range fun i => X i - C (p i)) := by
  apply le_antisymm
  · intro f hf
    have h0 : eval p f = 0 := hf
    simpa [h0] using sub_C_eval_mem_span p f
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    show eval p (X i - C (p i)) = 0
    simp

end

end ReciprocityTheory.AnForm.R
end
