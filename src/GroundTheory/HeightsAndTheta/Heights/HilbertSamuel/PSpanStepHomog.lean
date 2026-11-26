module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepHomog

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact MulMemClass.mul_mem (hs c hc) (ht c hc)

theorem pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {v : Ω} (hv : v ∈ chartLat y a 1) (e : ℕ) :
    v ^ e ∈ chartLat y a e := by
  induction e with
  | zero => intro c _; simp
  | succ e ih => rw [pow_succ]; exact mul_mem ih hv

abbrev forms {q : ℕ} (w : Fin q → Ω) (e : ℕ) : AddSubgroup Ω :=
  gradedSpan w (fun _ : Fin 1 => 0) (fun _ => 1) e

theorem mul_forms_mem {q r : ℕ} {w : Fin q → Ω} {d : Fin r → ℕ} {t : Fin r → Ω} {N e : ℕ} {x f : Ω}
    (hx : x ∈ gradedSpan w d t N) (hf : f ∈ forms w e) : x * f ∈ gradedSpan w d t (N + e) := by
  have hmono : ∀ μ : Fin q → ℕ, x * ∏ i, w i ^ μ i ∈ gradedSpan w d t (N + ∑ i, μ i) := by
    intro μ
    induction hx using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨l, ν, hν, rfl⟩ := hz
      have h := gradedSpan_gen_mem w d t l (ν + μ)
      have hdeg : d l + ∑ i, (ν + μ) i = N + ∑ i, μ i := by
        rw [← hν]; simp [Finset.sum_add_distrib, add_assoc]
      have hval : t l * ∏ i, w i ^ (ν + μ) i = t l * (∏ i, w i ^ ν i) * ∏ i, w i ^ μ i := by
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]; ring
      rwa [hdeg, hval] at h
    | zero => rw [zero_mul]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [add_mul]; exact add_mem hz hz'
    | neg z _ hz => rw [neg_mul]; exact neg_mem hz
  induction hf using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨l, μ, hμ, rfl⟩ := hz
    have h := hmono μ
    rwa [one_mul, ← hμ, zero_add]
  | zero => rw [mul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [mul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [mul_neg]; exact neg_mem hz

theorem one_mem_forms {q : ℕ} (w : Fin q → Ω) : (1 : Ω) ∈ forms w 0 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => (1 : Ω)) 0 (fun _ => 0)
  simpa using h

theorem mem_forms_one {q : ℕ} (w : Fin q → Ω) (i : Fin q) : w i ∈ forms w 1 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => (1 : Ω)) 0 (Pi.single i 1)
  simpa [Pi.single_apply, pow_ite, Finset.prod_ite_eq'] using h

theorem pow_mem_forms {q : ℕ} (w : Fin q → Ω) (i : Fin q) (e : ℕ) : w i ^ e ∈ forms w e := by
  induction e with
  | zero => simpa using one_mem_forms w
  | succ e ih => rw [pow_succ]; exact mul_forms_mem ih (mem_forms_one w i)

theorem exists_mul_pow_mem_forms {q : ℕ} {w : Fin q → Ω} {j : Fin q} (hj : w j ≠ 0) {c : Ω}
    (hc : c ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) : ∃ E : ℕ, c * w j ^ E ∈ forms w E := by
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨1, ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hj]
    exact mem_forms_one w i
  | algebraMap r =>
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, algebraMap_int_eq, eq_intCast, ← zsmul_one]
    exact zsmul_mem (one_mem_forms w) r
  | add x x' _ _ hx hx' =>
    obtain ⟨E, hE⟩ := hx
    obtain ⟨E', hE'⟩ := hx'
    refine ⟨E + E', ?_⟩
    have h1 := mul_forms_mem hE (pow_mem_forms w j E')
    have h2 := mul_forms_mem hE' (pow_mem_forms w j E)
    rw [add_comm E' E] at h2
    rw [show (x + x') * w j ^ (E + E') = x * w j ^ E * w j ^ E' + x' * w j ^ E' * w j ^ E by ring]
    exact add_mem h1 h2
  | mul x x' _ _ hx hx' =>
    obtain ⟨E, hE⟩ := hx
    obtain ⟨E', hE'⟩ := hx'
    refine ⟨E + E', ?_⟩
    rw [show x * x' * w j ^ (E + E') = x * w j ^ E * (x' * w j ^ E') by ring]
    exact mul_forms_mem hE hE'

theorem mul_pow_mem_forms_of_le {q : ℕ} {w : Fin q → Ω} {j : Fin q} {c : Ω} {E E' : ℕ}
    (h : c * w j ^ E ∈ forms w E) (hle : E ≤ E') : c * w j ^ E' ∈ forms w E' := by
  have h' := mul_forms_mem h (pow_mem_forms w j (E' - E))
  rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' hle] at h'

end SpanStepHomog


open SpanStepHomog in
theorem SpanStepHomog.proof (hL : SpanStepLocal.Statement) : SpanStepHomog.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  have H : ∀ j, ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, ∃ n : ℕ, b l * w j ^ n ∈ chartLat y a n) ∧
      (w j ≠ 0 → ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n →
        ∃ c : Fin r → Ω, (∀ l, c l ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) ∧
          g = ∑ l, c l * b l) := by
    intro j
    by_cases hj : w j = 0
    · exact ⟨0, Fin.elim0, fun l => l.elim0, fun h => (h hj).elim⟩
    · obtain ⟨r, b, h1, h2⟩ := hL K ι Ω y a q w hy hw hgen j hj
      exact ⟨r, b, h1, fun _ => h2⟩
  choose r b hb hspan using H
  choose nb hnb using hb
  set m := ∑ j, ∑ l, nb j l with hm
  have hle : ∀ j l, nb j l ≤ m := fun j l =>
    (Finset.single_le_sum (f := nb j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun j => ∑ l, nb j l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  let e := Fintype.equivFin (Σ j, Fin (r j))
  let T : (Σ j, Fin (r j)) → Ω := fun p => b p.1 p.2 * w p.1 ^ m
  let t : Fin (Fintype.card (Σ j, Fin (r j))) → Ω := fun i => T (e.symm i)
  have htv : ∀ j l, t (e ⟨j, l⟩) = b j l * w j ^ m := fun j l => by
    show T (e.symm (e ⟨j, l⟩)) = _
    rw [Equiv.symm_apply_apply]
  refine ⟨m, _, t, fun i => ?_, fun n s hs j hj => ?_⟩
  · have h := mul_mem (hnb (e.symm i).1 (e.symm i).2) (pow_mem (hw (e.symm i).1) (m - nb (e.symm i).1 (e.symm i).2))
    rwa [mul_assoc, ← pow_add, Nat.add_sub_cancel' (hle _ _)] at h
  have hwn : w j ^ n ≠ 0 := pow_ne_zero n hj
  obtain ⟨c, hc, hg⟩ := hspan j hj (s / w j ^ n) n (by rwa [div_mul_cancel₀ _ hwn])
  choose E hE using fun l => exists_mul_pow_mem_forms hj (hc l)
  refine ⟨m + ∑ l, E l, ?_⟩
  have hs' : s * w j ^ (m + ∑ l, E l) =
      ∑ l, t (e ⟨j, l⟩) * (c l * w j ^ (∑ l, E l)) * w j ^ n := by
    rw [show s = s / w j ^ n * w j ^ n by rw [div_mul_cancel₀ _ hwn], hg, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [htv, pow_add]; ring
  rw [hs', show n + (m + ∑ l, E l) = m + ∑ l, E l + n by ring]
  refine sum_mem fun l _ => mul_forms_mem (mul_forms_mem ?_ (mul_pow_mem_forms_of_le (hE l)
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)))) (pow_mem_forms w j n)
  have h := gradedSpan_gen_mem w (fun _ => m) t (e ⟨j, l⟩) (fun _ => 0)
  simpa using h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsSeparated
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionsSeparated

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (support_mul f g hm)
  simp [Finset.sum_add_distrib, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mem_mCoordIdeal_of_homog (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero,
    zero_mul]

def IsRepAt (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) (s : Ω) (z : (Σ k, ι k) → ℂ) (g h : MRing ι) : Prop :=
  ∃ dg dh : K → ℕ, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g dg ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧
    aeval y g = s * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0

theorem rep_cross {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {g h g' h' : MRing ι} (hr : IsRepAt y a τ s z g h)
    (hr' : IsRepAt y a τ s z g' h') :
    eval z (map (Int.castRingHom ℂ) g) * eval z (map (Int.castRingHom ℂ) h') =
      eval z (map (Int.castRingHom ℂ) g') * eval z (map (Int.castRingHom ℂ) h) := by
  obtain ⟨dg, dh, hg, hh, hd, hy, -⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy', -⟩ := hr'
  have hdeg : dg + dh' = dg' + dh := by
    funext k
    have : ((dg k + dh' k : ℕ) : ℤ) = ((dg' k + dh k : ℕ) : ℤ) := by
      push_cast
      linarith [hd k, hd' k]
    simp only [Pi.add_apply]
    exact_mod_cast this
  have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g * h' - g' * h) (dg + dh') := by
    refine isMultiHomog_sub (isMultiHomog_mul hg hh') ?_
    rw [hdeg]
    exact isMultiHomog_mul hg' hh
  have h0 : aeval y (g * h' - g' * h) = 0 := by
    rw [map_sub, map_mul, map_mul, hy, hy']
    ring
  have := hz.2 _ (mem_mCoordIdeal_of_homog y hF h0)
  simp only [map_sub, map_mul] at this
  exact sub_eq_zero.mp this

theorem rep_add {y : (Σ k, ι k) → Ω} {a : K → ℤ} {τ : ℕ} {s t : Ω} {z : (Σ k, ι k) → ℂ} {g h g' h' : MRing ι}
    (hr : IsRepAt y a τ s z g h) (hr' : IsRepAt y a τ t z g' h') :
    IsRepAt y a τ (s + t) z (g * h' + g' * h) (h * h') := by
  obtain ⟨dg, dh, hg, hh, hd, hy, hz0⟩ := hr
  obtain ⟨dg', dh', hg', hh', hd', hy', hz0'⟩ := hr'
  have hdeg : dg' + dh = dg + dh' := by
    funext k
    have : ((dg' k + dh k : ℕ) : ℤ) = ((dg k + dh' k : ℕ) : ℤ) := by
      push_cast
      linarith [hd k, hd' k]
    simp only [Pi.add_apply]
    exact_mod_cast this
  refine ⟨dg + dh', dh + dh', isMultiHomog_add (isMultiHomog_mul hg hh') ?_, isMultiHomog_mul hh hh', ?_, ?_, ?_⟩
  · rw [← hdeg]
    exact isMultiHomog_mul hg' hh
  · intro k
    simp only [Pi.add_apply]
    push_cast
    linarith [hd k]
  · rw [map_add (f := _), map_mul, map_mul, map_mul, hy, hy']
    ring
  · simp only [map_mul]
    exact mul_ne_zero hz0 hz0'

end SmallSectionsSeparated


open SmallSectionsSeparated in
theorem SmallSectionsSeparated.proof (hG : GridSeparation.Statement) : SmallSectionsSeparated.Statement := by
  intro K _ ι _ Ω _ y D A hV hB hA
  obtain ⟨C, hC, hZ⟩ := hG K ι Ω y D A hV hB hA
  refine ⟨C, hC, fun τ => ?_⟩
  obtain ⟨Z, hZP, hrep, hsep⟩ := hZ τ
  classical
  have hR : ∀ (s : chartLatNm y A.a τ) (z : Z), ∃ gh : MRing ι × MRing ι,
      IsRepAt y A.a τ (s : Ω) (z : (Σ k, ι k) → ℂ) gh.1 gh.2 := by
    intro s z
    obtain ⟨dg, dh, g, h, hg, hh, hd, hy, hz⟩ := hrep s s.2 z z.2
    exact ⟨(g, h), dg, dh, hg, hh, hd, hy, hz⟩
  choose gh hgh using hR
  let val : chartLatNm y A.a τ → Z → ℂ := fun s z =>
    eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) (gh s z).1) /
      eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) (gh s z).2)

  have hval : ∀ (s : chartLatNm y A.a τ) (z : Z) (g h : MRing ι),
      IsRepAt y A.a τ (s : Ω) (z : (Σ k, ι k) → ℂ) g h →
      val s z = eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g) /
        eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) := by
    intro s z g h hr
    have h1 := (hgh s z).choose_spec.choose_spec.2.2.2.2
    have h2 := hr.choose_spec.choose_spec.2.2.2.2
    rw [div_eq_div_iff h1 h2]
    exact rep_cross (hZP z z.2) (hgh s z) hr
  let ev : chartLatNm y A.a τ →+ (Z → ℂ) := AddMonoidHom.mk' (fun s z => val s z) (by
    intro s t
    funext z
    have hst := rep_add (hgh s z) (hgh t z)
    rw [Pi.add_apply, hval (s + t) z _ _ (by simpa using hst)]
    have h1 := (hgh s z).choose_spec.choose_spec.2.2.2.2
    have h2 := (hgh t z).choose_spec.choose_spec.2.2.2.2
    simp only [val, map_add (f := _), map_mul]
    field_simp)
  refine ⟨Z, ev, hZP, ?_, ?_⟩
  · intro s z
    obtain ⟨dg, dh, hg, hh, hd, hy, hz⟩ := hgh s z
    refine ⟨dg, dh, (gh s z).1, (gh s z).2, hg, hh, hd, hy, hz, ?_⟩
    show val s z * _ = _
    simp only [val]
    exact div_mul_cancel₀ _ hz
  · intro s t _ _ hst
    have hu : ((s - t : chartLatNm y A.a τ) : Ω) ≠ 0 := by
      intro h0
      exact hst (sub_eq_zero.mp (Subtype.ext h0))
    obtain ⟨z, hzZ, dg, dh, g, h, hg, hh, hd, hy, hz, hb⟩ := hsep _ (s - t).2 hu
    refine ⟨⟨z, hzZ⟩, ?_⟩
    have hev : ev s ⟨z, hzZ⟩ - ev t ⟨z, hzZ⟩ = val (s - t) ⟨z, hzZ⟩ := by
      rw [← Pi.sub_apply, ← map_sub]
      rfl
    rw [hev, hval (s - t) ⟨z, hzZ⟩ g h ⟨dg, dh, hg, hh, hd, hy, hz⟩, norm_div]
    rw [le_div_iff₀ (norm_pos_iff.mpr hz)]
    exact hb

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombExpand
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis famExt_symm)

noncomputable section

set_option linter.unusedSectionVars false

namespace ZCombExpand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {J : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem famExt_symm_of (e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (he : ∀ i, IsSmoothHerm (e i))
    (hJ : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
      J P n (L ∘ σ) = J P n L) :
    IsSymmForm (famExt J P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hJ (e ∘ s) σ.symm fun j => he _]

theorem famExt_expand (e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hs : IsSymmForm (famExt J P n e)) (q p : ℝ) :
    famExt J P n e (fun _ => ![q, p]) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * q ^ (n - i) * p ^ i *
        J P n (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) := by
  classical
  have hw : (fun _ : Fin n => (![q, p] : Fin 2 → ℝ)) =
      fun _ => p • (Pi.single 1 1 : Fin 2 → ℝ) + q • (Pi.single 0 1 : Fin 2 → ℝ) := by
    funext j i
    fin_cases i <;> simp
  rw [hw, symm_expand _ hs, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega]
  have hmix : (mix (n - i) (Pi.single 0 1) (p • Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).piecewise
        (fun j => p • (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) j)
        (mix (n - i) (Pi.single 0 1) (Pi.single 1 1)) := by
    funext j
    by_cases h : (j : ℕ) < n - i
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simp; omega)]
      simp [mix, h]
    · rw [Finset.piecewise_eq_of_mem _ _ _ (by simp; omega)]
      simp [mix, h]
  have hcard : (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).card = i := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, Fin.card_filter_val_lt]
    omega
  have hbasis : (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      fun j => Pi.single ((fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) j) 1 := by
    funext j
    simp only [mix]
    split_ifs <;> rfl
  have hlist : (e ∘ fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) =
      fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1 := by
    funext j
    simp only [Function.comp]
    split_ifs <;> rfl
  rw [hmix, MultilinearMap.map_piecewise_smul, Finset.prod_const, hcard, hbasis, famExt_basis, hlist,
    smul_eq_mul, Nat.choose_symm hin]
  simp only [RingHom.id_apply]
  ring

end ZCombExpand

theorem ZCombExpand.proof : ZCombExpand.Statement := by
  intro K _ ι _ I hI P d M H q p hP hM hH
  set e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ![M, H] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    fin_cases i
    · exact hM
    · exact hH
  set Z := HermLine.zcomb M H (q : ℤ) (p : ℤ) with hZ_def
  have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hM hH _ _
  refine ⟨?_, ?_⟩
  · have hposition : ∀ (L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin d), (∀ j, IsSmoothHerm (L j)) →
        I P d (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * I P d (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * I P d (Function.update L a (e 1)) := by
      intro L a hL
      cases d with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hM hH (q : ℤ) (p : ℤ)
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := I) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, ZCombExpand.famExt_expand e (famExt_symm hI hP e he)]
    rfl
  · intro hd
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    let J : Ideal (MRing ι) → (m : ℕ) → (Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ :=
      fun P' m L => I P' (m + 1) (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L)
    have hcons : ∀ L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, (∀ j, IsSmoothHerm (L j)) →
        ∀ j, IsSmoothHerm (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L j) := by
      intro L hL j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hM
      · simpa using hL j
    have hsymm : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
        J P n (L ∘ σ) = J P n L := by
      intro L σ hL
      have hc : (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (L ∘ σ) : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
          (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M L) ∘ (Equiv.Perm.decomposeFin.symm (0, σ)) := by
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
        · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
      show I P (n + 1) _ = I P (n + 1) _
      rw [hc, hI.1 P (n + 1) _ _ hP (hcons L hL)]
    have hposition : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        J P n (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * J P n (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * J P n (Function.update L a (e 1)) := by
      intro L a hL
      show I P (n + 1) _ = _ * I P (n + 1) _ + _ * I P (n + 1) _
      rw [Fin.cons_update, Fin.cons_update, Fin.cons_update]
      have h := ZCombLimit.fam_update_zcomb_int hI hP _ (hcons L hL) a.succ hM hH (q : ℤ) (p : ℤ)
      simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := J) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    have hl : (fun j : Fin (n + 1) => if (j : ℕ) = 0 then M else Z) =
        Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (fun _ : Fin n => Z) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp
    rw [hl, show I P (n + 1) (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M (fun _ : Fin n => Z)) =
      J P n (fun _ => Z) from rfl, key,
      ZCombExpand.famExt_expand e (ZCombExpand.famExt_symm_of e he hsymm), Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hl2 : (Fin.cons (α := fun _ => ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) M
        (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) =
        fun j : Fin (n + 1) => if (j : ℕ) < n + 1 - i then M else H := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero]
        exact (if_pos (show ((0 : Fin (n + 1)) : ℕ) < n + 1 - i by simp; omega)).symm
      · simp only [Fin.cons_succ, Fin.val_succ]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (by omega) h2
        · exact absurd (by omega) h1
        · rfl
    show _ * I P (n + 1) _ = _
    rw [hl2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEuclideanSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

namespace EuclideanSections

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [∀ k, Fintype (ι k)] in
theorem mul_mem_chartLat {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact mul_mem (hs c hc) (ht c hc)

theorem isBoundedH_mono {P : Ideal (MRing ι)} {y : (Σ k, ι k) → Ω} {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {τ : ℕ} {s : Ω}
    {c c' : ℝ} (hs : IsBoundedH P y A τ c s) (hc : c ≤ c') : IsBoundedH P y A τ c' s := by
  intro dg dh g h z hg hh hd he hz
  refine (hs dg dh g h z hg hh hd he hz).trans ?_
  have h0 : 0 ≤ A.h z ^ τ := pow_nonneg (A.pos z hz.1).le τ
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (norm_nonneg (eval z (map (Int.castRingHom ℂ) h)))) h0

theorem eventually_shift_le (D m : ℕ) (b E δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n ≤ N → N ≤ n + m →
      b * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) + E * ((N : ℝ) + 1) ^ D ≤
        (b + δ) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
  set F : ℝ := ((D + 1).factorial : ℝ) with hFdef
  have hF0 : 0 < F := by positivity
  have hlin : ∀ c : ℝ, (fun n : ℕ => (n : ℝ) + c) ~[atTop] fun n : ℕ => (n : ℝ) := fun c =>
    IsEquivalent.refl.add_isLittleO ((isLittleO_const_id_atTop c).comp_tendsto tendsto_natCast_atTop_atTop)
  have hu : (fun n : ℕ => ((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := (hlin m).pow (D + 1)
  have hv : (fun n : ℕ => ((n : ℝ) + (m + 1)) ^ D) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) :=
    ((hlin (m + 1)).pow D).isBigO.trans_isLittleO
      ((isLittleO_pow_pow_atTop_of_lt (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop)
  set c₁ := δ / (2 * (|b| + 1)) with hc₁
  set c₂ := δ / (2 * F * (|E| + 1)) with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hc₂0 : 0 < c₂ := by positivity
  have hbc : |b| * c₁ ≤ δ / 2 := by
    rw [hc₁, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg b]
  have hEc : F * (|E| * c₂) ≤ δ / 2 := by
    rw [hc₂, mul_div_assoc', mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg E]
  filter_upwards [hu.def hc₁0, hv.def hc₂0] with n h1 h2
  intro N hnN hNn
  have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
  have hN1 : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hN2 : (N : ℝ) ≤ n + m := by exact_mod_cast hNn
  have hw : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
  have hpow : (N : ℝ) ^ (D + 1) ≤ ((n : ℝ) + m) ^ (D + 1) := pow_le_pow_left₀ (by positivity) hN2 _
  have hpow' : (n : ℝ) ^ (D + 1) ≤ (N : ℝ) ^ (D + 1) := pow_le_pow_left₀ hn0 hN1 _
  have hv' : ((N : ℝ) + 1) ^ D ≤ ((n : ℝ) + (m + 1)) ^ D := pow_le_pow_left₀ (by positivity) (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by linarith)] at h1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw, abs_of_nonneg (by positivity)] at h2
  have hb : b * (N : ℝ) ^ (D + 1) ≤
      b * (n : ℝ) ^ (D + 1) + |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) := by
    rcases le_total 0 b with hb | hb
    · rw [abs_of_nonneg hb]; nlinarith
    · nlinarith [abs_nonneg b, mul_le_mul_of_nonpos_left hpow' hb]
  have hE : E * ((N : ℝ) + 1) ^ D ≤ |E| * ((n : ℝ) + (m + 1)) ^ D :=
    (mul_le_mul_of_nonneg_right (le_abs_self E) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hv' (abs_nonneg E))
  have hb2 : |b| * (((n : ℝ) + m) ^ (D + 1) - (n : ℝ) ^ (D + 1)) ≤ δ / 2 * (n : ℝ) ^ (D + 1) :=
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg b)).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hbc hw)
  have hE2 : |E| * F * ((n : ℝ) + (m + 1)) ^ D ≤ δ / 2 * (n : ℝ) ^ (D + 1) := by
    have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg E) hF0.le)
    nlinarith [mul_le_mul_of_nonneg_right hEc hw]
  have key : b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D) ≤ (b + δ) * (n : ℝ) ^ (D + 1) := by
    nlinarith [mul_le_mul_of_nonneg_left hE hF0.le]
  rw [show b * ((N : ℝ) ^ (D + 1) / F) + E * ((N : ℝ) + 1) ^ D =
      (b * (N : ℝ) ^ (D + 1) + F * (E * ((N : ℝ) + 1) ^ D)) / F by field_simp, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right key hF0.le

end EuclideanSections


open EuclideanSections in
theorem EuclideanSections.proof (hP : EuclideanSectionsPower.Statement) (hS : SmallSectionsNonzero.Statement)
    (hL : SublatticeDegree.Statement) (hG : SuccessiveMinimaSpan.Statement) : EuclideanSections.Statement := by
  intro K _ ι _ Ω _ _ y D A P0 II hD hII har hb hA hconj
  obtain ⟨r, φ, hinj, hdisc, hlat, hsup, hcon, ⟨Cr, hr⟩, m, hm, hdeg⟩ :=
    hP K ι Ω y D A P0 II hD hII har hb hA hconj
  obtain ⟨C, hC⟩ := hG K ι Ω y D A P0 hD har hb hA
  refine ⟨r, φ, hinj, hdisc, hlat, hsup, ⟨Cr, hr⟩, fun ε hε => ?_⟩
  set C₁ := max C 1 with hC₁
  have hC₁1 : (1 : ℝ) ≤ C₁ := le_max_right _ _
  have hlog : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁1
  set I := II K ι (mCoordIdeal y) (D + 1) (fun _ => A) with hI
  obtain ⟨Q, hQ⟩ := eventually_atTop.1 (hdeg (ε / 2) (half_pos hε))
  filter_upwards [eventually_shift_le D m (I + ε / 2) (Cr * Real.log C₁) (ε / 2) (half_pos hε),
    eventually_ge_atTop (m * Q)] with n hn hnQ
  intro _ _
  have hqQ : Q ≤ n / m + 1 := Nat.le_succ_of_le ((Nat.le_div_iff_mul_le hm).2 (by rw [mul_comm]; exact hnQ))
  have hnN : n ≤ m * (n / m + 1) := (Nat.lt_mul_div_succ n hm).le
  have hNn : m * (n / m + 1) ≤ n + m := by
    have := Nat.mul_div_le n m
    rw [mul_add, mul_one]
    omega
  suffices main : ∀ N : ℕ, n ≤ N → N ≤ n + m →
      -Real.log (ZLattice.covolume (imageLattice (φ N))) ≤
        (I + ε / 2) * ((N : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) →
      -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
        (I + ε) * ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) from
    main _ hnN hNn (hQ (n / m + 1) hqQ)
  intro N hnN hNn h1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnN
  obtain ⟨t, ht, ht0, hts⟩ := hS K ι Ω y D A P0 har hb hA j

  let ψ : chartLat y A.a n →+ chartLat y A.a (n + j) :=
    { toFun := fun s => ⟨(s : Ω) * t, mul_mem_chartLat s.2 ht⟩
      map_zero' := by ext; simp
      map_add' := fun s s' => by ext; simp [add_mul] }
  have hψ : Function.Injective ψ := fun s s' h =>
    Subtype.ext (mul_right_cancel₀ ht0 (congrArg Subtype.val h))
  have hψn : ∀ s, ‖φ (n + j) (ψ s)‖ ≤ ‖φ n s‖ := fun s => hcon n j s ⟨t, ht⟩ (ψ s) hts rfl

  have hclos : AddSubgroup.closure
      {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro x
    have hx : (x : Ω) ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s} := by
      rw [hC (n + j)]; exact x.2
    have key : ∀ z (hz : z ∈ AddSubgroup.closure
        {s | s ∈ chartLat y A.a (n + j) ∧ IsBoundedH (mCoordIdeal y) y A (n + j) C s}),
        ∃ hz' : z ∈ chartLat y A.a (n + j), (⟨z, hz'⟩ : chartLat y A.a (n + j)) ∈ AddSubgroup.closure
          {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)} := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem z hz => exact ⟨hz.1, AddSubgroup.subset_closure (isBoundedH_mono hz.2 (le_max_left _ _))⟩
      | zero => exact ⟨zero_mem _, zero_mem _⟩
      | add z w _ _ hz hw =>
        obtain ⟨hz', hz''⟩ := hz
        obtain ⟨hw', hw''⟩ := hw
        exact ⟨add_mem hz' hw', add_mem hz'' hw''⟩
      | neg z _ hz =>
        obtain ⟨hz', hz''⟩ := hz
        exact ⟨neg_mem hz', neg_mem hz''⟩
    obtain ⟨_, hx'⟩ := key x hx
    exact hx'
  have hbound : ∀ s ∈ {s : chartLat y A.a (n + j) | IsBoundedH (mCoordIdeal y) y A (n + j) C₁ (s : Ω)},
      ‖φ (n + j) s‖ ≤ C₁ := fun s hs => hsup (n + j) C₁ s (by linarith) hs
  have h2 := hL (chartLat y A.a (n + j)) (chartLat y A.a n) (r (n + j)) (r n) (φ (n + j)) (φ n) ψ _ C₁
    (hinj _) (hinj _) hψ hψn hclos hbound hC₁1
  have h3 : (r (n + j) : ℝ) * Real.log C₁ ≤ Cr * Real.log C₁ * (((n + j : ℕ) : ℝ) + 1) ^ D := by
    have := mul_le_mul_of_nonneg_right (hr (n + j)) hlog
    linarith
  have h4 := hn (n + j) (Nat.le_add_right n j) hNn
  have h5 : I + ε / 2 + ε / 2 = I + ε := by ring
  rw [h5] at h4
  linarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphImage
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

theorem BlockGraphImage.proof : BlockGraphImage.Statement := by
  intro K _ ι _ Ω _ _ κ _ y k₀ M N x hB

  let φ : MRing ι ⧸ mCoordIdeal y →+* MvPolynomial K Ω :=
    Ideal.Quotient.lift (mCoordIdeal y) (mConeMap y).toRingHom fun a ha => RingHom.mem_ker.1 ha
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.2 ha)

  let ψ : Polynomial Ω →+* MvPolynomial Unit (MvPolynomial K Ω) :=
    Polynomial.eval₂RingHom ((C : MvPolynomial K Ω →+* _).comp C) (C (X k₀) * X ())
  let ev : MvPolynomial Unit (MvPolynomial K Ω) →+* Polynomial Ω :=
    eval₂Hom (Polynomial.C.comp (MvPolynomial.eval fun _ => (1 : Ω))) fun _ => Polynomial.X
  have hev : ∀ p, ev (ψ p) = p := by
    have h : ev.comp ψ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [ψ, ev]
      · simp [ψ, ev]
    exact fun p => RingHom.congr_fun h p

  have hcone : ∀ q, mConeMap y (blockForms k₀ M q) = C (x q) * X k₀ := by
    intro q
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [blockForms, map_sum, map_mul, mConeMap, aeval_X, aeval_C, hB.1 q, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_assoc]
  let G : MRing (GlobalTheory κ) →+* MvPolynomial Unit (MvPolynomial K Ω) :=
    (MvPolynomial.map φ).comp ((graphMap (mCoordIdeal y) (blockForms k₀ M)).comp
      (rename (inrV (ι := ι) (ι₂ := GlobalTheory κ)) : MRing (GlobalTheory κ) →ₐ[ℤ] _).toRingHom)
  have hG : ∀ f, G f = ψ (coneMap ℤ x f) := by
    have h : G = ψ.comp (coneMap ℤ x).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro n
        exact RingHom.congr_fun (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ x).toRingHom).comp C)) n
      · rintro ⟨u, j⟩
        cases u
        simp only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
        rw [show (inrV (ι := ι) (ι₂ := GlobalTheory κ) ⟨(), j⟩) = ⟨Sum.inr (), j⟩ from rfl]
        rw [graphMap, eval₂Hom_X']
        simp only [map_mul, map_C, map_X, coneMap, aeval_X]
        rw [show φ (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨(), j⟩)) = C (x ⟨(), j⟩) * X k₀ from
          (Ideal.Quotient.lift_mk _ _ _).trans (hcone _)]
        simp [ψ, mul_assoc]
    exact fun f => RingHom.congr_fun h f
  ext f
  show rename inrV f ∈ RingHom.ker (graphMap (mCoordIdeal y) (blockForms k₀ M)) ↔ f ∈ RingHom.ker (coneMap ℤ x)
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have h0 : G f = 0 := by
      show MvPolynomial.map φ (graphMap (mCoordIdeal y) (blockForms k₀ M) (rename inrV f)) = 0
      rw [h, map_zero]
    rw [hG] at h0
    rw [← hev (coneMap ℤ x f), h0, map_zero]
  · intro h
    apply MvPolynomial.map_injective φ hφ
    rw [map_zero]
    show G f = 0
    rw [hG, h, map_zero]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseSemipos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

theorem leviForm_comp_clm {J : Type*} [Fintype J] (φ : (J → ℂ) → ℝ) (L : (J → ℂ) →L[ℝ] (J → ℂ))
    (hL : ∀ w, L (Complex.I • w) = Complex.I • L w) (z : J → ℂ)
    (hφ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ φ (L y))
    (hφ2 : DifferentiableAt ℝ (fderiv ℝ φ) (L z)) (w : J → ℂ) :
    leviForm (φ ∘ L) z w = leviForm φ (L z) (L w) := by
  set R := (ContinuousLinearMap.compL ℝ (J → ℂ) (J → ℂ) ℝ).flip L with hR
  have hev : fderiv ℝ (φ ∘ L) =ᶠ[𝓝 z] fun y => R (fderiv ℝ φ (L y)) := by
    filter_upwards [hφ] with y hy
    rw [fderiv_comp y hy L.differentiableAt, L.fderiv]
    rfl
  have hd : HasFDerivAt (fun y => R (fderiv ℝ φ (L y))) (R.comp ((fderiv ℝ (fderiv ℝ φ) (L z)).comp L)) z :=
    R.hasFDerivAt.comp z (hφ2.hasFDerivAt.comp z L.hasFDerivAt)
  have key : ∀ v, fderiv ℝ (fderiv ℝ (φ ∘ L)) z v v = fderiv ℝ (fderiv ℝ φ) (L z) (L v) (L v) := by
    intro v
    rw [hev.fderiv_eq, hd.fderiv]
    rfl
  unfold leviForm
  rw [key, key, hL]

theorem contDiffAt_log_fs {J : Type} [Fintype J] {y : J → ℂ} (hy : y ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.log ((fsMetric (ι := J)).ρ y)) y :=
  ((ProjLine.isSmoothMetric_fs (J := J) y hy).contDiffAt (isOpen_ne.mem_nhds hy)).log
    ((fsMetric (ι := J)).pos y hy).ne'

namespace Veronese

def scaleLin (D : ℕ) : (Ix (Idx D) → ℂ) →ₗ[ℂ] (Ix (Idx D) → ℂ) where
  toFun := scale D
  map_add' z z' := by
    funext q
    simp only [scale, Pi.add_apply]
    ring
  map_smul' c z := by
    funext q
    simp only [scale, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

def scaleL (D : ℕ) : (Ix (Idx D) → ℂ) →L[ℝ] (Ix (Idx D) → ℂ) :=
  (LinearMap.toContinuousLinearMap (scaleLin D)).restrictScalars ℝ

theorem scaleL_I (D : ℕ) (w : Ix (Idx D) → ℂ) : scaleL D (Complex.I • w) = Complex.I • scaleL D w :=
  (scaleLin D).map_smul Complex.I w

end Veronese

open Veronese

theorem VeroneseSemipos.proof : VeroneseSemipos.Statement := by
  intro D
  refine ⟨(isSmoothMetric_metric D).mono fun z hz h0 => ?_, fun z hz w _ => ?_⟩
  · obtain ⟨i, hi⟩ := hz ()
    exact hi (congrFun h0 _)
  · have hz0 : z ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := hz.1 ()
      exact hi (congrFun h0 _)
    have e : (fun z => Real.log ((ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofCone (metric D)).h z)) =
        (fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) ∘ scaleL D := rfl
    have hφ : ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ (fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) (scaleL D y) := by
      filter_upwards [isOpen_ne.mem_nhds hz0] with y hy
      exact (contDiffAt_log_fs (scale_ne_zero hy)).differentiableAt (by simp)
    have hφ2 : DifferentiableAt ℝ (fderiv ℝ fun y => Real.log ((fsMetric (ι := Ix (Idx D))).ρ y)) (scaleL D z) :=
      ((contDiffAt_log_fs (scale_ne_zero hz0)).fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).differentiableAt
        one_ne_zero
    rw [e, leviForm_comp_clm _ _ (scaleL_I D) z hφ hφ2 w]
    exact ProjLine.leviForm_log_fs_nonneg (scale_ne_zero hz0) (scaleL D w)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
