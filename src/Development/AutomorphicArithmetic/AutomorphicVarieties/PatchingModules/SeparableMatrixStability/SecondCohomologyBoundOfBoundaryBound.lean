module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelRed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraFin
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ultra_fin :
    ∀ (ι Z : Type) (U : Ultrafilter ι) (a : ι → Z) (s : Set Z), s.Finite → (∀ᶠ i in (U : Filter ι), a i ∈ s) →
      ∃! z, z ∈ s ∧ ∀ᶠ i in (U : Filter ι), a i = z := by
  intro ι Z U a s hs h
  have hsub : {i | a i ∈ s} ⊆ ⋃ z ∈ s, {i | a i = z} := by
    intro i hi
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨a i, hi, rfl⟩
  have hmem : (⋃ z ∈ s, {i | a i = z}) ∈ U := U.1.sets_of_superset h hsub
  obtain ⟨z, hz, hzU⟩ := (Ultrafilter.finite_biUnion_mem_iff hs).1 hmem
  refine ⟨z, ⟨hz, hzU⟩, ?_⟩
  rintro w ⟨-, hw⟩
  obtain ⟨i, hi1, hi2⟩ := (hw.and hzU).exists
  exact hi1.symm.trans hi2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelmerSecondExistsUltrafilterLimit
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelmerSecondClosedUnderLimits
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa.SelmerClosedness

private theorem q_iff {K : Type} [Field K] (m : ℕ) (a b : PowerSeries K) :
    Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) a = Ideal.Quotient.mk _ b ↔
      ∀ d < m, PowerSeries.coeff d a = PowerSeries.coeff d b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  simp only [map_sub, sub_eq_zero]

private theorem ulim_A {K : Type} [Field K] [Finite K] (U : Ultrafilter ℕ) (a : ℕ → PowerSeries K) :
    ∃ b : PowerSeries K, ∀ m, ∀ᶠ N in (U : Filter ℕ),
      Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ m}) (a N) = Ideal.Quotient.mk _ b := by
  classical
  have hv : ∀ d, ∃ v : K, ∀ᶠ N in (U : Filter ℕ), PowerSeries.coeff d (a N) = v := by
    intro d
    obtain ⟨v, hv⟩ := Ultrafilter.eq_pure_of_finite (U.map fun N => PowerSeries.coeff d (a N))
    refine ⟨v, ?_⟩
    have hmem : ({v} : Set K) ∈ (U.map fun N => PowerSeries.coeff d (a N)) := by
      rw [hv, Ultrafilter.mem_pure]
      exact Set.mem_singleton v
    exact Ultrafilter.mem_map.mp hmem
  choose v hv using hv
  refine ⟨PowerSeries.mk v, fun m => ?_⟩
  have hall : ∀ᶠ N in (U : Filter ℕ), ∀ d ∈ Finset.range m, PowerSeries.coeff d (a N) = v d :=
    (Filter.eventually_all_finset _).mpr (fun d _ => hv d)
  filter_upwards [hall] with N hN
  rw [q_iff]
  intro d hd
  rw [PowerSeries.coeff_mk]
  exact hN d (Finset.mem_range.mpr hd)

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n)

private theorem q_mono {m N : ℕ} (h : m ≤ N) {a b : x.A}
    (e : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) a = Ideal.Quotient.mk _ b) :
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a = Ideal.Quotient.mk _ b := by
  rw [Ideal.Quotient.eq] at e ⊢
  exact (Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ h)) e

private theorem q_sep {a b : x.A}
    (e : ∀ m, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a = Ideal.Quotient.mk _ b) : a = b :=
  PowerSeries.ext fun d => (q_iff (d + 1) a b).1 (e _) d (Nat.lt_succ_self d)

private theorem red_iff (g m : ℕ) (a b : DD x.A g) : x.redD g m a = x.redD g m b ↔
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a.a = Ideal.Quotient.mk _ b.a ∧
    (∀ j, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (a.ep j) = Ideal.Quotient.mk _ (b.ep j)) ∧
    (∀ j, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (a.ep' j) = Ideal.Quotient.mk _ (b.ep' j)) ∧
    Ideal.Quotient.mk (Ideal.span {x.t ^ m}) a.eta = Ideal.Quotient.mk _ b.eta := by
  constructor
  · intro e
    exact ⟨congrArg DD.a e, fun j => congrFun (congrArg DD.ep e) j,
      fun j => congrFun (congrArg DD.ep' e) j, congrArg DD.eta e⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact DD.ext h1 (funext h2) (funext h3) h4

private theorem red_mono {g m N : ℕ} (h : m ≤ N) {a b : DD x.A g} (e : x.redD g N a = x.redD g N b) :
    x.redD g m a = x.redD g m b := by
  rw [red_iff] at e ⊢
  obtain ⟨h1, h2, h3, h4⟩ := e
  exact ⟨q_mono x h h1, fun j => q_mono x h (h2 j), fun j => q_mono x h (h3 j), q_mono x h h4⟩

private theorem red_sep {g : ℕ} {a b : DD x.A g} (e : ∀ m, x.redD g m a = x.redD g m b) : a = b := by
  refine DD.ext ?_ ?_ ?_ ?_
  · exact q_sep x fun m => ((red_iff x g m a b).mp (e m)).1
  · funext j
    exact q_sep x fun m => ((red_iff x g m a b).mp (e m)).2.1 j
  · funext j
    exact q_sep x fun m => ((red_iff x g m a b).mp (e m)).2.2.1 j
  · exact q_sep x fun m => ((red_iff x g m a b).mp (e m)).2.2.2

private theorem red_surj (g m : ℕ) : Function.Surjective (x.redD g m) := by
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y.a
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective y.eta
  choose e1 he1 using fun j => Ideal.Quotient.mk_surjective (y.ep j)
  choose e2 he2 using fun j => Ideal.Quotient.mk_surjective (y.ep' j)
  exact ⟨⟨a, e1, e2, t⟩, DD.ext ha (funext he1) (funext he2) ht⟩

private theorem dd_components_smul {A : Type} [CommRing A] {g : ℕ} (c : A) (y : DD A g) :
    (c • y).a = c * y.a ∧ (c • y).ep = c • y.ep ∧ (c • y).ep' = c • y.ep' ∧ (c • y).eta = c * y.eta := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · funext j
    show c * y.ep j + 0 * y.a = c * y.ep j
    ring
  · funext j
    show c * y.ep' j + 0 * y.a = c * y.ep' j
    ring
  · show c * y.eta + 0 * y.a + ∑ j, (0 * y.ep' j + 0 * y.ep j) = c * y.eta
    simp

private theorem red_ker {g m : ℕ} {a b : DD x.A g} (e : x.redD g m a = x.redD g m b) :
    a - b ∈ Ideal.span {algebraMap x.A (DD x.A g) x.t} ^ m := by
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.mem_span_singleton']
  obtain ⟨h1, h2, h3, h4⟩ := (red_iff x g m a b).mp e
  have hc : ∀ u v : x.A, Ideal.Quotient.mk (Ideal.span {x.t ^ m}) u = Ideal.Quotient.mk _ v →
      ∃ w, u - v = x.t ^ m * w := by
    intro u v huv
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at huv
    exact huv
  obtain ⟨w1, hw1⟩ := hc _ _ h1
  obtain ⟨w4, hw4⟩ := hc _ _ h4
  choose w2 hw2 using fun j => hc _ _ (h2 j)
  choose w3 hw3 using fun j => hc _ _ (h3 j)
  refine ⟨⟨w1, w2, w3, w4⟩, ?_⟩
  rw [mul_comm, ← Algebra.smul_def]
  obtain ⟨s1, s2, s3, s4⟩ := dd_components_smul (x.t ^ m) (⟨w1, w2, w3, w4⟩ : DD x.A g)
  refine DD.ext ?_ ?_ ?_ ?_
  · rw [s1]
    exact hw1.symm
  · rw [s2]
    funext j
    exact (hw2 j).symm
  · rw [s3]
    funext j
    exact (hw3 j).symm
  · rw [s4]
    exact hw4.symm

private theorem pow_bot (g m : ℕ) : Ideal.span {algebraMap x.A (DD (x.Am m) g) x.t} ^ m = ⊥ := by
  rw [Ideal.span_singleton_pow, ← map_pow, Ideal.span_singleton_eq_bot]
  show DD.C (algebraMap x.A (x.Am m) (x.t ^ m)) = 0
  rw [Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]

private theorem ulim_D (g : ℕ) (U : Ultrafilter ℕ) (a : ℕ → DD x.A g) :
    ∃ b : DD x.A g, ∀ m, ∀ᶠ N in (U : Filter ℕ), x.redD g m (a N) = x.redD g m b := by
  obtain ⟨ba, hba⟩ := ulim_A U (fun N => (a N).a)
  obtain ⟨bt, hbt⟩ := ulim_A U (fun N => (a N).eta)
  choose b1 hb1 using fun j => ulim_A U (fun N => (a N).ep j)
  choose b2 hb2 using fun j => ulim_A U (fun N => (a N).ep' j)
  refine ⟨⟨ba, b1, b2, bt⟩, fun m => ?_⟩
  filter_upwards [hba m, hbt m, Filter.eventually_all.mpr (fun j => hb1 j m),
    Filter.eventually_all.mpr (fun j => hb2 j m)] with N h1 h4 h2 h3
  rw [red_iff]
  exact ⟨h1, h2, h3, h4⟩

private theorem part_of (g : ℕ) (b1 b2 b3 b4 : Bool) (y : DD x.A g)
    (h : ∀ m, ∃ N y', m ≤ N ∧ x.redD g m y = x.redD g m y' ∧ x.redD g N y' ∈ ddPart x.A (x.Am N) g b1 b2 b3 b4) :
    y ∈ ddPart x.A x.A g b1 b2 b3 b4 := by
  refine ⟨fun hb => ?_, fun hb => ?_, fun hb => ?_, fun hb => ?_⟩
  · apply q_sep x
    intro m
    obtain ⟨N, y', hmN, e, hp⟩ := h m
    have h1 := ((red_iff x g m y y').mp e).1
    have h2 : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) y'.a = Ideal.Quotient.mk _ 0 := by
      rw [map_zero]
      exact hp.1 hb
    rw [h1]
    exact q_mono x hmN h2
  · funext j
    show y.ep j = 0
    apply q_sep x
    intro m
    obtain ⟨N, y', hmN, e, hp⟩ := h m
    have h1 := ((red_iff x g m y y').mp e).2.1 j
    have h2 : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) (y'.ep j) = Ideal.Quotient.mk _ 0 := by
      rw [map_zero]
      exact congrFun (hp.2.1 hb) j
    rw [h1]
    exact q_mono x hmN h2
  · funext j
    show y.ep' j = 0
    apply q_sep x
    intro m
    obtain ⟨N, y', hmN, e, hp⟩ := h m
    have h1 := ((red_iff x g m y y').mp e).2.2.1 j
    have h2 : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) (y'.ep' j) = Ideal.Quotient.mk _ 0 := by
      rw [map_zero]
      exact congrFun (hp.2.2.1 hb) j
    rw [h1]
    exact q_mono x hmN h2
  · apply q_sep x
    intro m
    obtain ⟨N, y', hmN, e, hp⟩ := h m
    have h1 := ((red_iff x g m y y').mp e).2.2.2
    have h2 : Ideal.Quotient.mk (Ideal.span {x.t ^ N}) y'.eta = Ideal.Quotient.mk _ 0 := by
      rw [map_zero]
      exact hp.2.2.2 hb
    rw [h1]
    exact q_mono x hmN h2

private theorem mem_second_order_of_reductions (g : ℕ) (Y : Matrix (Fin n) (Fin n) (DD x.A g))
    (h : ∀ m, ∃ (N : ℕ) (Y' : Matrix (Fin n) (Fin n) (DD x.A g)), m ≤ N ∧ Y.map (x.redD g m) = Y'.map (x.redD g m) ∧
      Y'.map (x.redD g N) ∈ W2 n x.A (x.Am N) g x.a) :
    Y ∈ W2 n x.A x.A g x.a := by
  intro i j
  refine ⟨fun e => part_of x g _ _ _ _ _ fun m => ?_, fun e => part_of x g _ _ _ _ _ fun m => ?_⟩
  · obtain ⟨N, Y', hN, h1, h2⟩ := h m
    exact ⟨N, Y' i j, hN, congrFun (congrFun h1 i) j, (h2 i j).1 e⟩
  · obtain ⟨N, Y', hN, h1, h2⟩ := h m
    exact ⟨N, Y' i j, hN, congrFun (congrFun h1 i) j, (h2 i j).2 e⟩

variable {x} (k : Kap x) (m : ℕ)

private theorem map_ep (Z : Fin k.g → Matrix (Fin n) (Fin n) x.A) :
    (x.redD k.g m).mapMatrix (DD.epM fun j => (Z j).map (algebraMap x.A x.A)) =
      DD.epM fun j => (Z j).map (algebraMap x.A (x.Am m)) := by
  ext a b <;> simp [DD.epM, DD.map]

private theorem map_al (Z : Matrix (Fin n) (Fin n) x.A) :
    (x.redD k.g m).mapMatrix (Z.map (algebraMap x.A (DD x.A k.g))) = Z.map (algebraMap x.A (DD (x.Am m) k.g)) := by
  rw [AlgHom.mapMatrix_apply, Matrix.map_map]
  congr 1

private theorem map_ρ1 (g : F.G₀) : (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = k.ρ1 (x.Am m) g := by
  unfold Kap.ρ1 NP.ρX
  rw [map_mul, map_add (f := _), map_one, map_ep, map_al]

private theorem map_weyl_lift_reduction (v : F.Vl) : (x.redD k.g m).mapMatrix (k.w1 x.A v) = k.w1 (x.Am m) v := by
  unfold Kap.w1 NP.wX
  rw [map_mul, map_sub, map_one, map_ep, map_al]

private theorem map_inverse_weyl_lift_reduction (v : F.Vl) : (x.redD k.g m).mapMatrix (k.wi1 x.A v) = k.wi1 (x.Am m) v := by
  unfold Kap.wi1 NP.wiX
  rw [map_mul, map_add (f := _), map_one, map_ep, map_al]

private theorem mat_sep {Y Z : Matrix (Fin n) (Fin n) (DD x.A k.g)}
    (e : ∀ m, (x.redD k.g m).mapMatrix Y = (x.redD k.g m).mapMatrix Z) : Y = Z := by
  funext i j
  exact red_sep x fun m => congrFun (congrFun (e m) i) j

end UpperTheory.V.Pa.SelmerClosedness

open UpperTheory.V.Pa.SelmerClosedness in
theorem UpperTheory.V.Pa.selmer_second_closed_under_limits :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (z : G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), (∀ m, (fun g => (z g).map (x.redD k.g m)) ∈ Sel2 h (x.Am m) k) → z ∈ Sel2 h x.A k := by
  intro l _ L G G0 h n x k z hyp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    apply mem_second_order_of_reductions x k.g (z g)
    intro m
    obtain ⟨hW, -⟩ := hyp m
    exact ⟨m, z g, le_rfl, rfl, hW g⟩
  · intro i j N
    obtain ⟨-, hA, -⟩ := hyp N
    have hl := hA i j N
    have hf : IsLocallyConstant fun g => x.redD k.g N (z g i j) := by
      refine IsLocallyConstant.desc _ _ hl (fun a b hab => ?_)
      rw [Ideal.Quotient.eq, pow_bot, Ideal.mem_bot, sub_eq_zero] at hab
      exact hab
    let s := Function.surjInv (red_surj x k.g N)
    have hcomp : (fun g => Ideal.Quotient.mk (Ideal.span {algebraMap x.A (DD x.A k.g) x.t} ^ N) (z g i j)) =
        (fun y => Ideal.Quotient.mk (Ideal.span {algebraMap x.A (DD x.A k.g) x.t} ^ N) (s y)) ∘
          (fun g => x.redD k.g N (z g i j)) := by
      funext g
      simp only [Function.comp]
      rw [Ideal.Quotient.eq]
      exact red_ker x (Function.surjInv_eq (red_surj x k.g N) _).symm
    rw [hcomp]
    exact hf.comp _
  · intro g g'
    beta_reduce
    apply mat_sep k
    intro m
    obtain ⟨-, -, hc, -⟩ := hyp m
    rw [map_add (f := _), map_mul, map_mul, map_ρ1, map_ρ1]
    exact hc g g'
  · intro g
    apply mat_sep k
    intro m
    obtain ⟨-, -, -, hconj, -⟩ := hyp m
    have e := hconj g
    funext a b
    have e' := congrFun (congrFun e a) b
    simp at e' ⊢
    exact e'
  · intro u g hg
    apply mat_sep k
    intro m
    obtain ⟨-, -, -, -, hI, -⟩ := hyp m
    rw [map_zero]
    exact hI u g hg
  · intro v
    have hYm : ∀ m, ∃ Y : Matrix (Fin n) (Fin n) (DD x.A k.g),
        (x.redD k.g m).mapMatrix Y ∈ W2 n x.A (x.Am m) k.g x.a ∧
        LocAt G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (k.w1 (x.Am m)) (k.wi1 (x.Am m))
          (fun g => (z g).map (x.redD k.g m)) v ((x.redD k.g m).mapMatrix Y) := by
      intro m
      obtain ⟨-, -, -, -, -, hL⟩ := hyp m
      obtain ⟨Y0, hY0W, hY0L⟩ := hL v
      choose Yl hYl using fun a b => red_surj x k.g m (Y0 a b)
      have hY0 : (x.redD k.g m).mapMatrix (Matrix.of Yl) = Y0 := by
        funext a b
        exact hYl a b
      refine ⟨Matrix.of Yl, ?_, ?_⟩
      · rw [hY0]
        exact hY0W
      · rw [hY0]
        exact hY0L
    choose Yt hYtW hYtL using hYm
    let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
    choose Y hY using fun a b => ulim_D x k.g U (fun N => Yt N a b)
    have hev : ∀ m, ∃ N, m ≤ N ∧
        (x.redD k.g m).mapMatrix (Matrix.of Y) = (x.redD k.g m).mapMatrix (Yt N) := by
      intro m
      have h1 : ∀ᶠ N in (U : Filter ℕ), ∀ a b, x.redD k.g m (Yt N a b) = x.redD k.g m (Y a b) :=
        Filter.eventually_all.mpr fun a => Filter.eventually_all.mpr fun b => hY a b m
      have h2 : ∀ᶠ N in (U : Filter ℕ), m ≤ N := by
        apply Filter.Eventually.filter_mono Filter.hyperfilter_le_cofinite
        rw [Nat.cofinite_eq_atTop]
        exact Filter.eventually_ge_atTop m
      obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
      refine ⟨N, hN2, ?_⟩
      funext a b
      exact (hN1 a b).symm
    refine ⟨Matrix.of Y, ?_, ?_⟩
    · apply mem_second_order_of_reductions x k.g
      intro m
      obtain ⟨N, hmN, e⟩ := hev m
      exact ⟨N, Yt N, hmN, e, hYtW N⟩
    · intro g
      let E : Matrix (Fin n) (Fin n) (DD x.A k.g) → Matrix (Fin n) (Fin n) (DD x.A k.g) := fun Y1 =>
        k.wi1 x.A v * (z ((G.frame.φ v) g) -
          dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) Y1 ((G.frame.φ v) g)) * k.w1 x.A v
      have hE : ∀ m (Y1 : Matrix (Fin n) (Fin n) (DD x.A k.g)), (x.redD k.g m).mapMatrix (E Y1) =
          k.wi1 (x.Am m) v * ((z ((G.frame.φ v) g)).map (x.redD k.g m) -
            dY G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) ((x.redD k.g m).mapMatrix Y1) ((G.frame.φ v) g)) *
              k.w1 (x.Am m) v := by
        intro m Y1
        simp only [E, dY]
        rw [map_mul, map_mul, map_sub, map_sub, map_mul, map_mul, map_ρ1, map_ρ1, map_weyl_lift_reduction, map_inverse_weyl_lift_reduction]
        rfl
      have hent : ∀ i j, (∀ N, (k.wi1 (x.Am N) v * ((z ((G.frame.φ v) g)).map (x.redD k.g N) -
            dY G.frame (fun g => k.ρ1 (x.Am N) (h.p₀ g)) ((x.redD k.g N).mapMatrix (Yt N)) ((G.frame.φ v) g)) *
              k.w1 (x.Am N) v) i j = 0) → E (Matrix.of Y) i j = 0 := by
        intro i j h0
        apply red_sep x
        intro m
        obtain ⟨N, hmN, e⟩ := hev m
        have e1 := congrFun (congrFun (hE m (Matrix.of Y)) i) j
        have e2 := congrFun (congrFun (hE m (Yt N)) i) j
        have e3 := congrFun (congrFun (hE N (Yt N)) i) j
        rw [e] at e1
        have e4 : x.redD k.g m (E (Matrix.of Y) i j) = x.redD k.g m (E (Yt N) i j) :=
          e1.trans e2.symm
        rw [e4, map_zero]
        have e5 : x.redD k.g N (E (Yt N) i j) = x.redD k.g N 0 := by
          rw [map_zero]
          exact e3.trans (h0 N)
        rw [red_mono x hmN e5, map_zero]
      exact ⟨fun i j hij => hent i j (fun N => (hYtL N g).1 i j hij),
        fun hg i => hent i i (fun N => (hYtL N g).2 hg i)⟩
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem diag_mk {K : Type} [Field K] (a : ℕ → PowerSeries K) (b : PowerSeries K) (j : ℕ)
    (H : ∀ c < j, Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (c + 1)}) b =
      Ideal.Quotient.mk _ (a c)) :
    Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ j})
      (PowerSeries.mk fun c => PowerSeries.coeff c (a c)) = Ideal.Quotient.mk _ b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro c hc
  have := H c hc
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at this
  have := this c (Nat.lt_succ_self c)
  rw [map_sub, sub_eq_zero] at this ⊢
  rw [PowerSeries.coeff_mk, this]

private theorem lc_of_nil {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (t : R) (ht : IsNilpotent t) (f : Γ → R)
    (hf : AdicCont (Ideal.span {t}) f) : IsLocallyConstant f := by
  obtain ⟨N, hN⟩ := ht
  have h1 : IsLocallyConstant fun g => Ideal.Quotient.mk (Ideal.span {t} ^ N) (f g) := hf N
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk (Ideal.span {t} ^ N)) h1 ?_
  rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_pow, hN, Ideal.span_singleton_eq_bot]

private theorem lc_mat {Γ R : Type} [TopologicalSpace Γ] {n : ℕ} (f : Γ → Matrix (Fin n) (Fin n) R)
    (hf : ∀ i j, IsLocallyConstant fun g => f g i j) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have : ∀ᶠ g in nhds y, ∀ i j, f g i j = f y i j :=
    eventually_all.2 fun i => eventually_all.2 fun j => (hf i j).eventually_eq y
  exact this.mono fun g hg => Matrix.ext hg

private theorem selmer_second_finite_modulo_power (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n)
    (k : Kap x) (hG : TopFG G.Γ) (j : ℕ) : (Sel2 h (x.Am j) k).Finite := by
  obtain ⟨hfin, -, hn, hn', -⟩ := am_fin l G0.frame n x j k.g
  obtain ⟨-, ⟨h1, hm, -⟩, hlc, -⟩ := rho_hom l G0.frame n x k (x.Am j)
  have hfg : TopFG G.G₀ := (TopFG.subgroup_quot G.Γ hG).1 G.η.ker G.η_open
  have := coc_fin G.G₀ (DD (x.Am j) k.g) n (fun g => k.ρ1 (x.Am j) (h.p₀ g)) hfg
    (by simp only [map_one]; exact h1) (fun g g' => by simp only [map_mul]; exact hm _ _)
    ((hlc hn).2.comp_continuous h.p₀_cont)
  refine this.subset ?_
  rintro z ⟨-, h2, h3, -⟩
  exact ⟨lc_mat z fun a b => lc_of_nil _ hn' _ (h2 a b), h3⟩

theorem UpperTheory.V.Pa.selmer_second_exists_ultrafilter_limit :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (U : Ultrafilter ℕ) (z : ℕ → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), TopFG G.Γ → (U : Filter ℕ) ≤ atTop → (∀ m, (fun g => (z m g).map (x.redD k.g m)) ∈ Sel2 h (x.Am m) k) → ∃ Ψ ∈ Sel2 h x.A k, ∀ j, ∀ᶠ m in (U : Filter ℕ), ∀ g, (Ψ g).map (x.redD k.g j) = (z m g).map (x.redD k.g j) := by
  intro l _ L G G0 h n x k U z hG hU hz
  have hred : ∀ j, ∀ᶠ m in (U : Filter ℕ), (fun g => (z m g).map (x.redD k.g j)) ∈ Sel2 h (x.Am j) k := by
    intro j
    refine ((eventually_ge_atTop j).filter_mono hU).mono fun m hm => ?_
    have hle : Ideal.span {x.t ^ m} ≤ Ideal.span {x.t ^ j} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hm)
    exact (sel_red l L G G0 h n x k (x.Am m) (x.Am j) (Ideal.Quotient.factorₐ x.A hle)).2.2.1 _ (hz m)
  have hst : ∀ j, ∃ m', ∀ᶠ m in (U : Filter ℕ),
      (fun g => (z m g).map (x.redD k.g j)) = fun g => (z m' g).map (x.redD k.g j) := by
    intro j
    obtain ⟨w, ⟨-, hw⟩, -⟩ := ultra_fin ℕ _ U (fun m g => (z m g).map (x.redD k.g j)) _
      (selmer_second_finite_modulo_power l L G G0 h n x k hG j) (hred j)
    obtain ⟨m', hm'⟩ := hw.exists
    exact ⟨m', hw.mono fun m hm => hm.trans hm'.symm⟩
  choose μ hμ using hst
  let Ψ : G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g) := fun g => Matrix.of fun a b =>
    ⟨PowerSeries.mk fun c => PowerSeries.coeff c (z (μ (c + 1)) g a b).a,
     fun i => PowerSeries.mk fun c => PowerSeries.coeff c ((z (μ (c + 1)) g a b).ep i),
     fun i => PowerSeries.mk fun c => PowerSeries.coeff c ((z (μ (c + 1)) g a b).ep' i),
     PowerSeries.mk fun c => PowerSeries.coeff c (z (μ (c + 1)) g a b).eta⟩
  have hΨ : ∀ j, ∀ᶠ m in (U : Filter ℕ), ∀ g, (Ψ g).map (x.redD k.g j) = (z m g).map (x.redD k.g j) := by
    intro j
    have h1 : ∀ᶠ m in (U : Filter ℕ), ∀ c ∈ Finset.range j,
        (fun g => (z m g).map (x.redD k.g (c + 1))) = fun g => (z (μ (c + 1)) g).map (x.redD k.g (c + 1)) :=
      (Filter.eventually_all_finset _).2 fun c _ => hμ (c + 1)
    refine h1.mono fun m hm g => Matrix.ext fun a b => ?_
    have h2 : ∀ c < j, x.redD k.g (c + 1) (z m g a b) = x.redD k.g (c + 1) (z (μ (c + 1)) g a b) := fun c hc =>
      congrFun (congrFun (congrFun (hm c (Finset.mem_range.2 hc)) g) a) b
    refine DD.ext ?_ (funext fun i => ?_) (funext fun i => ?_) ?_
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).a) _ j fun c hc => congrArg DD.a (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).ep i) _ j fun c hc => congrArg (DD.ep · i) (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).ep' i) _ j fun c hc => congrArg (DD.ep' · i) (h2 c hc)
    · exact diag_mk (fun c => (z (μ (c + 1)) g a b).eta) _ j fun c hc => congrArg DD.eta (h2 c hc)
  refine ⟨Ψ, selmer_second_closed_under_limits l L G G0 h n x k Ψ fun j => ?_, hΨ⟩
  obtain ⟨m, hm1, hm2⟩ := ((hΨ j).and (hred j)).exists
  rw [funext hm1]
  exact hm2
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem power_series_exists_ultrafilter_limit {K : Type} [Field K] [Finite K] (U : Ultrafilter ℕ) (c : ℕ → PowerSeries K) :
    ∃ c0 : PowerSeries K, ∀ j, ∀ᶠ m in (U : Filter ℕ), (PowerSeries.X : PowerSeries K) ^ j ∣ c m - c0 := by
  have hv : ∀ i : ℕ, ∃ v : K, {m | PowerSeries.coeff i (c m) = v} ∈ (U : Filter ℕ) := by
    intro i
    by_contra hno
    push_neg at hno
    have hall : ∀ v : K, {m | PowerSeries.coeff i (c m) = v}ᶜ ∈ U := fun v =>
      Ultrafilter.compl_mem_iff_notMem.2 (hno v)
    have hinter : (⋂ v : K, {m | PowerSeries.coeff i (c m) = v}ᶜ) ∈ (U : Filter ℕ) :=
      Filter.iInter_mem.2 hall
    obtain ⟨m, hm⟩ := Filter.nonempty_of_mem hinter
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_setOf_eq] at hm
    exact hm _ rfl
  choose v hv using hv
  refine ⟨PowerSeries.mk v, fun j => ?_⟩
  have hj : ∀ᶠ m in (U : Filter ℕ), ∀ i : Fin j, PowerSeries.coeff (i : ℕ) (c m) = v i :=
    Filter.eventually_all.2 fun i => hv i
  filter_upwards [hj] with m hm
  rw [PowerSeries.X_pow_dvd_iff]
  intro i hi
  simp [map_sub, hm ⟨i, hi⟩, PowerSeries.coeff_mk]

private theorem power_series_eq_of_dvd_all_powers {K : Type} [Field K] (a b : PowerSeries K)
    (H : ∀ j, (PowerSeries.X : PowerSeries K) ^ j ∣ a - b) : a = b := by
  rw [← sub_eq_zero]
  ext n
  have h := H (n + 1)
  rw [PowerSeries.X_pow_dvd_iff] at h
  simpa using h n (Nat.lt_succ_self n)

private theorem dual_numbers_map_surjective {A X X' : Type} [CommRing A] [CommRing X] [CommRing X'] [Algebra A X] [Algebra A X'] (g : ℕ)
    (f : X →ₐ[A] X') (hf : Function.Surjective f) : Function.Surjective (DD.map g f) := by
  intro y
  choose pre hpre using hf
  exact ⟨⟨pre y.a, fun j => pre (y.ep j), fun j => pre (y.ep' j), pre y.eta⟩,
    DD.ext (hpre _) (funext fun j => hpre _) (funext fun j => hpre _) (hpre _)⟩

theorem UpperTheory.V.Pa.secondCohomologyBound_of_boundaryBound :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x), TopFG G.Γ → SecondSelmerSpanBoundAtAllLevels h k → K2 h k := by
  intro l _ L G G0 h n x k hTop hB2 z hz
  obtain ⟨C, hC⟩ := hB2
  set q : ∀ m : ℕ, x.A →ₐ[x.A] x.Am m := fun m => Ideal.Quotient.mkₐ x.A (Ideal.span {x.t ^ m}) with hqdef
  have hsurj : ∀ m, Function.Surjective (q m) := fun m => Ideal.Quotient.mkₐ_surjective _ _
  have hqeq : ∀ m (u v : x.A), q m u = q m v ↔ (PowerSeries.X : PowerSeries x.K) ^ m ∣ u - v := by
    intro m u v
    simp only [hqdef, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton] <;> rfl
  have hzm : ∀ m i j, (fun g => (z i j g).map (q m)) ∈ SelP h x (x.Am m) :=
    fun m i j => (sel_red l L G G0 h n x k x.A (x.Am m) (q m)).1 _ (hz i j)
  choose cm hcu Ψm hΨm hΨe using fun m => hC m (fun i j g => (z i j g).map (q m)) (hzm m)
  choose Ψt hΨt using fun m (g : G.G₀) (a b : Fin n) =>
    dual_numbers_map_surjective k.g (q m) (hsurj m) (Ψm m g a b)
  set Z : ℕ → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g) :=
    fun m g => Matrix.of (fun a b => Ψt m g a b) with hZdef
  have hZ : ∀ m, (fun g => (Z m g).map (x.redD k.g m)) = Ψm m := by
    intro m
    funext g
    exact Matrix.ext fun a b => hΨt m g a b
  set U := Ultrafilter.of (atTop : Filter ℕ) with hUdef
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨Ψ, hΨ, hlim⟩ := selmer_second_exists_ultrafilter_limit l L G G0 h n x k U Z hTop hU (fun m => by rw [hZ m]; exact hΨm m)
  choose c0 hc0 using fun i : Fin (k.g + 1) => power_series_exists_ultrafilter_limit U (fun m => cm m i)
  choose idx hidx using hcu
  have hi0 : ∃ i0, ∀ᶠ m in (U : Filter ℕ), idx m = i0 := by
    by_contra hno
    push_neg at hno
    have hinter : ∀ᶠ m in (U : Filter ℕ), ∀ i, ¬ idx m = i :=
      Filter.eventually_all.2 fun i => by simpa using hno i
    obtain ⟨m, hm⟩ := hinter.exists
    exact hm _ rfl
  obtain ⟨i0, hi0⟩ := hi0
  refine ⟨fun i => x.t ^ C * c0 i, ?_, Ψ, hΨ, ?_⟩
  · intro h0
    have h1 : x.t ^ C * c0 i0 = 0 := congrFun h0 i0
    have hc00 : c0 i0 = 0 := by
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 (pow_ne_zero _ PowerSeries.X_ne_zero)
      · exact h2
    obtain ⟨m, hm1, hm2⟩ := (hi0.and (hc0 i0 1)).exists
    have hu := hidx m
    rw [hm1] at hu
    have h3 : (PowerSeries.X : PowerSeries x.K) ∣ cm m i0 := by
      simpa [hc00] using hm2
    have h7 := isUnit_of_dvd_unit h3 hu
    simp [PowerSeries.isUnit_iff_constantCoeff] at h7
  · intro j γ a b
    apply power_series_eq_of_dvd_all_powers
    intro J
    obtain ⟨m, hm1, hm2, hm3⟩ := ((hlim J).and ((Filter.eventually_all.2 fun i => hc0 i J).and
      ((Filter.eventually_ge_atTop J).filter_mono hU))).exists
    have d1 : (PowerSeries.X : PowerSeries x.K) ^ J ∣ (Ψ γ a b).ep' j - (Ψt m γ a b).ep' j := by
      have e := congrArg (fun M => (M a b).ep' j) (hm1 γ)
      exact (hqeq J ((Ψ γ a b).ep' j) ((Ψt m γ a b).ep' j)).1 e
    have d2 : (PowerSeries.X : PowerSeries x.K) ^ J ∣
        (Ψt m γ a b).ep' j - x.t ^ C * ∑ i, cm m i * z i j γ a b := by
      have e := hΨe m j γ a b
      rw [← hΨt m γ a b] at e
      have e2 : q m ((Ψt m γ a b).ep' j) = q m (x.t ^ C * ∑ i, cm m i * z i j γ a b) := by
        rw [show q m ((Ψt m γ a b).ep' j) = (DD.map k.g (q m) (Ψt m γ a b)).ep' j from rfl, e]
        simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.map_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sum]
        simp only [map_mul]
        rw [Algebra.smul_def, ← (q m).commutes, Algebra.algebraMap_self, RingHom.id_apply]
        congr 1
      exact (pow_dvd_pow _ hm3).trans ((hqeq m _ _).1 e2)
    have d3 : (PowerSeries.X : PowerSeries x.K) ^ J ∣
        x.t ^ C * ∑ i, cm m i * z i j γ a b - (∑ i, (x.t ^ C * c0 i) • z i j γ) a b := by
      have e : x.t ^ C * ∑ i, cm m i * z i j γ a b - (∑ i, (x.t ^ C * c0 i) • z i j γ) a b =
          x.t ^ C * ∑ i, (cm m i - c0 i) * z i j γ a b := by
        simp [Matrix.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib, sub_mul, mul_sub, mul_assoc]
      rw [e]
      exact Dvd.dvd.mul_left (Finset.dvd_sum fun i _ => Dvd.dvd.mul_right (hm2 i) _) _
    have := dvd_add (dvd_add d1 d2) d3
    simpa using this
