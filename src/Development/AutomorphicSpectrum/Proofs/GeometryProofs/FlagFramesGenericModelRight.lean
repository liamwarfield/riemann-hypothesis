module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PieceLocalizationAtElement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsChartBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatricesRegularGeneric

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedFrameInChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedFrameInChart
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace ChartFrame

theorem locSub_le_of_mul {F : Type} [Field F] {R : Subring F} {a b : F} (ha : a ∈ R) (hb : b ∈ R)
    (h0 : a * b ≠ 0) : locSub R a ≤ locSub R (a * b) := by
  have hb0 : b ≠ 0 := right_ne_zero_of_mul h0
  unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.locSub
  rw [Subring.closure_le]
  rintro y (hy | hy)
  · exact Subring.subset_closure (Set.mem_union_left _ hy)
  · rw [Set.mem_singleton_iff] at hy
    rw [hy, show a⁻¹ = b * (a * b)⁻¹ by rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hb0, mul_one]]
    exact mul_mem (Subring.subset_closure (Set.mem_union_left _ hb))
      (Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton _)))

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem unitAt_mul' {p : Cpt ξ} {f g : Ω} (hf : unitAt ξ p f) (hg : unitAt ξ p g) :
    unitAt ξ p (f * g) := by
  unfold GlobalTheory.CompanionTheory.Ar.unitAt at hf hg ⊢
  obtain ⟨hf0, hf1, hf2⟩ := hf
  obtain ⟨hg0, hg1, hg2⟩ := hg
  refine ⟨mul_ne_zero hf0 hg0, mul_mem hf1 hg1, ?_⟩
  rw [mul_inv]
  exact mul_mem hf2 hg2

theorem unitAt_prod' {p : Cpt ξ} {ι : Type} (s : Finset ι) (f : ι → Ω) (h : ∀ i ∈ s, unitAt ξ p (f i)) :
    unitAt ξ p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    unfold GlobalTheory.CompanionTheory.Ar.unitAt
    refine ⟨one_ne_zero, one_mem _, ?_⟩
    rw [inv_one]
    exact one_mem _
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact unitAt_mul' (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem exists_dual_family {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} {β : Fin r → E}
    (hβ : LinearIndependent Ω β) :
    ∃ w : Fin r → Module.Dual Ω E, ∀ l l', w l (β l') = (1 : Matrix (Fin r) (Fin r) Ω) l l' := by
  classical
  have hext : ∀ l : Fin r, ∃ g : Module.Dual Ω E,
      g.comp (Submodule.span Ω (Set.range β)).subtype = (Module.Basis.span hβ).coord l :=
    fun l => LinearMap.exists_extend ((Module.Basis.span hβ).coord l)
  choose w hw using hext
  refine ⟨w, fun l l' => ?_⟩
  have h1 : w l (β l') = (Module.Basis.span hβ).coord l (Module.Basis.span hβ l') := by
    rw [← hw l, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
  rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  rcases eq_or_ne l l' with rfl | hne
  · simp
  · simp [hne, hne.symm]

end ChartFrame


open ChartFrame ChartTie in
theorem exists_chart_frame : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (r : ℕ) (V : Submodule Ω E) (L : Lat ξ E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (c : κ) (p : Cpt ξ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → IsTwistGen ξ x L m φ → (LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = V) → InChart ξ x c p → ∃ g ∈ chartSub x c, unitAt ξ p g ∧ ∃ (T : Matrix (Fin r) (Fin r) Ω) (M : Matrix (Fin n) (Fin r) Ω) (N : Matrix (Fin r) (Fin n) Ω), T.det ≠ 0 ∧ (∀ j l, M j l ∈ locSub (chartSub x c) g) ∧ (∀ l j, N l j ∈ locSub (chartSub x c) g) ∧ N * M = 1 ∧ ∀ j l, φ j (b l) = x c ^ m * (M * T) j l := by
  intro X Ω _ ξ E _ _ κ x r V L m n φ b c p hCT _hgen hVB hTw hb hIn
  classical
  obtain ⟨hbli, hbV⟩ := hb
  have hx0 : x c ≠ 0 := by
    unfold GlobalTheory.CompanionTheory.Ar.InChart at hIn
    exact hIn.1
  have hxm : x c ^ m ≠ 0 := pow_ne_zero m hx0
  unfold GlobalTheory.CompanionTheory.Ar.FlagBun.IsTwistGen at hTw
  obtain ⟨hTw1, hTw2⟩ := hTw
  unfold GlobalTheory.CompanionTheory.Ar.Lat.IsVB GlobalTheory.CompanionTheory.Ar.Lat.IsVBOn at hVB
  obtain ⟨U, hpU, b', hb'V, hfr⟩ := hVB p (Set.mem_univ p)
  have hF := hfr p (Set.mem_univ p) hpU
  unfold GlobalTheory.CompanionTheory.Ar.Lat.IsFrameAt at hF
  obtain ⟨hb'li, hLp⟩ := hF
  obtain ⟨w, hw⟩ := exists_dual_family hb'li
  have hcoord : ∀ e ∈ Submodule.span Ω (Set.range b'), e = ∑ k, w k e • b' k := by
    intro e he
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 he
    have hwc : ∀ k, w k (∑ i, cf i • b' i) = cf k := by
      intro k
      simp [hw, Matrix.one_apply]
    exact (Finset.sum_congr rfl fun k _ => by rw [hwc k]).symm
  have hbexp : ∀ l, b l = ∑ k, w k (b l) • b' k := fun l =>
    hcoord _ (by rw [hb'V, ← hbV]; exact Submodule.subset_span ⟨l, rfl⟩)
  have hdet : (Matrix.of fun k l => w k (b l)).det ≠ 0 := by
    intro hdet0
    obtain ⟨v, hv0, hTv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet0
    apply hv0
    have hsum : ∑ l, v l • b l = 0 := by
      calc ∑ l, v l • b l = ∑ l, v l • ∑ k, w k (b l) • b' k :=
            Finset.sum_congr rfl fun l _ => by rw [← hbexp l]
        _ = ∑ l, ∑ k, (v l * w k (b l)) • b' k := by simp only [Finset.smul_sum, smul_smul]
        _ = ∑ k, ∑ l, (v l * w k (b l)) • b' k := Finset.sum_comm
        _ = ∑ k, (Matrix.mulVec (Matrix.of fun k l => w k (b l)) v) k • b' k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Finset.sum_smul]
            congr 1
            simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
            exact Finset.sum_congr rfl fun l _ => mul_comm _ _
        _ = 0 := by simp [hTv]
    exact funext (Fintype.linearIndependent_iff.1 hbli v hsum)
  have hb'Lp : ∀ k, b' k ∈ L p := fun k => by
    rw [hLp]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hMreg : ∀ j k, φ j (b' k) / x c ^ m ∈ regAt ξ p := fun j k =>
    hTw1 j p c hIn (b' k) (hb'Lp k)
  have hwreg : ∀ l, ∀ e ∈ L p, w l e ∈ regAt ξ p := by
    intro l e he
    rw [hLp] at he
    obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [Subring.smul_def, map_smul, hw, smul_eq_mul]
    refine mul_mem (cf i).2 ?_
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hN : ∀ l, ∃ gv : Fin n → Ω, (∀ j, gv j ∈ regAt ξ p) ∧
      ∀ e ∈ L p, w l e = ∑ j, gv j * (φ j e / x c ^ m) := fun l =>
    hTw2 p c hIn (w l) (hwreg l)
  choose gv hgvreg hgv using hN
  have hNM : (Matrix.of fun l j => gv l j) * (Matrix.of fun j k => φ j (b' k) / x c ^ m) = 1 := by
    ext l l'
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [← hgv l (b' l') (hb'Lp l'), hw]
  have hreg : ∀ a ∈ regAt ξ p, ∃ s ∈ chartSub x c, unitAt ξ p s ∧ a ∈ locSub (chartSub x c) s := by
    intro a ha
    obtain ⟨s, hs, hsu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hCT c p hIn a).1 ha
    have hs0 : s ≠ 0 := by
      unfold GlobalTheory.CompanionTheory.Ar.unitAt at hsu
      exact hsu.1
    refine ⟨s, by unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartSub; exact hs, hsu, ?_⟩
    unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.locSub
    rw [show a = s * a * s⁻¹ by rw [mul_comm s a, mul_assoc, mul_inv_cancel₀ hs0, mul_one]]
    exact mul_mem
      (Subring.subset_closure (Set.mem_union_left _ (by unfold GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartSub; exact hsa)))
      (Subring.subset_closure (Set.mem_union_right _ (Set.mem_singleton _)))
  have hent : ∀ i : (Fin n × Fin r) ⊕ (Fin r × Fin n),
      Sum.elim (fun jk => φ jk.1 (b' jk.2) / x c ^ m) (fun lj => gv lj.1 lj.2) i ∈ regAt ξ p := by
    rintro (⟨j, k⟩ | ⟨l, j⟩)
    · exact hMreg j k
    · exact hgvreg l j
  choose s hsR hsU hsloc using fun i => hreg _ (hent i)
  have hgU : unitAt ξ p (∏ i, s i) := unitAt_prod' _ _ fun i _ => hsU i
  have hgR : (∏ i, s i) ∈ chartSub x c := prod_mem fun i _ => hsR i
  have hg0 : (∏ i, s i) ≠ 0 := by
    have h := hgU
    unfold GlobalTheory.CompanionTheory.Ar.unitAt at h
    exact h.1
  have hmono : ∀ i, locSub (chartSub x c) (s i) ≤ locSub (chartSub x c) (∏ i, s i) := by
    intro i
    have hsplit := Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)
    rw [← hsplit]
    exact locSub_le_of_mul (hsR i) (prod_mem fun j _ => hsR j) (by rw [hsplit]; exact hg0)
  refine ⟨∏ i, s i, hgR, hgU, Matrix.of fun k l => w k (b l),
    Matrix.of fun j k => φ j (b' k) / x c ^ m, Matrix.of fun l j => gv l j, hdet, ?_, ?_, hNM, ?_⟩
  · intro j k
    simp only [Matrix.of_apply]
    exact hmono _ (hsloc (Sum.inl (j, k)))
  · intro l j
    simp only [Matrix.of_apply]
    exact hmono _ (hsloc (Sum.inr (l, j)))
  · intro j l
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    conv_lhs => rw [hbexp l]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul]
    first
      | (rw [div_mul_eq_mul_div, mul_div_assoc', mul_comm (x c ^ m), mul_div_assoc, div_self hxm,
          mul_one, mul_comm])
      | (field_simp; ring)
      | field_simp

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistedFrameInChartStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_frame_in_chart : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (r : ℕ) (V : Submodule Ω E) (L : Lat ξ E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (b : Fin r → E) (c : κ) (p : Cpt ξ), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → L.IsVB r V → IsTwistGen ξ x L m φ → (LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = V) → InChart ξ x c p → ∃ g ∈ chartSub x c, unitAt ξ p g ∧ ∃ (T : Matrix (Fin r) (Fin r) Ω) (M : Matrix (Fin n) (Fin r) Ω) (N : Matrix (Fin r) (Fin n) Ω), T.det ≠ 0 ∧ (∀ j l, M j l ∈ locSub (chartSub x c) g) ∧ (∀ l j, N l j ∈ locSub (chartSub x c) g) ∧ N * M = 1 ∧ ∀ j l, φ j (b l) = x c ^ m * (M * T) j l := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_chart_frame | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_chart_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.exists_chart_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegular
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem chartSub_div_mem {F : Type} [Field F] {κ : Type} (x : κ → F) (c j : κ) :
    x j / x c ∈ chartSub x c :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem chartSub_le_of_forall {F : Type} [Field F] {κ : Type} {x : κ → F} {c : κ} {T : Subring F}
    (h : ∀ j, x j / x c ∈ T) : chartSub x c ≤ T := by
  intro a ha
  have ha' : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := ha
  induction ha' using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    exact h j
  | algebraMap n => simpa using intCast_mem T n
  | add b d _ _ hb hd => exact T.add_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))
  | mul b d _ _ hb hd => exact T.mul_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))

theorem locSub_le_of {F : Type} [Field F] {R T : Subring F} {a : F} (h : R ≤ T) (ha : a⁻¹ ∈ T) :
    locSub R a ≤ T :=
  Subring.closure_le.2 (Set.union_subset h (Set.singleton_subset_iff.2 ha))

theorem flagCoord_div_eq {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type}
    (x : κ → Ω) {S : Type} [Fintype S] {r n m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω}
    {c₀ : κ} (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (hx : x c₀ ≠ 0)
    (h : ∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) (k : κ)
    (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc ((k, J') : FlagIx κ n r) / flagCoord κ x φ cc ((c₀, J) : FlagIx κ n r) =
      algebraMap Ω (GenField Ω r) (x k / x c₀) *
        ∏ q : (Σ s, Fin (r s)), stepMinor (flagB M T q.1) q.2 (J' q) / stepMinor (flagB M T q.1) q.2 (J q) := by
  have hi : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := (map_ne_zero _).2 hx
  rw [flagCoord_eq x h k J', flagCoord_eq x h c₀ J, map_div₀, mul_div_mul_comm,
    ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  exact mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hi))

theorem chartRing_eq_ratioRing : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type)
    (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω)
    (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 →
    g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) →
    (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) →
    algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧
    locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) =
      ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  intro Ω _ E _ _ κ x S _ r n m φ cc M T c₀ J g hx hg hg0 h hJ
  classical
  set A := chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) with hA
  have hdiv := fun k J' => flagCoord_div_eq (m := m) x J hx h k J'

  have h1 : ∀ k, algebraMap Ω (GenField Ω r) (x k / x c₀) ∈ A := by
    intro k
    have e := hdiv k J
    have e1 : ∏ q : (Σ s, Fin (r s)),
        stepMinor (flagB M T q.1) q.2 (J q) / stepMinor (flagB M T q.1) q.2 (J q) = 1 :=
      Finset.prod_eq_one fun q _ => div_self (hJ q)
    rw [e1, _root_.mul_one] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ((k, J) : FlagIx κ n r)

  have h2 : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A := by
    intro q J'
    have e := hdiv c₀ (Function.update J q J')
    rw [div_self hx, map_one, _root_.one_mul, Finset.prod_div_distrib,
      prod_update_div (β := fun q : (Σ s, Fin (r s)) => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => stepMinor (flagB M T q.1) q.2 b) J hJ q J'] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)
      ((c₀, Function.update J q J') : FlagIx κ n r)
  have himg : chartSub x c₀ ≤ A.comap (algebraMap Ω (GenField Ω r)) :=
    chartSub_le_of_forall fun j => h1 j
  have hgA : algebraMap Ω (GenField Ω r) g ∈ A := himg hg
  refine ⟨hgA, le_antisymm ?_ ?_⟩
  ·
    set R' := locSub (chartSub x c₀) g with hR'
    have him : ∀ b ∈ R', algebraMap Ω (GenField Ω r) b ∈ ratioRing R' (flagB M T) J := fun b hb =>
      Subring.subset_closure (Or.inl ⟨b, hb, rfl⟩)
    refine locSub_le_of (chartSub_le_of_forall ?_) ?_
    · rintro ⟨k, J'⟩
      rw [hdiv k J']
      refine Subring.mul_mem _ (him _ (le_locSub _ _ (chartSub_div_mem x c₀ k))) ?_
      exact Subring.prod_mem _ fun q _ => Subring.subset_closure (Or.inr ⟨q, J' q, rfl⟩)
    · rw [← map_inv₀]
      exact him _ (inv_mem_locSub _ _)
  · refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨b, hb, rfl⟩
      have hle : locSub (chartSub x c₀) g ≤
          (locSub A (algebraMap Ω (GenField Ω r) g)).comap (algebraMap Ω (GenField Ω r)) := by
        refine locSub_le_of (himg.trans fun a ha => le_locSub _ _ ha) ?_
        show algebraMap Ω (GenField Ω r) g⁻¹ ∈ locSub A (algebraMap Ω (GenField Ω r) g)
        rw [map_inv₀]
        exact inv_mem_locSub _ _
      exact hle hb
    · rintro _ ⟨q, J', rfl⟩
      exact le_locSub _ _ (h2 q J')

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegularStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_frame_matrix_regular : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 → g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧ locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) = ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmooth
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmooth
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem val_appLE_of_dominates {X X' : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω']
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X} {i : Ω →+* Ω'}
    (hd : Dominates ξ' ξ f i) {U : X.Opens} {W : X'.Opens} (e : W ≤ f ⁻¹ᵁ U) (hW : genPt ξ' ∈ W)
    (hU : genPt ξ ∈ U) (t : Γ(X, U)) :
    (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) =
      i ((X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t) := by
  have hfq : f (genPt ξ') ∈ U := e hW
  have hp : genPt ξ ⤳ f (genPt ξ') := by rw [RegAtDom.map_genPt hd]
  have h := RegAtDom.genMap_stalkMap hd (genPt ξ') specializes_rfl hp
    ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t)
  have l1 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ f.stalkMap (genPt ξ') =
      f.appLE U W e ≫ X'.presheaf.germ W (genPt ξ') hW := by
    rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have l2 : X'.presheaf.germ W (genPt ξ') hW ≫ X'.presheaf.stalkSpecializes specializes_rfl =
      X'.presheaf.germ W (genPt ξ') hW := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have l3 : X.presheaf.germ U (f (genPt ξ')) hfq ≫ X.presheaf.stalkSpecializes hp =
      X.presheaf.germ U (genPt ξ) hU := TopCat.Presheaf.germ_stalkSpecializes _ _ _
  have a1 : (f.stalkMap (genPt ξ')).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t) :=
    congrArg (fun g => g.hom t) l1
  have a2 : ∀ s, (X'.presheaf.stalkSpecializes specializes_rfl).hom
      ((X'.presheaf.germ W (genPt ξ') hW).hom s) = (X'.presheaf.germ W (genPt ξ') hW).hom s :=
    fun s => congrArg (fun g => g.hom s) l2
  have a3 : (X.presheaf.stalkSpecializes hp).hom ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU).hom t := congrArg (fun g => g.hom t) l3
  rw [a1] at h
  have b1 : genMap ξ' ⟨genPt ξ', specializes_rfl⟩ ((X'.presheaf.germ W (genPt ξ') hW).hom ((f.appLE U W e).hom t)) =
      (X'.presheaf.germ W (genPt ξ') hW ≫ Scheme.stalkClosedPointTo ξ').hom ((f.appLE U W e).hom t) := by
    exact congrArg (Scheme.stalkClosedPointTo ξ').hom (a2 _)
  have b2 : genMap ξ ⟨f (genPt ξ'), hp⟩ ((X.presheaf.germ U (f (genPt ξ')) hfq).hom t) =
      (X.presheaf.germ U (genPt ξ) hU ≫ Scheme.stalkClosedPointTo ξ).hom t := by
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom a3
  rw [← b1, h, b2]

theorem smooth_of_pieces : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω']
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'),
    IsCptGen ξ → IsCptGen ξ' → Dominates ξ' ξ f i →
    (∀ p' : X', ∃ (U : X.Opens) (W : X'.Opens) (R : Subring Ω) (C : Subring Ω') (h : ∀ a ∈ R, i a ∈ C),
      IsPiece ξ U R ∧ IsPiece ξ' W C ∧ W ≤ f ⁻¹ᵁ U ∧ p' ∈ W ∧
      ((i.comp R.subtype).codRestrict C (fun a => h a a.2)).Smooth) → Smooth f := by
  intro X X' Ω Ω' _ _ ξ ξ' f i hg hg' hd h
  refine (HasRingHomProperty.iff_exists_appLE (P := @Smooth) (Q := RingHom.Smooth)
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1).2 fun p' => ?_
  obtain ⟨U, W, R, C, hRC, hU, hW, e, hp, hs⟩ := h p'
  refine ⟨⟨U, hU.affine⟩, ⟨W, hW.affine⟩, hp, e, ?_⟩
  have hWg : genPt ξ' ∈ W := (hW.spec p' hp).mem_open W.isOpen hp
  have hUg : genPt ξ ∈ U := by
    have h1 : f (genPt ξ') ∈ U := e hWg
    rwa [RegAtDom.map_genPt hd] at h1
  obtain ⟨injU, ranU⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X Ω ξ hg U hUg hU.spec
  obtain ⟨injW, ranW⟩ := GlobalTheory.T.germ_genPt_injective_range_regAt X' Ω' ξ' hg' W hWg hW.spec
  have memR : ∀ t, (X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom t ∈ R :=
    fun t => (hU.ring _).2 ((ranU _).1 ⟨t, rfl⟩)
  have memC : ∀ t, (X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom t ∈ C :=
    fun t => (hW.ring _).2 ((ranW _).1 ⟨t, rfl⟩)
  let eU : Γ(X, U) ≃+* R := RingEquiv.ofBijective
    ((X.presheaf.germ U (genPt ξ) hUg ≫ Scheme.stalkClosedPointTo ξ).hom.codRestrict R memR)
    ⟨fun a b hab => injU (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranU r.1).2 ((hU.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  let eW : Γ(X', W) ≃+* C := RingEquiv.ofBijective
    ((X'.presheaf.germ W (genPt ξ') hWg ≫ Scheme.stalkClosedPointTo ξ').hom.codRestrict C memC)
    ⟨fun a b hab => injW (congrArg Subtype.val hab), fun r => by
      obtain ⟨t, ht⟩ := (ranW r.1).2 ((hW.ring r.1).1 r.2)
      exact ⟨t, Subtype.ext ht⟩⟩
  have hval : ∀ t, eW ((f.appLE U W e).hom t) =
      ((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)) (eU t) :=
    fun t => Subtype.ext (val_appLE_of_dominates hd e hWg hUg t)
  have key : (f.appLE U W e).hom = (eW.symm : C →+* Γ(X', W)).comp
      (((i.comp R.subtype).codRestrict C (fun a => hRC a a.2)).comp (eU : Γ(X, U) →+* R)) :=
    RingHom.ext fun t => (eW.symm_apply_eq.2 (hval t).symm).symm
  show RingHom.Smooth (f.appLE U W e).hom
  rw [key]
  exact RingHom.Smooth.comp (RingHom.Smooth.comp (RingHom.Smooth.of_bijective eU.bijective) hs)
    (RingHom.Smooth.of_bijective eW.symm.bijective)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingPiecesSmoothStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominating_pieces_smooth : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω'), IsCptGen ξ → IsCptGen ξ' → Dominates ξ' ξ f i → (∀ p' : X', ∃ (U : X.Opens) (W : X'.Opens) (R : Subring Ω) (C : Subring Ω') (h : ∀ a ∈ R, i a ∈ C), IsPiece ξ U R ∧ IsPiece ξ' W C ∧ W ≤ f ⁻¹ᵁ U ∧ p' ∈ W ∧ ((i.comp R.subtype).codRestrict C (fun a => h a a.2)).Smooth) → Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.smooth_of_pieces <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelRight
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem isPiece_chart {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}
    (hT : CoordTie ℤ ξ x) {c : κ} (hc : x c ≠ 0) :
    ∃ U : X.Opens, IsPiece ξ U (chartSub x c) ∧ ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := by
  obtain ⟨U, hU, hm⟩ := hT.affine c hc
  have hq : ∀ q : Cpt ξ, q.1 ∈ U ↔ InChart ξ x c q := fun q =>
    ⟨fun h => ((hm q.1).1 h).2, fun h => (hm q.1).2 ⟨q.2, h⟩⟩
  refine ⟨U, ⟨hU, fun q h => ((hm q).1 h).1, fun a => ?_⟩, hq⟩
  refine (hT.ring c hc a).trans (forall_congr' fun q => imp_congr (hq q).symm Iff.rfl)

theorem coordTie_int_inst {X : Scheme.{0}} {F : Type} [Field F] {ξ : Spec (CommRingCat.of F) ⟶ X} {κ : Type} {x : κ → F}
    (inst : Algebra ℤ F) (h : @CoordTie X F _ ℤ _ inst ξ κ x) : @CoordTie X F _ ℤ _ (Ring.toIntAlgebra F) ξ κ x := by
  rwa [Subsingleton.elim inst (Ring.toIntAlgebra F)] at h

theorem locSub_le_of_mul {F : Type} [Field F] {R : Subring F} {a b g : F} (hb : b ∈ R) (h : a * b = g) (hg : g ≠ 0) :
    locSub R a ≤ locSub R g := by
  refine (Subring.closure_le).2 (Set.union_subset (fun y hy => le_locSub R g hy) ?_)
  rintro _ rfl
  have ha : a ≠ 0 := left_ne_zero_of_mul (h ▸ hg)
  have hb0 : b ≠ 0 := right_ne_zero_of_mul (h ▸ hg)
  have e : a⁻¹ = b * g⁻¹ := by rw [← h]; field_simp
  rw [SetLike.mem_coe, e]
  exact (locSub R g).mul_mem (le_locSub R g hb) (inv_mem_locSub R g)

theorem flag_smooth : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → Smooth f := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hT hall hVB hTw hc hT' hall' hdom hch
  classical
  have hi : Function.Injective (algebraMap Ω (GenField Ω r)) := (algebraMap Ω (GenField Ω r)).injective
  refine GlobalTheory.T.dominating_pieces_smooth X X' Ω (GenField Ω r) ξ ξ' f (algebraMap Ω (GenField Ω r)) hT.gen hT'.gen hdom (fun p' => ?_)
  let P' : Cpt ξ' := ⟨p', hall' p'⟩
  obtain ⟨⟨c₀, J⟩, hcJ⟩ := hT'.cover P'
  have hy0 : flagCoord κ x φ c (c₀, J) ≠ 0 := hcJ.1
  have hx0 : x c₀ ≠ 0 := by
    intro h0
    apply hy0
    simp [flagCoord, h0]

  have hover : ∀ Q' : Cpt ξ', InChart ξ' (flagCoord κ x φ c) ((c₀, J) : FlagIx κ n r) Q' →
      InChart ξ x c₀ ⟨f Q'.1, hall _⟩ := by
    intro Q' hQ
    refine (hch Q' c₀ (hall _)).2 ⟨by simpa using hx0, fun k => ?_⟩
    have h := hQ.2 ((k, J) : FlagIx κ n r)
    have hpr : (∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det) ≠ 0 := by
      intro h0
      apply hy0
      simp [flagCoord, h0]
    have e : flagCoord κ x φ c ((k, J) : FlagIx κ n r) / flagCoord κ x φ c ((c₀, J) : FlagIx κ n r) =
        algebraMap Ω (GenField Ω r) (x k) / algebraMap Ω (GenField Ω r) (x c₀) := by
      simp only [flagCoord]
      have : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
      field_simp
    rwa [e] at h
  let P : Cpt ξ := ⟨f p', hall _⟩
  have h2 : InChart ξ x c₀ P := hover P' hcJ
  have hfr := fun s => GlobalTheory.T.twisted_frame_in_chart X Ω ξ E κ x (r s) (V s) (L s) (m s) (n s) (φ s) (c s) c₀ P hT hall (hVB s) (hTw s) (hc s) h2
  choose g hgR hgu T M N hT0 hM hN hNM hφ using hfr
  let g₀ : Ω := ∏ s, g s
  have hg₀R : g₀ ∈ chartSub x c₀ := Subring.prod_mem _ fun s _ => hgR s
  have hg₀0 : g₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (hgu s).1
  have hreg : ∀ a ∈ chartSub x c₀, ∀ Q : Cpt ξ, InChart ξ x c₀ Q → a ∈ regAt ξ Q := fun a ha Q hQ =>
    (hT.ring c₀ hx0 a).1 ha Q hQ
  have hg₀inv : g₀⁻¹ ∈ regAt ξ P := by
    have : g₀⁻¹ = ∏ s, (g s)⁻¹ := by simp [g₀]
    rw [this]
    exact Subring.prod_mem _ fun s _ => (hgu s).2.2
  have hg₀u : unitAt ξ P g₀ := ⟨hg₀0, hreg _ hg₀R P h2, hg₀inv⟩
  let R : Subring Ω := locSub (chartSub x c₀) g₀
  have hle : ∀ s, locSub (chartSub x c₀) (g s) ≤ R := fun s =>
    locSub_le_of_mul (b := ∏ s' ∈ Finset.univ.erase s, g s')
      (Subring.prod_mem _ fun s' _ => hgR s') (Finset.mul_prod_erase Finset.univ g (Finset.mem_univ s)) hg₀0
  have hRP : ∀ a ∈ R, a ∈ regAt ξ P := by
    have : R ≤ regAt ξ P := (Subring.closure_le).2 (Set.union_subset (fun y hy => hreg y hy P h2)
      (by rintro _ rfl; exact hg₀inv))
    exact this
  obtain ⟨hPh, hdom1, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom P'
  have hRO : ∀ a ∈ R, algebraMap Ω (GenField Ω r) a ∈ regAt ξ' P' := fun a ha => hdom1 a (hRP a ha)
  haveI : IsLocalRing (regAt ξ' P') := (regAt_isLocalRing_isFractionRing_stalk X' _ ξ' hT'.gen P').1
  have hscale : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), _ :=
    fun k J' => flagCoord_eq (m := m) x hφ k J'
  have hax : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := by simpa using hx0
  have hprod0 := hscale c₀ J
  have hβ0 : ∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0 := by
    intro q h0
    apply hy0
    rw [hprod0, Finset.prod_eq_zero (Finset.mem_univ q) (by rw [h0, mul_zero]), mul_zero]
  have hβJ : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ regAt ξ' P' := by
    intro q J'
    have h := hcJ.2 ((c₀, Function.update J q J') : FlagIx κ n r)
    rw [hscale c₀ (Function.update J q J'), hprod0, mul_div_mul_left _ _ hax,
      prod_update_div (β := fun q => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => (algebraMap Ω (GenField Ω r) (x c₀) ^ m q.1) ^ ((q.2 : ℕ) + 1) * stepMinor (flagB M T q.1) q.2 b) J
        (fun q => mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hax)) (hβ0 q)) q J',
      mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hax))] at h
    exact h
  obtain ⟨t, htR, ht0, htO, htiO, hmap, hsm⟩ := GlobalTheory.T.frame_matrices_regular_generic Ω S r n R (regAt ξ' P') T M N J hRO hT0
    (fun s j l => hle s (hM s j l)) (fun s l j => hle s (hN s l j)) hNM hβ0 hβJ
  obtain ⟨hgA, hAeq⟩ := GlobalTheory.T.chart_frame_matrix_regular Ω E κ x S r n m φ c M T c₀ J g₀ hx0 hg₀R hg₀0 hφ hβ0
  obtain ⟨U₀, hU₀, hU₀m⟩ := isPiece_chart hT hx0
  obtain ⟨U₁, hU₁, hU₁m⟩ := GlobalTheory.T.piece_localization_at_element X Ω ξ U₀ _ g₀ hT.gen hU₀ hg₀R hg₀0
  obtain ⟨W₀, hW₀, hW₀m⟩ := isPiece_chart (coordTie_int_inst _ hT') hy0
  have hig0 : algebraMap Ω (GenField Ω r) g₀ ≠ 0 := by simpa using hg₀0
  obtain ⟨W₁, hW₁, hW₁m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₀ _ _ hT'.gen hW₀ hgA hig0
  rw [hAeq] at hW₁
  obtain ⟨W₂, hW₂, hW₂m⟩ := GlobalTheory.T.piece_localization_at_element X' _ ξ' W₁ _ t hT'.gen hW₁ htR ht0
  refine ⟨U₁, W₂, R, _, hmap, hU₁, hW₂, ?_, ?_, hsm⟩
  · intro q' hq'
    let Q' : Cpt ξ' := ⟨q', hall' q'⟩
    have e1 := ((hW₂m Q').1 hq').1
    obtain ⟨e2, e3⟩ := (hW₁m Q').1 e1
    have e4 := (hW₀m Q').1 e2
    have e5 := hover Q' e4
    obtain ⟨h', -, hun⟩ := RegAtDom.regAt_dominates X Ω ξ X' (GenField Ω r) ξ' f _ hdom Q'
    exact (hU₁m ⟨f q', hall _⟩).2 ⟨(hU₀m _).2 e5, hun hT'.gen g₀ (hreg _ hg₀R _ e5) e3⟩
  · refine (hW₂m P').2 ⟨(hW₁m P').2 ⟨(hW₀m P').2 hcJ, hig0, hRO _ (le_locSub _ _ hg₀R), ?_⟩, ht0, htO, htiO⟩
    rw [← map_inv₀]
    exact hRO _ (inv_mem_locSub _ _)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagFramesGenericModelRightStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frames_generic_model_right : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.flag_smooth | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.flag_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.flag_smooth <;> assumption)
end
