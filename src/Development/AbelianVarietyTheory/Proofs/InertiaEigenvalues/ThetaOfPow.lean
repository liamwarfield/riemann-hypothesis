module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ForallFieldIffForallSubgroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaOfPow
open Polynomial

namespace GlobalTheory.GLq.LabelModel
theorem lift {F : Type} [Field F] {m M : ℕ} (hM : 0 < M) (hm : m ∣ M) {ξ ζ : F} (hξ : IsPrimitiveRoot ξ M)
    (hζ : IsPrimitiveRoot ζ m) : ∃ ξ' : F, IsPrimitiveRoot ξ' M ∧ ξ' ^ (M / m) = ζ := by
  obtain ⟨c, rfl⟩ := hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_right hM
  haveI : NeZero m := ⟨hm0.ne'⟩
  haveI : NeZero (m * c) := ⟨hM.ne'⟩
  have hη : IsPrimitiveRoot (ξ ^ c) m := hξ.pow hM (mul_comm _ _)
  obtain ⟨a, -, hac, ha⟩ := (hη.isPrimitiveRoot_iff).1 hζ
  obtain ⟨U, hU⟩ := ZMod.unitsMap_surjective (n := m) (m := m * c) (Dvd.intro _ rfl) (ZMod.unitOfCoprime a hac)
  refine ⟨ξ ^ (U : ZMod (m * c)).val, hξ.pow_of_coprime _ (ZMod.val_coe_unit_coprime U), ?_⟩
  rw [Nat.mul_div_cancel_left _ hm0, ← pow_mul, mul_comm, pow_mul, ← ha]
  have h1 : (((U : ZMod (m * c)).val : ℕ) : ZMod m) = (a : ZMod m) := by
    have := congrArg (fun u : (ZMod m)ˣ => (u : ZMod m)) hU
    simpa [ZMod.unitsMap_val] using this
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).1 h1
  rw [pow_eq_pow_mod _ hη.pow_eq_one, pow_eq_pow_mod a hη.pow_eq_one, h2]

variable (g : ℕ) [hg : Fact g.Prime]

theorem pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 :=
  Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)

theorem dv {d e : ℕ} (h : d ∣ e) : g ^ d - 1 ∣ g ^ e - 1 := Nat.pow_sub_one_dvd_pow_sub_one g h

theorem exprim {d : ℕ} (hd : 0 < d) : ∃ ξ : Formalism.CyclotomicNorms.Fbar g, IsPrimitiveRoot ξ (g ^ d - 1) := by
  haveI : NeZero (((g ^ d - 1 : ℕ)) : Formalism.CyclotomicNorms.Fbar g) := ⟨by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ hg.out.pos), Nat.cast_pow, CharP.cast_eq_zero (Formalism.CyclotomicNorms.Fbar g) g, zero_pow hd.ne']
    simp⟩
  haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot _ _

theorem chain : ∃ z : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ n, IsPrimitiveRoot (z n) (g ^ n.factorial - 1) ∧
    z (n+1) ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
  have step : ∀ n (x : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)}),
      ∃ y : {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ (n+1).factorial - 1)},
        y.1 ^ ((g ^ (n+1).factorial - 1) / (g ^ n.factorial - 1)) = x.1 := by
    intro n x
    obtain ⟨ξ, hξ⟩ := exprim g (Nat.factorial_pos (n+1))
    obtain ⟨y, hy, hy'⟩ := lift (pos g (Nat.factorial_pos (n+1))) (dv g (Nat.factorial_dvd_factorial (Nat.le_succ n))) hξ x.2
    exact ⟨⟨y, hy⟩, hy'⟩
  choose f hf using step
  obtain ⟨x0, hx0⟩ := exprim g (Nat.factorial_pos 0)
  let s : ∀ n : ℕ, {x : Formalism.CyclotomicNorms.Fbar g // IsPrimitiveRoot x (g ^ n.factorial - 1)} :=
    fun n => Nat.rec ⟨x0, hx0⟩ (fun n x => f n x) n
  exact ⟨fun n => (s n).1, fun n => ⟨(s n).2, hf n (s n)⟩⟩

theorem divmul {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) (hb : 0 < b) : c / b * (b / a) = c / a := by
  obtain ⟨u, rfl⟩ := h1
  obtain ⟨v, rfl⟩ := h2
  have ha : 0 < a := Nat.pos_of_mul_pos_right hb
  rw [Nat.mul_div_cancel_left _ hb, Nat.mul_div_cancel_left _ ha, mul_assoc, Nat.mul_div_cancel_left _ ha, mul_comm]

theorem gensys : ∃ ζ : ℕ → Formalism.CyclotomicNorms.Fbar g, ∀ d, 0 < d → IsPrimitiveRoot (ζ d) (g ^ d - 1) ∧
    ∀ d', d ∣ d' → 0 < d' → ζ d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = ζ d := by
  obtain ⟨z, hz⟩ := chain g
  have hc : ∀ n k, z (n + k) ^ ((g ^ (n+k).factorial - 1) / (g ^ n.factorial - 1)) = z n := by
    intro n k
    induction k with
    | zero => simp [Nat.div_self (pos g (Nat.factorial_pos n))]
    | succ k ih =>
      rw [← ih, ← (hz (n+k)).2, ← pow_mul, ← add_assoc,
        divmul (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right n k)))
          (dv g (Nat.factorial_dvd_factorial (Nat.le_succ _))) (pos g (Nat.factorial_pos _))]
  refine ⟨fun d => z d ^ ((g ^ d.factorial - 1) / (g ^ d - 1)), fun d hd => ⟨?_, fun d' hdd hd' => ?_⟩⟩
  · exact (hz d).1.pow (pos g (Nat.factorial_pos _)) (Nat.div_mul_cancel (dv g (Nat.dvd_factorial hd le_rfl))).symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_dvd hd' hdd)
    beta_reduce
    rw [← hc d k, ← pow_mul, ← pow_mul,
      divmul (dv g hdd) (dv g (Nat.dvd_factorial hd' le_rfl)) (pos g hd'),
      divmul (dv g (Nat.dvd_factorial hd le_rfl)) (dv g (Nat.factorial_dvd_factorial (Nat.le_add_right d k))) (pos g (Nat.factorial_pos _))]

theorem level (x : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) : ∃ d, 0 < d ∧ x ^ (g ^ d - 1) = 1 := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  let K := IntermediateField.adjoin (ZMod g) {x}
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = g ^ Module.finrank (ZMod g) K := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hcard] at this
  exact ⟨_, Module.finrank_pos, by simpa [y] using congrArg Subtype.val this⟩

noncomputable def E (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((g ^ d - 1 : ℕ) : ℂ))

theorem E_prim {d : ℕ} (hd : 0 < d) : IsPrimitiveRoot (E g d) (g ^ d - 1) :=
  Complex.isPrimitiveRoot_exp _ (pos g hd).ne'

theorem E_pow {d d' : ℕ} (h : d ∣ d') (hd : 0 < d) (hd' : 0 < d') : E g d' ^ ((g ^ d' - 1) / (g ^ d - 1)) = E g d := by
  obtain ⟨c, hc⟩ := dv g h
  have h1 := pos g hd
  have h2 := pos g hd'
  have hc0 : c ≠ 0 := by rintro rfl; omega
  unfold E
  rw [← Complex.exp_nat_mul, hc, Nat.mul_div_cancel_left _ h1]
  congr 1
  have : ((g ^ d - 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h1.ne'
  have : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc0
  rw [Nat.cast_mul]
  field_simp

theorem prim_iff {R : Type} [CommMonoid R] {z : R} {m : ℕ} (h : IsPrimitiveRoot z m) (hm : 0 < m) (a b : ℕ) :
    z ^ a = z ^ b ↔ a ≡ b [MOD m] := by
  have hf : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, h.pow_eq_one⟩
  rw [hf.pow_eq_pow_iff_modEq, ← h.eq_orderOf]

theorem inhab : Nonempty (LabelDatum g) := by
  classical
  obtain ⟨ζ, hζ⟩ := gensys g
  let R : Formalism.CyclotomicNorms.Fbar g → ℂ → Prop := fun x c => ∃ d, 0 < d ∧ ∃ j, x = ζ d ^ j ∧ c = E g d ^ j
  have common : ∀ x c y c', R x c → R y c' → ∃ d, 0 < d ∧ ∃ j j', x = ζ d ^ j ∧ c = E g d ^ j ∧ y = ζ d ^ j' ∧ c' = E g d ^ j' := by
    rintro x c y c' ⟨d, hd, j, rfl, rfl⟩ ⟨e, he, k, rfl, rfl⟩
    have hde := Nat.mul_pos hd he
    refine ⟨d * e, hde, (g ^ (d * e) - 1) / (g ^ d - 1) * j, (g ^ (d * e) - 1) / (g ^ e - 1) * k, ?_, ?_, ?_, ?_⟩
    · rw [pow_mul (ζ _), (hζ d hd).2 _ (Dvd.intro _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro _ rfl) hd hde]
    · rw [pow_mul (ζ _), (hζ e he).2 _ (Dvd.intro_left _ rfl) hde]
    · rw [pow_mul (E _ _), E_pow g (Dvd.intro_left _ rfl) he hde]
  have key : ∀ x c y c', R x c → R y c' → (x = y ↔ c = c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    rw [prim_iff (hζ d hd).1 (pos g hd), prim_iff (E_prim g hd) (pos g hd)]
  have mul : ∀ x c y c', R x c → R y c' → R (x * y) (c * c') := by
    intro x c y c' h h'
    obtain ⟨d, hd, j, j', rfl, rfl, rfl, rfl⟩ := common _ _ _ _ h h'
    exact ⟨d, hd, j + j', (pow_add _ _ _).symm, (pow_add _ _ _).symm⟩
  have ex : ∀ x, x ≠ 0 → ∃ c, R x c := by
    intro x hx
    obtain ⟨d, hd, h⟩ := level g x hx
    haveI : NeZero (g ^ d - 1) := ⟨(pos g hd).ne'⟩
    obtain ⟨j, -, hj⟩ := (hζ d hd).1.eq_pow_of_pow_eq_one h
    exact ⟨_, d, hd, j, hj.symm, rfl⟩
  choose! t ht using ex
  let t' : Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if x = 0 then 0 else t x
  have ht' : ∀ x, x ≠ 0 → R x (t' x) := fun x hx => by simpa [t', hx] using ht x hx
  refine ⟨⟨⟨⟨t', ?_⟩, ?_⟩, ?_, ζ, fun d hd => (hζ d hd).1.eq_orderOf.symm,
    fun d e hd he => (hζ d hd).2 _ (Dvd.intro _ rfl) (Nat.mul_pos hd he)⟩⟩
  · exact (key _ _ _ _ (ht' 1 one_ne_zero) ⟨1, one_pos, 0, by simp, by simp⟩).1 rfl
  · intro x y
    by_cases hx : x = 0
    · simp [t', hx]
    by_cases hy : y = 0
    · simp [t', hy]
    exact (key _ _ _ _ (ht' _ (mul_ne_zero hx hy)) (mul _ _ _ _ (ht' x hx) (ht' y hy))).1 rfl
  · intro x y hx hy h
    exact (key _ _ _ _ (ht' x hx) (ht' y hy)).2 h

theorem thetaOf_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have h : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  have hp : IsPrimitiveRoot (L.gen d) (g ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h1 := (prim_iff hp (pos g hd) _ _).1 h.choose_spec
  have h2 : L.teich x ^ (g ^ d - 1) = 1 := by rw [← map_pow, hx, map_one]
  rw [thetaOf, dite_eq_left h, pow_eq_pow_mod _ h2, pow_eq_pow_mod n h2, h1]

end GlobalTheory.GLq.LabelModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximation
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.AxLemma

theorem ax_lemma_complete : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (y : ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ‖Per.σC g y - y‖ ≤ r) → ∃ z : Om l, (∀ g ∈ H, g z = z) ∧ ‖y - (z : ℂ_[l])‖ ≤ c * r := by
  intro l _
  obtain ⟨c, hc, hax⟩ := ax_lemma l
  refine ⟨c + 1, by linarith, fun H y r hr hy => ?_⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Om l, ‖y - (y₀ : ℂ_[l])‖ ≤ r := by
    have hd : DenseRange ((↑) : PadicAlgCl l → ℂ_[l]) := UniformSpace.Completion.denseRange_coe
    obtain ⟨b, hb⟩ := Metric.denseRange_iff.1 hd y r hr
    exact ⟨b, by rw [← dist_eq_norm]; exact hb.le⟩
  have hsub : ∀ a b : Om l, ((a - b : Om l) : ℂ_[l]) = (a : ℂ_[l]) - (b : ℂ_[l]) := by
    intro a b
    rw [PadicComplex.coe_eq, map_sub, ← PadicComplex.coe_eq, ← PadicComplex.coe_eq]
  obtain ⟨z, hz, hyz⟩ := hax H y₀ r (fun g hg => by
    rw [← PadicComplex.norm_extends l, hsub, ← GlobalTheory.RingBasics.σC_coe]
    have e : Per.σC g (y₀ : ℂ_[l]) - (y₀ : ℂ_[l])
        = Per.σC g ((y₀ : ℂ_[l]) - y) + ((Per.σC g y - y) + (y - (y₀ : ℂ_[l]))) := by
      rw [map_sub]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [GlobalTheory.RingBasics.norm_σC, norm_sub_rev]; exact hy₀
    · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hy g hg) hy₀))
  refine ⟨z, hz, ?_⟩
  rw [← PadicComplex.norm_extends l, hsub] at hyz
  have e : y - (z : ℂ_[l]) = (y - (y₀ : ℂ_[l])) + ((y₀ : ℂ_[l]) - (z : ℂ_[l])) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  linarith

end GlobalTheory.AxLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximationStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axLemma_padicComplex_fixed_element_approximation : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (y : ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ‖Per.σC g y - y‖ ≤ r) → ∃ z : Om l, (∀ g ∈ H, g z = z) ∧ ‖y - (z : ℂ_[l])‖ ≤ c * r := by
  first | exact @GlobalTheory.AxLemma.ax_lemma_complete | exact GlobalTheory.AxLemma.ax_lemma_complete | (intros; apply GlobalTheory.AxLemma.ax_lemma_complete <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEq
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem deRham_invariants_coord_finrank :
    ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), FiniteDimensional Qp LL → Module.Finite LL ↥(DdR PD ρ) → Module.finrank LL ↥(DdR PD ρ) = Module.finrank Qp K * Module.finrank LL V → ∀ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i))) → ∃ D : Submodule K (Fin d → BdR), (∀ y, y ∈ D ↔ ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (y i)) = y) ∧ Module.Finite K ↥D ∧ Module.finrank K ↥D = d := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ ρ d bV hL hfin hrk Φ hΦ
  haveI := PD.finK
  let D : Submodule K (Fin d → BdR) :=
    { carrier := {y | ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec
          (fun i => PD.actdR g (y i)) = y}
      add_mem' := by
        intro a b ha hb g
        have : (fun i => PD.actdR g ((a + b) i)) =
            (fun i => PD.actdR g (a i)) + (fun i => PD.actdR g (b i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, ha g, hb g]
      zero_mem' := by
        intro g
        have : (fun i => PD.actdR g ((0 : Fin d → BdR) i)) = 0 := by
          funext i; simp
        rw [this, Matrix.mulVec_zero]
      smul_mem' := by
        intro c a ha g
        have : (fun i => PD.actdR g ((c • a) i)) = c • (fun i => PD.actdR g (a i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_smul, ha g] }
  have hmem : ∀ z, z ∈ DdR PD ρ ↔ Φ z ∈ D := by
    intro z
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← hΦ g z]
    exact Φ.injective.eq_iff.symm
  let e : ↥(DdR PD ρ) ≃ₗ[Qp] ↥D :=
    { toFun := fun z => ⟨Φ z.1, (hmem _).1 z.2⟩
      invFun := fun y => ⟨Φ.symm y.1, (hmem _).2 (by simpa using y.2)⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp)
      left_inv := fun z => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  haveI : Module.Finite Qp ↥(DdR PD ρ) := Module.Finite.trans LL _
  haveI : Module.Finite Qp ↥D := Module.Finite.equiv e
  refine ⟨D, fun y => Iff.rfl, Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K ↥D
  have h2 := Module.finrank_mul_finrank Qp LL ↥(DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  have h4 : Module.finrank Qp V = d := by simpa using Module.finrank_eq_card_basis bV
  have h5 := e.finrank_eq
  have hpos : 0 < Module.finrank Qp K := Module.finrank_pos
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h1, ← h5, ← h2, hrk, ← h4, ← h3]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamInvariantsCoordinatesFinrankEqStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_invariants_coordinates_finrank_eq : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {d : ℕ} (bV : Module.Basis (Fin d) Qp V), FiniteDimensional Qp LL → Module.Finite LL ↥(DdR PD ρ) → Module.finrank LL ↥(DdR PD ρ) = Module.finrank Qp K * Module.finrank LL V → ∀ Φ : V ⊗[Qp] BdR ≃ₗ[Qp] (Fin d → BdR), (∀ (g : G) (z : V ⊗[Qp] BdR), Φ (actVdR PD ρ g z) = (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (Φ z i))) → ∃ D : Submodule K (Fin d → BdR), (∀ y, y ∈ D ↔ ∀ g : G, (Matrix.of fun i j => algebraMap Qp BdR (bV.repr (ρ g (bV j)) i)).mulVec (fun i => PD.actdR g (y i)) = y) ∧ Module.Finite K ↥D ∧ Module.finrank K ↥D = d := by
  first | exact @GlobalTheory.deRham_invariants_coord_finrank | exact GlobalTheory.deRham_invariants_coord_finrank | (intros; apply GlobalTheory.deRham_invariants_coord_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFamilyAdaptedToSeparatedFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFamilyAdaptedToSeparatedFiltration
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_family_adapted_filtration :
    ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W) (d : ℕ), Module.Finite E ↥D → Module.finrank E ↥D = d → (∀ a, F (a + 1) ≤ F a) → (∀ x, ∃ a, x ∈ F a) → (∀ x, (∀ a, x ∈ F a) → x = 0) → ∃ (x : Fin d → W) (u : Fin d → ℤ), (∀ k, x k ∈ D ∧ x k ∈ F (u k)) ∧ ∀ (a : ℤ) (c : Fin d → E), (∀ k, u k ≠ a → c k = 0) → ∑ k, c k • x k ∈ F (a + 1) → ∀ k, c k = 0 := by
  intro E W _ _ _ D F d hfin hd hF hex hsep
  have anti : Antitone F := antitone_int_of_succ_le hF
  induction d generalizing D with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  | succ d ih =>
    have hne : D ≠ ⊥ := by
      rintro rfl
      simp at hd
    have hinh : ∃ z, D ≤ F z := by
      obtain ⟨s, hs⟩ : D.FG := Module.Finite.iff_fg.mp hfin
      choose g hg using hex
      obtain ⟨m, hm⟩ := (s.image g).bddBelow
      refine ⟨m, ?_⟩
      rw [← hs, Submodule.span_le]
      intro y hy
      exact anti (hm (by simpa using ⟨y, hy, rfl⟩)) (hg y)
    have hbdd : ∃ b : ℤ, ∀ z, D ≤ F z → z ≤ b := by
      obtain ⟨y, hyD, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have : ∃ b, y ∉ F b := by
        by_contra h
        push Not at h
        exact hy0 (hsep y h)
      obtain ⟨b, hb⟩ := this
      refine ⟨b, fun z hz => ?_⟩
      by_contra h
      exact hb (anti (not_le.mp h).le (hz hyD))
    obtain ⟨lo, hlo, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
    have hnot : ¬ D ≤ F (lo + 1) := fun h => by have := hmax _ h; omega
    obtain ⟨x0, hx0D, hx0F⟩ := SetLike.not_le_iff_exists.mp hnot
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hx0F
    have hx0 : x0 ∉ D ⊓ LinearMap.ker f := fun h => hf0 h.2
    have hfin' : Module.Finite E ↥(D ⊓ LinearMap.ker f) :=
      Submodule.finiteDimensional_of_le (inf_le_left : D ⊓ LinearMap.ker f ≤ D)
    have hsup : (D ⊓ LinearMap.ker f) ⊔ Submodule.span E {x0} = D := by
      apply le_antisymm
      · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hx0D)
      · intro y hy
        have h1 : y - (f y / f x0) • x0 ∈ D ⊓ LinearMap.ker f := by
          refine ⟨D.sub_mem hy (D.smul_mem _ hx0D), ?_⟩
          simp [LinearMap.mem_ker, div_mul_cancel₀ _ hf0]
        have h2 : (f y / f x0) • x0 ∈ Submodule.span E {x0} :=
          Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        simpa using Submodule.add_mem_sup h1 h2
    have hd' : Module.finrank E ↥(D ⊓ LinearMap.ker f) = d := by
      have hne0 : x0 ≠ 0 := fun h => hf0 (by simp [h])
      have := Submodule.finrank_sup_add_finrank_inf_eq (D ⊓ LinearMap.ker f) (Submodule.span E {x0})
      rw [hsup, hd, ((Submodule.disjoint_span_singleton' hne0).mpr hx0).eq_bot, finrank_bot,
        finrank_span_singleton hne0] at this
      omega
    obtain ⟨x, u, h1, h2⟩ := ih _ hfin' hd'
    refine ⟨Fin.cons x0 x, Fin.cons lo u, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ⟨hx0D, hlo hx0D⟩
      · exact ⟨(h1 j).1.1, (h1 j).2⟩
    · intro a c hc hs
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      have hc0 : c 0 = 0 := by
        by_cases ha : lo = a
        · subst ha
          have h3 := hf hs
          set_option synthInstance.maxHeartbeats 100000 in
            rw [LinearMap.mem_ker, map_add (f := _), map_sum, map_smul] at h3
          have h4 : ∑ j : Fin d, f (c j.succ • x j) = 0 :=
            Finset.sum_eq_zero fun j _ => by
              rw [map_smul, (LinearMap.mem_ker.mp (h1 j).1.2), smul_zero]
          rw [h4, add_zero, smul_eq_mul] at h3
          exact (mul_eq_zero.mp h3).resolve_right hf0
        · exact hc 0 ha
      rw [hc0, zero_smul, zero_add] at hs
      have h5 := h2 a (fun j => c j.succ) (fun j hj => hc j.succ hj) hs
      intro k
      exact Fin.cases hc0 h5 k

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFamilyAdaptedToSeparatedFiltrationStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_family_adapted_to_separated_filtration : ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W) (d : ℕ), Module.Finite E ↥D → Module.finrank E ↥D = d → (∀ a, F (a + 1) ≤ F a) → (∀ x, ∃ a, x ∈ F a) → (∀ x, (∀ a, x ∈ F a) → x = 0) → ∃ (x : Fin d → W) (u : Fin d → ℤ), (∀ k, x k ∈ D ∧ x k ∈ F (u k)) ∧ ∀ (a : ℤ) (c : Fin d → E), (∀ k, u k ≠ a → c k = 0) → ∑ k, c k • x k ∈ F (a + 1) → ∀ k, c k = 0 := by
  first | exact @GlobalTheory.exists_family_adapted_filtration | exact GlobalTheory.exists_family_adapted_filtration | (intros; apply GlobalTheory.exists_family_adapted_filtration <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwise
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwise
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory.SerreTateIndep

variable {l : ℕ} [Fact l.Prime] {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)}
  {χ : GQ l →* ℚ_[l]ˣ} {r : ℕ} {U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)}

theorem chiC_add (i j : ℤ) (g : GQ l) : chiC χ (i + j) g = chiC χ i g * chiC χ j g := by
  simp [chiC, zpow_add]

theorem twAct_twist (i j : ℤ) (g : GQ l) (y : Fin r → PadicComplex l) :
    twAct act χ (i + j) U g y = chiC χ i g • twAct act χ j U g y := by
  unfold twAct
  rw [chiC_add, mul_smul]

theorem twAct_comb {n : ℕ} (i : ℤ) (g : GQ l) (c : Fin n → PadicComplex l)
    (x : Fin n → Fin r → PadicComplex l) :
    twAct act χ i U g (∑ k, c k • x k) = ∑ k, act g (c k) • twAct act χ i U g (x k) := by
  unfold twAct
  have : (fun b => act g ((∑ k, c k • x k) b)) = ∑ k, act g (c k) • fun b => act g (x k b) := by
    funext b; simp [Finset.sum_apply]
  rw [this, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mulVec_smul, smul_comm]

theorem twAct_zero (i : ℤ) (g : GQ l) : twAct act χ i U g 0 = 0 := by
  unfold twAct
  have : (fun b => act g ((0 : Fin r → PadicComplex l) b)) = 0 := by
    funext b; simp
  rw [this, Matrix.mulVec_zero, smul_zero]

theorem linearIndependent_of_weightwise (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ)
    (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l))
    (hinv : ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) →
      (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E))
    (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l))
    (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ)
    (he : ∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k)
    (hE : ∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) →
      ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) :
    LinearIndependent (PadicComplex l) e := by
  classical
  have key : ∀ (s : Finset (Fin n)) (c : Fin n → PadicComplex l), (∀ k, k ∉ s → c k = 0) →
      ∑ k, c k • e k = 0 → ∀ k, c k = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro c hc _ k; exact hc k (by simp)
    | insert k0 s hk0 ih =>
      intro c hc hsum
      by_cases h0 : c k0 = 0
      · refine ih c (fun k hk => ?_) hsum
        by_cases hkk : k = k0
        · rw [hkk]; exact h0
        · exact hc k (by simp [hkk, hk])
      exfalso
      set d : Fin n → PadicComplex l := fun k => (c k0)⁻¹ * c k with hd
      have hd0 : d k0 = 1 := inv_mul_cancel₀ h0
      have hds : ∑ k, d k • e k = 0 := by
        simp only [hd, mul_smul]
        rw [← Finset.smul_sum, hsum, smul_zero]
      have hfix : ∀ k, ∀ g ∈ G, chiC χ (u k0 - u k) g * act g (d k) = d k := by
        intro k g hg
        have h1 : ∑ k, (chiC χ (u k0 - u k) g * act g (d k)) • e k = 0 := by
          have h := twAct_comb (act := act) (χ := χ) (U := U) (u k0) g d e
          rw [hds, twAct_zero] at h
          rw [h]
          refine Finset.sum_congr rfl fun k _ => ?_
          conv_rhs => rw [← sub_add_cancel (u k0) (u k), twAct_twist, he g hg k]
          rw [smul_smul, mul_comm]
        have h2 := ih (fun k => chiC χ (u k0 - u k) g * act g (d k) - d k) (fun k hk => ?_) ?_ k
        · exact sub_eq_zero.1 h2
        · by_cases hkk : k = k0
          · subst hkk
            simp [hd0, chiC]
          · have : c k = 0 := hc k (by simp [hkk, hk])
            simp [hd, this]
        · simp only [sub_smul, Finset.sum_sub_distrib, h1, hds, sub_self]
      have hex : ∀ k, ∃ x : ↥E, (((x : ↥E) : Om l) : PadicComplex l) = d k ∧ (u k ≠ u k0 → x = 0) := by
        intro k
        by_cases hu : u k = u k0
        · obtain ⟨x, hx, hxd⟩ := (hinv _ _ (hfix k)).2 (by rw [hu, sub_self])
          exact ⟨⟨x, hx⟩, hxd, fun h => (h hu).elim⟩
        · refine ⟨0, ?_, fun _ => rfl⟩
          rw [(hinv _ _ (hfix k)).1 (sub_ne_zero.2 (Ne.symm hu))]
          simp
      choose x hx hx0 using hex
      have h3 := hE (u k0) x hx0 (by simp only [hx, hds]) k0
      have h4 := hx k0
      rw [h3, hd0] at h4
      simp at h4
  exact Fintype.linearIndependent_iff.2 fun c hc => key Finset.univ c (by simp) hc

end GlobalTheory.SerreTateIndep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SerreTateLinearIndependentOfWeightwiseStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serreTate_linearIndependent_of_weightwise : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ) (G : Subgroup (GQ l)) (E : IntermediateField ℚ_[l] (Om l)), (∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ G, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC E)) → ∀ (r n : ℕ) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (e : Fin n → Fin r → PadicComplex l) (u : Fin n → ℤ), (∀ σ ∈ G, ∀ k, twAct act χ (u k) U σ (e k) = e k) → (∀ (a : ℤ) (c : Fin n → ↥E), (∀ k, u k ≠ a → c k = 0) → ∑ k, (((c k : ↥E) : Om l) : PadicComplex l) • e k = 0 → ∀ k, c k = 0) → LinearIndependent (PadicComplex l) e := by
  first | exact @GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | exact GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise | (intros; apply GlobalTheory.SerreTateIndep.linearIndependent_of_weightwise <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisOfFullLattice
noncomputable section

namespace GlobalTheory.Cyc

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped TensorProduct

theorem exists_basis_of_fullLattice {R F M V ι : Type} [CommRing R] [IsDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup M] [Module R M] [AddCommGroup V] [Module F V]
    (f : M →+ V) (hf : Function.Injective f)
    (hs : ∀ (c : R) (m : M), f (c • m) = algebraMap R F c • f m)
    (hfull : ∀ v : V, ∃ c : R, c ≠ 0 ∧ ∃ m, algebraMap R F c • v = f m)
    (b0 : Module.Basis ι R M) :
    ∃ b : Module.Basis ι F V, (∀ j, b j = f (b0 j)) ∧
      ∀ m i, b.repr (f m) i = algebraMap R F (b0.repr m i) := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  haveI : IsScalarTower R F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : M →ₗ[R] V := { toFun := f, map_add' := map_add f, map_smul' := hs }
  haveI : IsLocalizedModule (nonZeroDivisors R) g :=
    { map_units := fun s => by
        have h0 : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
        rw [Module.End.isUnit_iff]
        exact MulAction.bijective (β := V) (Units.mk0 _ h0 : Fˣ)
      surj := fun v => by
        obtain ⟨c, hc, m, hm⟩ := hfull v
        exact ⟨(m, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hm⟩
      exists_of_eq := fun h => ⟨1, by rw [hf h]⟩ }
  exact ⟨b0.ofIsLocalizedModule F (nonZeroDivisors R) g,
    fun j => b0.ofIsLocalizedModule_apply F _ g j,
    fun m i => b0.ofIsLocalizedModule_repr_apply F _ g m i⟩

theorem exists_basis_of_locLat {R G F LL O ι : Type} [CommRing R] [IsDomain R] [Group G]
    [TopologicalSpace G] [Field F] [Field LL] [Algebra F LL] [CommRing O] [Algebra O LL]
    [TopologicalSpace LL] [Algebra R F] [IsFractionRing R F] [Algebra R O] [Fintype ι]
    (T : LocLat G F LL O)
    (hc : ∀ c : R, algebraMap O LL (algebraMap R O c) = algebraMap F LL (algebraMap R F c))
    (hden : ∀ a : LL, ∃ c : R, c ≠ 0 ∧
      ∃ o : O, algebraMap O LL o = algebraMap F LL (algebraMap R F c) * a) :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ b0 : Module.Basis ι R ↥T.L.T, ∃ b : Module.Basis ι F T.V, (∀ j, b j = (b0 j : T.V)) ∧
      (∀ (m : ↥T.L.T) i, b.repr (m : T.V) i = algebraMap R F (b0.repr m i)) ∧
      (∀ (a : O) j i, b.repr (algebraMap O LL a • b j) i =
        algebraMap R F (b0.repr ⟨_, T.L.T.smul_mem a (b0 j).2⟩ i)) ∧
      ∀ v : T.V, (∀ i, ∃ c : R, b.repr v i = algebraMap R F c) → v ∈ T.L.T := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  intro b0
  have key : ∀ (c : R) (w : T.V), algebraMap R F c • w = algebraMap R O c • w := by
    intro c w
    rw [← algebraMap_smul LL (algebraMap R F c) w, ← algebraMap_smul LL (algebraMap R O c) w, hc]
  have hfull : ∀ v : T.V, ∃ c : R, c ≠ 0 ∧ algebraMap R F c • v ∈ T.L.T := by
    intro v
    have hv : v ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
    | zero => exact ⟨1, one_ne_zero, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', hy⟩ := hy
      refine ⟨c * c', mul_ne_zero hc hc', ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, map_mul, mul_smul, key c']
        exact T.L.T.smul_mem _ hx
      · rw [map_mul, mul_smul, key c]
        exact T.L.T.smul_mem _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨c', hc', o, ho⟩ := hden a
      refine ⟨c' * c, mul_ne_zero hc' hc, ?_⟩
      have := T.L.T.smul_mem o hx
      rw [← algebraMap_smul LL, ho, mul_smul, algebraMap_smul,
        smul_comm a (algebraMap R F c) x] at this
      rwa [map_mul, mul_smul]
  obtain ⟨b, hb, hr⟩ := exists_basis_of_fullLattice (R := R) (F := F)
    (T.L.T.subtype.toAddMonoidHom) Subtype.val_injective
    (fun c m => (key c m).symm)
    (fun v => by
      obtain ⟨c, hc, hv⟩ := hfull v
      exact ⟨c, hc, ⟨_, hv⟩, rfl⟩) b0
  refine ⟨b, hb, hr, fun a j i => ?_, fun v hv => ?_⟩
  · rw [← hr, hb, algebraMap_smul]
    rfl
  · rw [← b.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := hv i
    rw [hc, key, hb]
    exact T.L.T.smul_mem _ (b0 i).2

theorem exists_ratBasis_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ b : Module.Basis (Fin d) ℚ_[l] T.V, (∀ (g : ↥(GK K)) (i j : Fin d), M (g : GQ l) i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr (T.ρ g (b j)) i)) ∧ (∀ (a : ↥(OL LL)) (i j : Fin d), A a i j = algebraMap ℚ_[l] (PadicComplex l) (b.repr ((a : ↥LL.1) • b j) i)) ∧ ∀ v : T.V, v ∈ T.L.T ↔ ∀ i, ‖b.repr v i‖ ≤ 1 := by
  intro l _ K LL T d M A h
  letI := zlMod LL T
  obtain ⟨b0, hM, hA⟩ := h
  obtain ⟨b, hb, hr, ha, hv⟩ := exists_basis_of_locLat (R := ℤ_[l]) T (fun _ => rfl) (fun a => by
    have ha : IsAlgebraic ℤ_[l] a :=
      (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 (Algebra.IsAlgebraic.isAlgebraic a)
    obtain ⟨c, hc, hint⟩ := ha.exists_integral_multiple
    exact ⟨c, hc, ⟨c • a, hint⟩, Algebra.smul_def c a⟩) b0
  refine ⟨b, fun g i j => ?_, fun a i j => ?_, fun v => ⟨fun h i => ?_, fun h => ?_⟩⟩
  · have e : T.ρ g (b j) = ((actTZ LL T g (b0 j) : ↥T.L.T) : T.V) := congrArg (T.ρ g) (hb j)
    rw [e]
    exact (hM g i j).trans
      (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (hr (actTZ LL T g (b0 j)) i).symm)
  · exact (hA a i j).trans (congrArg (algebraMap ℚ_[l] (PadicComplex l)) (ha a j i).symm)
  · exact (congrArg norm (hr ⟨v, h⟩ i)).trans_le (b0.repr ⟨v, h⟩ i).2
  · exact hv v fun i => ⟨⟨_, h i⟩, rfl⟩

end GlobalTheory.Cyc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundary
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.TopSteps

theorem mem_cob_of_repr_mem_herrB : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (z : G → Fin A.m → k)
    (b g : ZMod n → Vc k A.m), Repr F A z b g → (b, g) ∈ herrB (F.D A) → z ∈ cob A := by
  intro k G _ _ l n _ _ _ R F A z b g hR hB
  obtain ⟨E, a, p, e, ε, hE, ha, hp, hinj, hex, hpe, hρe, hε⟩ := hR
  unfold GlobalTheory.Models.herrB at hB
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hB

  have hbx : ∀ i, b i = (F.D A).φ i (x (i - 1)) - x i := fun i => by
    have h := congrArg (fun q => q.1 i) hx
    simp at h
    exact h.symm
  have hgx : ∀ i, g i = (F.D A).γ i (x i) - x i := fun i => by
    have h := congrArg (fun q => q.2 i) hx
    simp at h
    exact h.symm
  have hA : F.Obj A := F.obj_sub A E a ha hinj hE
  have h1 : F.Obj (GlobalTheory.Models.chr (1 : G →* kˣ)) := F.obj_one

  set η : ZMod n → Vc k E.m := fun i => ε i - F.map A E a i (x i) with hη
  have hηφ : ∀ i, (F.D E).φ i (η (i - 1)) = η i := by
    intro i
    have h2 := (hε i).2.1
    rw [hbx i, map_sub, F.map_φ A E a hA hE ha] at h2
    simp only [hη, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h2.symm
  have hηγ : ∀ i, (F.D E).γ i (η i) = η i := by
    intro i
    have h3 := (hε i).2.2
    rw [hgx i, map_sub, F.map_γ A E a hA hE ha] at h3
    simp only [hη, map_sub]
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact h3.symm
  obtain ⟨f, hf, hfη⟩ := F.fix E hE η hηφ hηγ

  have hmap0 : ∀ i y, F.map A (GlobalTheory.Models.chr (1 : G →* kˣ)) 0 i y = 0 := by
    intro i y
    have h := F.map_smul A (GlobalTheory.Models.chr (1 : G →* kˣ)) 0 0 hA h1 (fun _ _ => by simp) i y
    simpa using h
  have hpa : p ∘ₗ a = 0 := LinearMap.ext fun y => hex.apply_apply_eq_zero y
  have hpa_map : ∀ i y, F.map E (GlobalTheory.Models.chr (1 : G →* kˣ)) p i (F.map A E a i y) = 0 := by
    intro i y
    have h := F.map_comp A E (GlobalTheory.Models.chr (1 : G →* kˣ)) a p hA hE h1 ha hp i
    rw [hpa] at h
    have h' := LinearMap.congr_fun h y
    simpa [hmap0] using h'.symm

  set one : Fin 1 → k := fun _ => 1 with hone
  set c : k := p (f one) 0 with hc
  have hqc : ∀ v : Fin 1 → k, p (f v) = c • v := by
    intro v
    have hv : v = v 0 • one := funext fun j => by
      obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [hone]
    rw [hv, map_smul, map_smul]
    funext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [hc, hone, mul_comm]
  have hq : p ∘ₗ f = c • LinearMap.id := LinearMap.ext fun v => by simp [hqc]
  have hidH : GlobalTheory.Models.IsHom (GlobalTheory.Models.chr (1 : G →* kˣ)) (GlobalTheory.Models.chr (1 : G →* kˣ)) LinearMap.id :=
    fun _ _ => rfl

  have hcu : c • F.unit 0 = F.unit 0 := by
    have hcomp := F.map_comp _ E _ f p h1 hE h1 hf hp 0
    have hval := LinearMap.congr_fun hcomp (F.unit 0)
    rw [LinearMap.comp_apply, hfη 0, hη, map_sub, (hε 0).1, hpa_map, sub_zero, hq,
      F.map_smul _ _ _ c h1 h1 hidH, F.map_id _ h1] at hval
    simpa using hval
  have hc1 : c = 1 := by
    by_contra hne
    have hu : (c - 1) • F.unit 0 = 0 := by rw [sub_smul, one_smul, hcu, sub_self]
    apply F.unit_ne 0
    have h := inv_smul_smul₀ (sub_ne_zero.mpr hne) (F.unit 0)
    rw [hu, smul_zero] at h
    exact h.symm

  have hpw : p (f one) = one := by rw [hqc, hc1, one_smul]
  have hρ1 : ∀ σ (v : Fin 1 → k), (GlobalTheory.Models.chr (1 : G →* kˣ)).ρ σ v = v := fun σ v => by
    change ((1 : G →* kˣ) σ : k) • LinearMap.id v = v
    simp
  have hw : ∀ σ, E.ρ σ (f one) = f one := fun σ => by
    rw [← hf σ one, hρ1]

  have hker : p (e - f one) = 0 := by rw [map_sub, hpe, hpw, sub_self]
  obtain ⟨y, hy⟩ := (hex (e - f one)).1 hker
  have hkey : ∀ σ, A.ρ σ y = y + z σ := fun σ => by
    apply hinj
    rw [ha σ y, hy, map_sub, hρe σ, hw σ, map_add (f := _), hy]
    abel
  unfold GlobalTheory.Models.cob
  refine LinearMap.mem_range.mpr ⟨y, funext fun σ => ?_⟩
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [hkey σ]
  abel

end GlobalTheory.TopSteps
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCoboundariesOfHerrPairCoboundaryStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_coboundaries_of_herrPair_coboundary : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A : Ob k G) (z : G → Fin A.m → k) (b g : ZMod n → Vc k A.m), Repr F A z b g → (b, g) ∈ herrB (F.D A) → z ∈ cob A := by
  first | exact @GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB | exact GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB | (intros; apply GlobalTheory.TopSteps.mem_cob_of_repr_mem_herrB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanDOfFixed
noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

private theorem mulR_mulR (a b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V a (mulR ℚ_[l] P.R.BdR LL V b x) = mulR ℚ_[l] P.R.BdR LL V (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp [mul_assoc]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem mulR_neg (a : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V (-a) x = -mulR ℚ_[l] P.R.BdR LL V a x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, neg_zero]
  | tmul v c => simp [tmul_neg]
  | add y z hy hz => simp only [map_add (f := _), hy, hz, neg_add]

private theorem mulR_one (x : V ⊗[ℚ_[l]] P.R.BdR) :
    mulR ℚ_[l] P.R.BdR LL V 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private theorem act_mulR (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K))
    (a : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    actVdR (P.PD K) ρ g (mulR ℚ_[l] P.R.BdR LL V a x) =
      mulR ℚ_[l] P.R.BdR LL V ((P.PD K).actdR g a) (actVdR (P.PD K) ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v c => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

private def spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) :
    AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR) where
  carrier := {y | ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR),
    (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, mulR ℚ_[l] P.R.BdR LL V (b i) (d i)}
  zero_mem' := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, b, d, hd, rfl⟩ ⟨n, b', d', hd', rfl⟩
    refine ⟨m + n, Fin.append b b', Fin.append d d', fun i => ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hd j
      · rw [Fin.append_right]; exact hd' j
    · simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  neg_mem' := by
    rintro _ ⟨m, b, d, hd, rfl⟩
    refine ⟨m, fun i => -b i, d, hd, ?_⟩
    simp only [mulR_neg, Finset.sum_neg_distrib]

private theorem mulR_mem_spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (a : P.R.BdR)
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ spanD P K ρ) :
    mulR ℚ_[l] P.R.BdR LL V a x ∈ spanD P K ρ := by
  obtain ⟨m, b, d, hd, rfl⟩ := hx
  refine ⟨m, fun i => a * b i, d, hd, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, mulR_mulR]

private theorem act_mem_spanD (K : FinExt l) (ρ : Representation LL ↥(GK K) V) (g : ↥(GK K))
    (x : V ⊗[ℚ_[l]] P.R.BdR) (hx : x ∈ spanD P K ρ) :
    actVdR (P.PD K) ρ g x ∈ spanD P K ρ := by
  obtain ⟨m, b, d, hd, rfl⟩ := hx
  refine ⟨m, fun i => (P.PD K).actdR g (b i), d, hd, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [act_mulR, (mem_DdR (P.PD K) ρ _).1 (hd i)]

private theorem mem_spanD_of_fixed {K K' : FinExt l} (h : K.1 ≤ K'.1)
    (ρ : Representation LL ↥(GK K) V) (x : V ⊗[ℚ_[l]] P.R.BdR)
    (hxH : x ∈ DdR (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :
    x ∈ spanD P K ρ := by
  haveI : FiniteDimensional ℚ_[l] ↥K'.1 := K'.2
  haveI : Finite (GQ l ⧸ GK K') :=
    Subgroup.quotient_finite_of_isOpen _ (IntermediateField.fixingSubgroup_isOpen K'.1)
  haveI : (GK K').FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine JumpDescent.descent (Ω := Om l) ((GK K').subgroupOf (GK K))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom) ?_ ?_
    (fun c => (mulR ℚ_[l] P.R.BdR LL V (algebraMap (Om l) P.R.BdR c)).toAddMonoidHom) ?_ ?_ ?_
    (fun g => ((g : GQ l) : Om l →* Om l)) (fun _ _ _ => rfl) (fun _ => rfl) ?_
    K'.1.toSubalgebra.toSubsemiring.toSubmonoid ?_
    ⊤ (spanD P K ρ) (fun _ _ _ => trivial) (fun _ _ _ => trivial) (act_mem_spanD P K ρ)
    (fun c => mulR_mem_spanD P K ρ _)
    (fun y _ hy' => ⟨1, fun _ => 1, fun _ => y, fun _ => (mem_DdR (P.PD K) ρ y).2 hy', by
      simp only [mulR_one, Fin.sum_univ_one]⟩) x trivial ?_
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v b => simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  · intro x
    simp only [map_one, LinearMap.toAddMonoidHom_coe, mulR_one]
  · intro g g' x
    simp only [map_mul, LinearMap.toAddMonoidHom_coe, mulR_mulR]
  · intro g g' x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, add_zero]
    | tmul v b => simp [add_mul, tmul_add]
    | add y z hy hz => simp only [map_add (f := _)] at hy hz ⊢; rw [hy, hz]; abel
  · intro g c x
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [act_mulR, P.PD_actdR, P.actQdR_Om]
    rfl
  · intro g
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hg a ha => hg ⟨a, ha⟩, fun hg a => hg a.1 a.2⟩
  · intro g hg
    have := (mem_DdR (P.PD K') _ x).1 hxH ⟨g.1, hg⟩
    rw [JumpDescent.actVdR_comp P h] at this
    exact this

end

theorem spans_descent : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1)
    (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    (ρ : Representation ↥LL.1 ↥(GK K) V),
    Spans (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) → Spans (P.PD K) ρ := by
  intro l _ P K K' LL h V _ _ _ _ ρ hs y
  obtain ⟨m, b, d, hd, rfl⟩ := hs y
  exact (spanD P K ρ).sum_mem fun i _ =>
    mulR_mem_spanD P K ρ _ _ (mem_spanD_of_fixed P h ρ _ (hd i))

end GlobalTheory.DRFil
end
end
