module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZero
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.SubstDiff

variable {τ B : Type} [CommRing B]

def euler (j : τ) (g : MvPowerSeries τ B) : MvPowerSeries τ B :=
  fun γ => (γ j : B) * coeff γ g

theorem coeff_euler (j : τ) (g : MvPowerSeries τ B) (γ : τ →₀ ℕ) :
    coeff γ (euler j g) = (γ j : B) * coeff γ g := rfl

theorem euler_mul (j : τ) (x y : MvPowerSeries τ B) :
    euler j (x * y) = euler j x * y + x * euler j y := by
  classical
  ext γ
  rw [coeff_euler, map_add (f := _), coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q.1 + q.2 = γ := Finset.HasAntidiagonal.mem_antidiagonal.1 hq
  rw [coeff_euler, coeff_euler, ← hq', Finsupp.add_apply]
  push_cast
  ring

theorem euler_one (j : τ) : euler j (1 : MvPowerSeries τ B) = 0 := by
  classical
  ext γ
  rw [coeff_euler, coeff_one, map_zero]
  split_ifs with h
  · subst h; simp
  · simp

theorem euler_pow (j : τ) (x : MvPowerSeries τ B) (n : ℕ) :
    euler j (x ^ (n + 1)) = ((n + 1 : ℕ) : MvPowerSeries τ B) * x ^ n * euler j x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ x (n + 1), euler_mul, ih]
    push_cast
    ring

theorem euler_prod_mem {σ : Type} (j : τ) (u : σ → MvPowerSeries τ B) (α : σ → ℕ)
    (s : Finset σ) :
    euler j (∏ i ∈ s, u i ^ α i) ∈
      Ideal.span (Set.range fun i => ((α i : ℕ) : MvPowerSeries τ B)) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, euler_one]; exact Ideal.zero_mem _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, euler_mul]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ?_) (Ideal.mul_mem_left _ _ ih)
    rcases h : α a with _ | n
    · rw [pow_zero, euler_one]; exact Ideal.zero_mem _
    · rw [euler_pow]
      refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨a, ?_⟩))
      simp only [h]

variable {Q : Type} [CommRing Q] [Algebra B Q]

theorem smul_mem_of_mem_span {σ : Type} (N : Submodule B Q) (α : σ → ℕ) (c : Q)
    (hc : ∀ i, (α i : Q) * c ∈ N) (h : MvPowerSeries τ B)
    (hh : h ∈ Ideal.span (Set.range fun i => ((α i : ℕ) : MvPowerSeries τ B))) :
    ∀ e, coeff e h • c ∈ N := by
  induction hh using Submodule.span_induction with
  | mem x hx =>
    classical
    obtain ⟨i, rfl⟩ := hx
    intro e
    dsimp only
    rw [← map_natCast (C (σ := τ) (R := B)), coeff_C]
    split_ifs
    · rw [Algebra.smul_def, map_natCast]; exact hc i
    · rw [zero_smul]; exact N.zero_mem
  | zero => intro e; rw [map_zero, zero_smul]; exact N.zero_mem
  | add x y _ _ hx hy => intro e; rw [map_add (f := _), add_smul]; exact N.add_mem (hx e) (hy e)
  | smul r x _ hx =>
    classical
    intro e
    rw [smul_eq_mul, coeff_mul, Finset.sum_smul]
    refine N.sum_mem fun q _ => ?_
    rw [mul_smul]
    exact N.smul_mem _ (hx q.2)

end GlobalTheory.QLog.SubstDiff

open GlobalTheory.QLog.SubstDiff in
theorem GlobalTheory.QLog.dIn_subst_up :
    ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O]
      [Algebra B Q] (θ : B →+* O), IsFrame p Q θ →
      ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q)
        (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) →
        DIn N (MvPowerSeries.subst (QLog.up Q u) f) ∧
          (In N f → In N (MvPowerSeries.subst (QLog.up Q u) f)) := by
  intro p _ B O Q _ _ _ _ θ _ σ τ _ N f u hD hu
  set NQ : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N with hNQ
  have memNQ : ∀ q : Q, q ∈ NQ ↔ ∃ b ∈ N, q = algebraMap B Q b := by
    intro q
    rw [hNQ, Submodule.mem_map]
    constructor
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  have ha : HasSubst (QLog.up Q u) :=
    hasSubst_of_constantCoeff_zero fun i => by
      simp only [QLog.up]
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hu i,
        map_zero]

  have hprod : ∀ d : σ →₀ ℕ, (d.prod fun s e => (QLog.up Q u s) ^ e) =
      map (algebraMap B Q) (∏ i, u i ^ d i) := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp only [QLog.up, map_pow]
  have hcoeff : ∀ e, coeff e (MvPowerSeries.subst (QLog.up Q u) f) =
      ∑ d ∈ (coeff_subst_finite ha f e).toFinset,
        algebraMap B Q (coeff e (∏ i, u i ^ d i)) * coeff d f := by
    intro e
    rw [coeff_subst ha, finsum_eq_sum _ (coeff_subst_finite ha f e)]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hprod, coeff_map, smul_eq_mul, mul_comm]
  refine ⟨fun e j => ?_, fun hI e => ?_⟩
  · rw [← memNQ, hcoeff, Finset.mul_sum]
    refine NQ.sum_mem fun d _ => ?_
    have key := smul_mem_of_mem_span NQ (fun i => d i) (coeff d f)
      (fun i => (memNQ _).2 (by obtain ⟨b, hb, h⟩ := hD d i; exact ⟨b, hb, h⟩))
      _ (euler_prod_mem j u (fun i => d i) Finset.univ) e
    convert key using 1
    rw [coeff_euler, Algebra.smul_def, map_mul, map_natCast]
    ring
  · rw [← memNQ, hcoeff]
    refine NQ.sum_mem fun d _ => ?_
    rw [← Algebra.smul_def]
    exact NQ.smul_mem _ ((memNQ _).2 (by obtain ⟨b, hb, h⟩ := hI d; exact ⟨b, hb, h⟩))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffCoeffsInIdealSubstOfConstantCoeffZeroStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diffCoeffsInIdeal_subst_of_constantCoeff_zero : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → DIn N (subst (up Q u) f) ∧ (In N f → In N (subst (up Q u) f)) := by
  first | exact @GlobalTheory.QLog.dIn_subst_up | exact GlobalTheory.QLog.dIn_subst_up | (intros; apply GlobalTheory.QLog.dIn_subst_up <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.TowerLev

theorem compat_seq {X : Type} (A : ℕ → Set X) (hfin : ∀ j, (A j).Finite)
    (hne : ∀ j, (A j).Nonempty) (φ : ℕ → X → X) (hφ : ∀ j, ∀ x ∈ A (j + 1), φ j x ∈ A j) :
    ∃ s : ℕ → X, ∀ j, s j ∈ A j ∧ φ j (s (j + 1)) = s j := by
  let F : ℕᵒᵖ ⥤ Type := Functor.ofOpSequence (X := fun j => ↥(A j))
    (fun j => TypeCat.ofHom (fun x => ⟨φ j x.1, hφ j x.1 x.2⟩ : ↥(A (j + 1)) → ↥(A j)))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => (hfin j.unop).to_subtype
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => (hne j.unop).to_subtype
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  refine ⟨fun j => (s (Opposite.op j)).1, fun j => ⟨(s (Opposite.op j)).2, ?_⟩⟩
  have h := hs (homOfLE (Nat.le_add_right j 1)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h
  exact congrArg Subtype.val h

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] {Q : Type} [CommGroup Q]

def IsLev (D : Datum p) (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ) (r : ℕ) (f : D.La → Q) : Prop :=
  ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
    (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧
    ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y

variable {D : Datum p}

theorem map_zero_of_add {f : D.La → Q} (hf : ∀ x y, f (x + y) = f x * f y) : f 0 = 1 := by
  have h := hf 0 0
  rw [add_zero] at h
  simpa using h.symm

theorem map_nsmul_of_add {f : D.La → Q} (hf : ∀ x y, f (x + y) = f x * f y) (n : ℕ) (x : D.La) :
    f (n • x) = f x ^ n := by
  induction n with
  | zero => simp [map_zero_of_add hf]
  | succ n ih => rw [succ_nsmul, hf, ih, pow_succ]

theorem cancel_nsmul (D : Datum p) (n : ℕ) (hn : n ≠ 0) {a b : D.La} (h : n • a = n • b) : a = b := by
  haveI := D.freeLa
  have h' : (n : ℤ) • a = (n : ℤ) • b := by simpa [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hn : (n : ℤ) ≠ 0) h'

theorem IsLev.step {act : D.O → Q → Q} {W : ℕ → Q → Q → kˣ} {ζ : ℕ → kˣ}
    (hact : ∀ c a b, act c (a * b) = act c a * act c b) (hζ : ∀ r, ζ (r + 1) ^ p = ζ r)
    (hW : ∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 →
      W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p)
    (r : ℕ) (f : D.La → Q) (hf : IsLev D act W ζ (r + 1) f) : IsLev D act W ζ r (fun x => f x ^ p) := by
  obtain ⟨⟨hadd, hlin, hker, honto⟩, hpair⟩ := hf
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hkill : ∀ x, f x ^ (p ^ (r + 1)) = 1 := fun x => (honto _).2 ⟨x, rfl⟩
  refine ⟨⟨fun x y => ?_, fun c x => ?_, fun x => ?_, fun g => ?_⟩, fun x y => ?_⟩
  · simp only
    rw [hadd, mul_pow]
  · simp only
    rw [hlin]
    exact (map_pow (MonoidHom.mk' (act c) (hact c)) (f x) p).symm
  · simp only
    rw [← map_nsmul_of_add hadd, hker]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, cancel_nsmul D p hp0 (by rw [hy, pow_succ', mul_smul])⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, by rw [pow_succ', mul_smul]⟩
  · simp only
    constructor
    · intro hg
      have hg' : g ^ (p ^ (r + 1)) = 1 := by rw [pow_succ, pow_mul, hg, one_pow]
      obtain ⟨x, rfl⟩ := (honto g).1 hg'
      rw [← map_nsmul_of_add hadd, hker] at hg
      obtain ⟨y, hy⟩ := hg
      have hx : x = p • y := cancel_nsmul D (p ^ r) (pow_ne_zero _ hp0) (by rw [hy, pow_succ, mul_smul])
      exact ⟨y, by rw [hx, map_nsmul_of_add hadd]⟩
    · rintro ⟨x, rfl⟩
      rw [← pow_mul, ← pow_succ', hkill]
  · simp only
    rw [hW r (f x) (f y) (hkill x) (hkill y), hpair, ← hζ r, ← zpow_natCast (ζ (r + 1) ^ _),
      ← zpow_natCast (ζ (r + 1)), ← zpow_mul, ← zpow_mul, mul_comm]

theorem finite_range_of_add {f : D.La → Q} (hadd : ∀ x y, f (x + y) = f x * f y) {n : ℕ} (hn : n ≠ 0)
    (hker : ∀ y, f (n • y) = 1) : (Set.range f).Finite := by
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  have hpos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  refine ((Set.Finite.pi (fun _ : Module.Free.ChooseBasisIndex ℤ D.La => Set.finite_Ico (0 : ℤ) n)).image
    (fun v => f (∑ i, v i • B i))).subset ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨fun i => B.repr x i % n, fun i _ => ⟨Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩, ?_⟩
  have hx : x = ∑ i, (B.repr x i % n) • B i + n • ∑ i, (B.repr x i / n) • B i := by
    rw [← natCast_zsmul, Finset.smul_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [← B.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, ← add_smul, Int.emod_add_mul_ediv]
  rw [congrArg f hx, hadd, hker, _root_.mul_one]

def toLin (f : D.La → Q) (hf : ∀ x y, f (x + y) = f x * f y) : D.La →ₗ[ℤ] Additive Q :=
  (AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun x y => by rw [hf]; rfl)).toIntLinearMap

theorem finite_isLev {act : D.O → Q → Q} {W : ℕ → Q → Q → kˣ} {ζ : ℕ → kˣ} (r : ℕ) :
    {f | IsLev D act W ζ r f}.Finite := by
  rcases Set.eq_empty_or_nonempty {f | IsLev D act W ζ r f} with h | ⟨f0, hf0⟩
  · rw [h]; exact Set.finite_empty
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hT : (Set.range f0).Finite :=
    finite_range_of_add hf0.1.1 (pow_ne_zero r hp0) (fun y => (hf0.1.2.2.1 _).2 ⟨y, rfl⟩)
  refine Set.Finite.of_finite_image (f := fun f : D.La → Q => fun i => f (B i)) ?_ ?_
  · refine (Set.Finite.pi (fun _ => hT)).subset ?_
    rintro _ ⟨f, hf, rfl⟩ i _
    exact (hf0.1.2.2.2 _).1 ((hf.1.2.2.2 _).2 ⟨B i, rfl⟩)
  · intro f hf g hg hfg
    have key : toLin f hf.1.1 = toLin g hg.1.1 :=
      B.ext (fun i => congrArg Additive.ofMul (congrFun hfg i))
    funext x
    exact congrArg Additive.toMul (LinearMap.congr_fun key x)

theorem exists_compatible : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q]
    (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ), (∀ c a b, act c (a * b) = act c a * act c b) →
    (∀ r, ζ (r + 1) ^ p = ζ r) →
    (∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 → W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p) →
    (∀ r, ∃ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧
      (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧
      ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y) →
    ∃ ev : ℕ → D.La → Q, (∀ r, ((∀ x y, ev r (x + y) = ev r x * ev r y) ∧
      (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧
      (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) ∧ ∀ x y, W r (ev r x) (ev r y) = ζ r ^ D.EF x y) ∧
      ∀ r x, ev (r + 1) x ^ p = ev r x := by
  intro p _ D k _ Q _ act W ζ hact hζ hW hex
  obtain ⟨s, hs⟩ := compat_seq (fun r => {f | IsLev D act W ζ r f}) (fun r => finite_isLev r) hex
    (fun _ f x => f x ^ p) (fun r f hf => IsLev.step hact hζ hW r f hf)
  exact ⟨s, fun r => (hs r).1, fun r x => congrFun (hs r).2 x⟩

end GlobalTheory.TowerLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSimilitudeLevelTowerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_similitude_level_tower : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (k : Type) [Field k] (Q : Type) [CommGroup Q] (act : D.O → Q → Q) (W : ℕ → Q → Q → kˣ) (ζ : ℕ → kˣ), (∀ c a b, act c (a * b) = act c a * act c b) → (∀ r, ζ (r + 1) ^ p = ζ r) → (∀ r (a b : Q), a ^ (p ^ (r + 1)) = 1 → b ^ (p ^ (r + 1)) = 1 → W r (a ^ p) (b ^ p) = W (r + 1) a b ^ p) → (∀ r, ∃ f : D.La → Q, ((∀ x y, f (x + y) = f x * f y) ∧ (∀ (c : D.O) x, f (c • x) = act c (f x)) ∧ (∀ x, f x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, f x = g)) ∧ ∀ x y, W r (f x) (f y) = ζ r ^ D.EF x y) → ∃ ev : ℕ → D.La → Q, (∀ r, ((∀ x y, ev r (x + y) = ev r x * ev r y) ∧ (∀ (c : D.O) x, ev r (c • x) = act c (ev r x)) ∧ (∀ x, ev r x = 1 ↔ ∃ y, x = (p ^ r) • y) ∧ (∀ g : Q, g ^ (p ^ r) = 1 ↔ ∃ x, ev r x = g)) ∧ ∀ x y, W r (ev r x) (ev r y) = ζ r ^ D.EF x y) ∧ ∀ r x, ev (r + 1) x ^ p = ev r x := by
  first | (exact @GlobalTheory.TowerLev.exists_compatible) | (exact GlobalTheory.TowerLev.exists_compatible) | (intros; apply GlobalTheory.TowerLev.exists_compatible  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesCoeffsInIdealPowEqFactorialMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesCoeffsInIdealPowEqFactorialMul
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DPSeries

section SlopeTestRemainingChoices

variable {B : Type} [CommRing B] {τ : Type}

def coeffIdeal (J : Ideal B) (τ : Type) : Ideal (MvPowerSeries τ B) where
  carrier := {f | ∀ α, coeff α f ∈ J}
  add_mem' {a b} ha hb α := by
    rw [map_add (f := _)]
    exact J.add_mem (ha α) (hb α)
  zero_mem' α := by simp
  smul_mem' c f hf α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun x _ => J.mul_mem_left _ (hf _)

theorem coeff_pow_congr {f g : MvPowerSeries τ B} {β : τ →₀ ℕ}
    (h : ∀ α ≤ β, coeff α f = coeff α g) : ∀ n, ∀ α ≤ β, coeff α (f ^ n) = coeff α (g ^ n) := by
  classical
  intro n
  induction n with
  | zero => intro α _; rfl
  | succ n ih =>
    intro α hα
    rw [pow_succ, pow_succ, coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have h1 : x.1 ≤ β := le_trans (by rw [← hx]; exact le_self_add) hα
    have h2 : x.2 ≤ β := le_trans (by rw [← hx]; exact le_add_self) hα
    rw [ih _ h1, h _ h2]

variable (p : ℕ) (J : Ideal B)

def HasPDiv (f : MvPowerSeries τ B) : Prop :=
  f ∈ coeffIdeal J τ ∧ ∃ y ∈ coeffIdeal J τ, f ^ p = (p : MvPowerSeries τ B) * y

variable {p J}

theorem hasPDiv_add (hp : p.Prime) {a b : MvPowerSeries τ B} (ha : HasPDiv p J a)
    (hb : HasPDiv p J b) : HasPDiv p J (a + b) := by
  obtain ⟨ha, ya, hya, hpa⟩ := ha
  obtain ⟨hb, yb, hyb, hpb⟩ := hb
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp a b
  refine ⟨(coeffIdeal J τ).add_mem ha hb, ya + yb + a * b * r, ?_, ?_⟩
  · exact (coeffIdeal J τ).add_mem ((coeffIdeal J τ).add_mem hya hyb)
      ((coeffIdeal J τ).mul_mem_right _ ((coeffIdeal J τ).mul_mem_right _ ha))
  · rw [hr, hpa, hpb]; ring

theorem hasPDiv_monomial (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) (α : τ →₀ ℕ) {c : B}
    (hc : c ∈ J) : HasPDiv p J (monomial α c) := by
  classical
  obtain ⟨y, hy, hcy⟩ := hJ c hc
  refine ⟨fun γ => ?_, monomial (p • α) y, fun γ => ?_, ?_⟩
  · rw [coeff_monomial]; split_ifs
    · exact hc
    · exact J.zero_mem
  · rw [coeff_monomial]; split_ifs
    · exact hy
    · exact J.zero_mem
  · rw [monomial_pow, hcy]
    ext γ
    rw [coeff_monomial, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, coeff_monomial]
    split_ifs <;> simp

theorem hasPDiv_sum (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y)
    (c : (τ →₀ ℕ) → B) (hc : ∀ α, c α ∈ J) (s : Finset (τ →₀ ℕ)) :
    HasPDiv p J (∑ α ∈ s, monomial α (c α)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (coeffIdeal J τ).zero_mem, 0, (coeffIdeal J τ).zero_mem, ?_⟩
    simp [hp.ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasPDiv_add hp (hasPDiv_monomial hJ a (hc a)) ih

theorem pow_prime_eq (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y)
    {w : MvPowerSeries τ B} (hw : w ∈ coeffIdeal J τ) :
    ∃ y ∈ coeffIdeal J τ, w ^ p = (p : MvPowerSeries τ B) * y := by
  classical
  have key : ∀ β : τ →₀ ℕ, ∃ c ∈ J, coeff β (w ^ p) = p * c := by
    intro β
    set w' : MvPowerSeries τ B := ∑ α ∈ Finset.Iic β, monomial α (coeff α w) with hw'
    have hagree : ∀ α ≤ β, coeff α w = coeff α w' := by
      intro α hα
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hw', map_sum]
      simp_rw [coeff_monomial]
      rw [Finset.sum_ite_eq]
      simp [Finset.mem_Iic.mpr hα]
    obtain ⟨_, y, hy, hpy⟩ := hasPDiv_sum hp hJ (fun α => coeff α w) hw (Finset.Iic β)
    refine ⟨coeff β y, hy β, ?_⟩
    have hpy' : w' ^ p = (p : MvPowerSeries τ B) * y := hpy
    rw [coeff_pow_congr hagree p β le_rfl, hpy',
      ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul]
  choose c hcJ hc using key
  let y : MvPowerSeries τ B := fun β => c β
  have hy : ∀ β, coeff β y = c β := fun _ => rfl
  refine ⟨y, fun β => by rw [hy]; exact hcJ β, ?_⟩
  ext β
  rw [hc, ← map_natCast (C (σ := τ) (R := B)) p, coeff_C_mul, hy]

theorem pow_eq_pow_factorization_mul (hp : p.Prime) (hJ : ∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) :
    ∀ n : ℕ, 0 < n → ∀ w ∈ coeffIdeal J τ, ∃ y ∈ coeffIdeal J τ,
      w ^ n = (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn w hw
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hmn : m < p * m := by nlinarith [hp.two_le]
    obtain ⟨z, hz, hwz⟩ := pow_prime_eq hp hJ hw
    obtain ⟨y, hy, hzy⟩ := ih m hmn hm z hz
    refine ⟨y, hy, ?_⟩
    rw [Nat.factorization_factorial_mul hp, pow_mul, hwz, mul_pow, hzy]
    ring
  · rcases Nat.lt_or_ge n 2 with h | h
    · have h1 : n = 1 := by omega
      subst h1
      exact ⟨w, hw, by simp⟩
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      obtain ⟨y, hy, hwy⟩ := ih k (by omega) (by omega) w hw
      refine ⟨w * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩
      have hv : (k + 1).factorial.factorization p = k.factorial.factorization p := by
        rw [Nat.factorial_succ, Nat.factorization_mul (Nat.succ_ne_zero k)
          (Nat.factorial_ne_zero k), Finsupp.add_apply,
          Nat.factorization_eq_zero_of_not_dvd hpn, zero_add]
      rw [hv, pow_succ, hwy]; ring

end SlopeTestRemainingChoices

theorem pow_eq_factorial_mul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B,
    (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (τ : Type) (w : MvPowerSeries τ B),
    (∀ α, coeff α w ∈ J) → ∀ n : ℕ, 0 < n → ∃ y : MvPowerSeries τ B,
    (∀ α, coeff α y ∈ J) ∧ w ^ n = (n.factorial : MvPowerSeries τ B) * y := by
  intro p hpf B O Q _ _ _ _ θ hF J hJ τ w hw n hn
  have hp : p.Prime := hpf.out
  obtain ⟨y, hy, hwy⟩ := pow_eq_pow_factorization_mul hp hJ n hn w hw
  obtain ⟨c, hc_def⟩ : ∃ c, c = ordCompl[p] n.factorial := ⟨_, rfl⟩
  have hcop : Nat.Coprime c p := by
    rw [hc_def]; exact (Nat.coprime_ordCompl hp (Nat.factorial_ne_zero n)).symm
  obtain ⟨u, hu⟩ := hF.unit_coprime c hcop
  refine ⟨C (↑u⁻¹ : B) * y, (coeffIdeal J τ).mul_mem_left _ hy, ?_⟩
  have hnat : p ^ (n.factorial.factorization p) * c = n.factorial := by
    rw [hc_def]; exact Nat.ordProj_mul_ordCompl_eq_self _ _
  have hfac : (p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * (c : MvPowerSeries τ B) =
      (n.factorial : MvPowerSeries τ B) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, hnat]
  have hcu : (c : MvPowerSeries τ B) * C (↑u⁻¹ : B) = 1 := by
    rw [← map_natCast (C (σ := τ) (R := B)) c, ← hu, ← map_mul, Units.mul_inv, map_one]
  rw [hwy, ← hfac]
  linear_combination (-((p : MvPowerSeries τ B) ^ (n.factorial.factorization p) * y)) * hcu

end GlobalTheory.DPSeries
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesCoeffsInIdealPowEqFactorialMulStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mvPowerSeries_coeffsInIdeal_pow_eq_factorial_mul : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (τ : Type) (w : MvPowerSeries τ B), (∀ α, coeff α w ∈ J) → ∀ n : ℕ, 0 < n → ∃ y : MvPowerSeries τ B, (∀ α, coeff α y ∈ J) ∧ w ^ n = (n.factorial : MvPowerSeries τ B) * y := by
  first | exact @GlobalTheory.DPSeries.pow_eq_factorial_mul | exact GlobalTheory.DPSeries.pow_eq_factorial_mul | (intros; apply GlobalTheory.DPSeries.pow_eq_factorial_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffFrob
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.QLog.Window

section Integral

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type}

theorem in_top_iff (f : MvPowerSeries σ Q) :
    In (⊤ : Ideal B) f ↔ ∃ s : MvPowerSeries σ B, f = map (algebraMap B Q) s := by
  constructor
  · intro h
    choose b _ hb using h
    let s : MvPowerSeries σ B := fun α => b α
    refine ⟨s, ?_⟩
    ext α
    rw [coeff_map, hb]
    rfl
  · rintro ⟨s, rfl⟩ α
    exact ⟨coeff α s, Submodule.mem_top, by rw [coeff_map]⟩

theorem in_zero (N : Ideal B) : In N (0 : MvPowerSeries σ Q) := fun _ =>
  ⟨0, N.zero_mem, by simp⟩

theorem in_add {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f + g) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add (f := _), ea, eb, map_add (f := _)]⟩

theorem in_neg {N : Ideal B} {f : MvPowerSeries σ Q} (hf : In N f) : In N (-f) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨-a, N.neg_mem ha, by rw [map_neg, ea, map_neg]⟩

theorem in_smul {N : Ideal B} {f : MvPowerSeries σ Q} (hf : In N f) (b : B) :
    In N (algebraMap B Q b • f) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  exact ⟨b * a, N.mul_mem_left b ha, by rw [map_smul, smul_eq_mul, ea, ← map_mul]⟩

theorem in_sum {N : Ideal B} {ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ Q)
    (hf : ∀ i ∈ s, In N (f i)) : In N (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using in_zero (σ := σ) (Q := Q) N
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact in_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Integral

section Frob

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (p : ℕ) [hp : Fact p.Prime]
  {σ : Type} [Finite σ] (s : Q →+* Q)

theorem hasSubst_X_pow : HasSubst (fun i : σ => (X i : MvPowerSeries σ Q) ^ p) :=
  HasSubst.X_pow hp.out.ne_zero

theorem frob_add (f g : MvPowerSeries σ Q) : frob p s (f + g) = frob p s f + frob p s g := by
  unfold frob
  rw [map_add (f := _), subst_add (hasSubst_X_pow p)]

theorem frob_zero : frob p s (0 : MvPowerSeries σ Q) = 0 := by
  have h := frob_add p s (0 : MvPowerSeries σ Q) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem frob_sub (f g : MvPowerSeries σ Q) : frob p s (f - g) = frob p s f - frob p s g := by
  unfold frob
  rw [map_sub, subst_sub (hasSubst_X_pow p)]

theorem map_smul' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (r : R)
    (f : MvPowerSeries σ R) : map φ (r • f) = φ r • map φ f := by
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul]

theorem frob_smul (r : Q) (f : MvPowerSeries σ Q) : frob p s (r • f) = s r • frob p s f := by
  unfold frob
  rw [map_smul', subst_smul (hasSubst_X_pow p)]

theorem frob_sum {ι : Type} (t : Finset ι) (f : ι → MvPowerSeries σ Q) :
    frob p s (∑ i ∈ t, f i) = ∑ i ∈ t, frob p s (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using frob_zero p s
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frob_add, ih]

theorem frob_comb (σ' : B →+* B) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ' b))
    {ι : Type} [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    frob p s (comb b e) = comb (fun i => σ' (b i)) fun i => frob p s (e i) := by
  unfold comb
  rw [frob_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frob_smul, hs]

theorem constantCoeff_frob {f : MvPowerSeries σ Q} (hf : constantCoeff f = 0) :
    constantCoeff (frob p s f) = 0 := by
  unfold frob
  refine constantCoeff_subst_eq_zero (hasSubst_X_pow p) (fun i => ?_) ?_
  · rw [map_pow, constantCoeff_X, zero_pow hp.out.ne_zero]
  · rw [constantCoeff_map, hf, map_zero]

theorem in_frob (σ' : B →+* B) (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (σ' b))
    {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) : In (⊤ : Ideal B) (frob p s f) := by
  obtain ⟨t, rfl⟩ := (in_top_iff f).1 hf
  refine (in_top_iff _).2 ⟨subst (fun i : σ => (X i : MvPowerSeries σ B) ^ p) (map σ' t), ?_⟩
  have hm : map s (map (algebraMap B Q) t) = map (algebraMap B Q) (map σ' t) := by
    ext α
    simp only [coeff_map, hs]
  unfold frob
  rw [hm, map_subst (HasSubst.X_pow hp.out.ne_zero)]
  simp only [map_pow, map_X]

end Frob

section Cob

theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero h),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {d : ℕ}
  {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}

theorem constantCoeff_up (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) :
    constantCoeff (up Q μ i) = 0 := by
  rw [up, constantCoeff_map, hμ, map_zero]

theorem ql_zero (hμ : ∀ i, constantCoeff (μ i) = 0) (N : Ideal B) :
    QL μ N (0 : MvPowerSeries (Fin d) Q) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, ?_⟩
  have h := formalCoboundary_smul (constantCoeff_up (Q := Q) hμ) (0 : Q) 0
  rw [zero_smul, zero_smul] at h
  rw [h]
  exact in_zero N

theorem ql_add_smul (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B}
    {f g : MvPowerSeries (Fin d) Q} (hf : QL μ N f) (hg : QL μ N g) (b : B) :
    QL μ N (f + algebraMap B Q b • g) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, map_add (f := _), map_smul, coeff_zero_eq_constantCoeff_apply,
      coeff_zero_eq_constantCoeff_apply, hf.1, hg.1, smul_zero, add_zero]
  · obtain ⟨a, ha, ea⟩ := hf.2.1 i
    obtain ⟨a', ha', ea'⟩ := hg.2.1 i
    refine ⟨a + b * a', N.add_mem ha (N.mul_mem_left b ha'), ?_⟩
    simp only [lin] at ea ea' ⊢
    rw [map_add (f := _), map_smul, ea, ea', smul_eq_mul, map_add (f := _), map_mul]
  · rw [formalCoboundary_add (constantCoeff_up hμ), formalCoboundary_smul (constantCoeff_up hμ)]
    exact in_add hf.2.2 (in_smul hg.2.2 b)

theorem ql_comb (hμ : ∀ i, constantCoeff (μ i) = 0) {N : Ideal B} {ι : Type} [Fintype ι]
    (e : ι → MvPowerSeries (Fin d) Q) (he : ∀ i, QL μ N (e i)) (b : ι → B) :
    QL μ N (comb b e) := by
  classical
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using ql_zero (Q := Q) hμ N
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, add_comm]
    exact ql_add_smul hμ ih (he a) (b a)

end Cob

end GlobalTheory.QLog.Window
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstLiftXPowFrob
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.Katz

variable (p : ℕ) [Fact p.Prime] {k k' k'' : Type} [Field k] [CharP k p] [Field k'] [CharP k' p]
  [Field k''] [CharP k'' p]

theorem wittMap_injective (σ : k →+* k') :
    Function.Injective ((algebraMap (WittVector p k') (Fr p k')).comp (WittVector.map σ)) :=
  (IsFractionRing.injective (WittVector p k') (Fr p k')).comp (WittVector.map_injective σ σ.injective)

def frMap (σ : k →+* k') : Fr p k →+* Fr p k' := IsFractionRing.lift (wittMap_injective p σ)

theorem frMap_algebraMap (σ : k →+* k') (w : WittVector p k) :
    frMap p σ (algebraMap _ _ w) = algebraMap _ _ (WittVector.map σ w) :=
  IsFractionRing.lift_algebraMap _ _

theorem frMap_id : frMap p (RingHom.id k) = RingHom.id (Fr p k) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp [frMap_algebraMap, WittVector.map_id]

theorem frMap_comp (σ : k →+* k') (τ : k' →+* k'') :
    frMap p (τ.comp σ) = (frMap p τ).comp (frMap p σ) := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap]
  congr 1

theorem map_lift {ι : Type} (σ : k →+* k') (f : MvPowerSeries ι k) :
    MvPowerSeries.map (frMap p σ) (lift p f) = lift p (MvPowerSeries.map σ f) := by
  ext α
  rw [coeff_map, coeff_lift, coeff_lift, frMap_algebraMap, WittVector.map_teichmuller, coeff_map]

theorem map_subst_lift {d e : ℕ} (τ : k' →+* k'') (ψ : Fin d → MvPowerSeries (Fin e) k')
    (hψ : ∀ j, constantCoeff (ψ j) = 0) (g : MvPowerSeries (Fin d) (Fr p k')) :
    MvPowerSeries.map (frMap p τ) (subst (fun j => lift p (ψ j)) g) =
      subst (fun j => lift p (MvPowerSeries.map τ (ψ j))) (MvPowerSeries.map (frMap p τ) g) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero fun j => constantCoeff_lift p (hψ j))]
  simp only [map_lift]

theorem lift_X_pow {ι : Type} (i : ι) (n : ℕ) :
    lift p ((X i : MvPowerSeries ι k) ^ n) = X i ^ n := by
  classical
  ext α
  rw [coeff_lift, coeff_X_pow, coeff_X_pow]
  split_ifs <;> simp

theorem frobRing_eq (h : (p : k) = 0) : frobRing h = frobenius k p :=
  RingHom.ext fun r => by rw [frobRing_apply, frobenius_def]

theorem frMap_frobenius [PerfectRing k p] : frMap p (frobenius k p) = KatzF.sig p k := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors (WittVector p k)) (RingHom.ext fun w => ?_)
  simp only [RingHom.comp_apply, frMap_algebraMap, KatzF.sig, WittVector.FractionRing.frobenius]
  rw [RingEquiv.coe_toRingHom, IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  rw [← WittVector.frobenius_eq_map_frobenius]
  rfl

theorem subst_lift_X_pow_frob [PerfectRing k p] (h : (p : k) = 0) {d : ℕ}
    (f : MvPowerSeries (Fin d) (Fr p k)) :
    subst (fun j => lift p ((X j : MvPowerSeries (Fin d) k) ^ p)) (MvPowerSeries.map (frMap p (frobRing h)) f) =
      KatzF.frobS p f := by
  simp only [lift_X_pow, frobRing_eq p h, frMap_frobenius, KatzF.frobS]
  rfl

theorem ringHom_eq_of_app {q : ℕ} {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
    {σ : O →+* O'} {τ : O' →+* O''} {υ : O →+* O''} {G : PDivGroup q O} {G' : PDivGroup q O'}
    {G'' : PDivGroup q O''} (s : SemiHom σ G' G) (t : SemiHom τ G'' G') (u : SemiHom υ G'' G)
    (h : ∀ n a, u.app n a = t.app n (s.app n a)) : υ = τ.comp σ := by
  ext r
  have e := h 0 (r • 1)
  rw [(u.app 0).smul_map, (s.app 0).smul_map, (t.app 0).smul_map, map_one, map_one, map_one] at e
  have := congrArg (Coalgebra.counit (R := O'')) e
  simpa [Algebra.smul_def] using this

end GlobalTheory.Katz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneFraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneFraction
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace LawUp

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (CobCob.elim_has hu hv)]
  congr 1
  funext j
  cases j <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => map φ (op μ u v i)) =
      op (fun i => map φ (μ i)) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  funext i
  exact mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem isLaw_map (φ : R →+* S) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : IsLaw μ) :
    IsLaw (fun i => map φ (μ i)) := by
  have h12 := CobCob.op_const h.const (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
  have h23 := CobCob.op_const h.const (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, h.const i, map_zero]
  · have e := map_op φ μ (τ := Fin d) (u := fun i => (X i : MvPowerSeries (Fin d) R))
      (v := fun _ => 0) (fun _ => constantCoeff_X _) (fun _ => map_zero _)
    rw [h.unit] at e
    simp only [map_X, map_zero] at e
    exact e.symm
  · have e := mvPowerSeriesMap_evalTwoGroups φ (μ i) (τ := Fin d ⊕ Fin d)
      (u := fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (v := fun i => X (Sum.inl i)) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
    simp only [map_X] at e
    unfold swap
    rw [← e]
    exact congrArg (map φ) (h.comm i)
  · have e1 := map_op φ μ h12 CobCob.constantCoeff_threeGroupsThirdVariables
    have e2 := map_op φ μ CobCob.constantCoeff_threeGroupsFirstVariables h23
    have e3 := map_op φ μ (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
    have e4 := map_op φ μ (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
    have hx1 : (fun i => map φ (x1 (R := R) (d := d) i)) = x1 := by funext i; exact map_X _ _
    have hx2 : (fun i => map φ (x2 (R := R) (d := d) i)) = x2 := by funext i; exact map_X _ _
    have hx3 : (fun i => map φ (x3 (R := R) (d := d) i)) = x3 := by funext i; exact map_X _ _
    rw [hx1, hx2] at e3
    rw [hx2, hx3] at e4
    rw [e3, hx3] at e1
    rw [e4, hx1] at e2
    rw [← e1, ← e2, h.assoc]

end LawUp

theorem formalGroupLawCoboundaryTwo_coboundaryOne_fractions : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  intro B Q _ _ _ d μ h g
  have hL : IsLaw (up Q μ) := LawUp.isLaw_map (algebraMap B Q) h
  exact ((formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hL.const g).2.2.2.2.2 hL).1

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneFractionStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  first | exact @GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions | exact GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions | (intros; apply GlobalTheory.formalGroupLawCoboundaryTwo_coboundaryOne_fractions <;> assumption)
end
end
