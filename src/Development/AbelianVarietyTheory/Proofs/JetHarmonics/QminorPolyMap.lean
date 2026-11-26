module

public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesMultiplicativeChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMap
open Formalism.REAL Finset

namespace GlobalTheory

theorem _root_.GlobalTheory.qminor_polyMap (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (s : ℂ) :
    ∃ c : ℕ → A, ∀ u : ℂ, _root_.Formalism.REAL.qminor E a b (u - s) = ∑ i ∈ Finset.range (t + 1), u ^ i • c i := by
  classical
  let F : Equiv.Perm (Fin t) → Fin t → Polynomial A := fun σ k =>
    Polynomial.C (if a (σ k) = b k then (1 : A) else 0) * Polynomial.X +
      Polynomial.C ((if a (σ k) = b k then algebraMap ℂ A (-s - ((k : ℕ) : ℂ)) else 0) +
        E (a (σ k)) (b k))
  let P : Polynomial A :=
    ∑ σ, Polynomial.C (((Equiv.Perm.sign σ : ℤ) : A)) * (List.ofFn (F σ)).prod
  have hdeg : P.natDegree < t + 1 := by
    refine Nat.lt_succ_of_le (Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_)
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_list_prod_le _).trans ?_
    have h1 : ∀ k, (F σ k).natDegree ≤ 1 := fun k =>
      (Polynomial.natDegree_add_le _ _).trans
        (max_le ((Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le) (by simp))
    rw [List.map_ofFn, List.sum_ofFn]
    calc ∑ k, (Polynomial.natDegree ∘ F σ) k ≤ ∑ _k : Fin t, 1 := Finset.sum_le_sum fun k _ => h1 k
      _ = t := by simp
  refine ⟨fun i => P.coeff i, fun u => ?_⟩
  have hcomm : ∀ (p : Polynomial A) (k : ℕ),
      Commute ((RingHom.id A) (p.coeff k)) (algebraMap ℂ A u) := fun p k =>
    Algebra.commute_algebraMap_right u _
  have hF : ∀ σ k, Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) (F σ k) =
      _root_.Formalism.REAL.Tm E (u - s - ((k : ℕ) : ℂ)) (a (σ k)) (b k) := by
    intro σ k
    unfold _root_.Formalism.REAL.Tm
    simp only [F, Polynomial.eval₂_add, Polynomial.eval₂_mul_X, Polynomial.eval₂_C,
      RingHom.id_apply]
    split_ifs with h
    · rw [one_mul, ← add_assoc, ← map_add (f := _)]
      congr 2
      ring
    · simp
  have hP : Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) P = _root_.Formalism.REAL.qminor E a b (u - s) := by
    unfold _root_.Formalism.REAL.qminor
    simp only [P, Polynomial.eval₂_finsetSum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Polynomial.eval₂_mul_noncomm _ _ (hcomm _), Polynomial.eval₂_C,
      Polynomial.eval₂_list_prod_noncomm _ _ _ (fun p _ => hcomm p), List.map_ofFn]
    simp only [Function.comp_def, hF, RingHom.id_apply]
  rw [← hP, Polynomial.eval₂_eq_sum_range' _ hdeg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.id_apply, ← map_pow, Algebra.smul_def]
  exact (Algebra.commutes _ _).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorPolyMapStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qminor_sub_eq_polynomial : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin t → Fin n) (s : ℂ), ∃ c : ℕ → A, ∀ u : ℂ, qminor E a b (u - s) = ∑ i ∈ Finset.range (t + 1), u ^ i • c i := by
  first | exact @GlobalTheory.qminor_polyMap | exact GlobalTheory.qminor_polyMap | (intros; apply GlobalTheory.qminor_polyMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsAdicColimitOfFactor
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AdicColimit

variable {R : Type} [CommRing R] (I : Ideal R)

abbrev thickι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) : (thickObj R I e T).left ⟶ T.left :=
  pullback.fst T.hom (thick R I e)

abbrev thickHom (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    (thickObj R I e T').left ⟶ (thickObj R I e T).left :=
  ((Over.pullback (thick R I e)).map r).left

def IsAdicColimit (T : Over (Spec (CommRingCat.of R))) : Prop :=
  ∀ (X : Scheme.{0}) (f : ∀ e : ℕ, (thickObj R I e T).left ⟶ X), (∀ e, thickMap R I e T ≫ f (e + 1) = f e) →
    ∃! g : T.left ⟶ X, ∀ e, thickι I e T ≫ g = f e

instance mono_thick (e : ℕ) : Mono (thick R I e) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

instance mono_thickι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) : Mono (thickι I e T) :=
  inferInstanceAs (Mono (pullback.fst T.hom (thick R I e)))

@[reassoc]
theorem thickMap_ι (e : ℕ) (T : Over (Spec (CommRingCat.of R))) :
    thickMap R I e T ≫ thickι I (e + 1) T = thickι I e T :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

@[reassoc]
theorem thickHom_ι (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    thickHom I e r ≫ thickι I e T = thickι I e T' ≫ r.left :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem thickMap_thickHom (e : ℕ) {T' T : Over (Spec (CommRingCat.of R))} (r : T' ⟶ T) :
    thickMap R I e T' ≫ thickHom I (e + 1) r = thickHom I e r ≫ thickMap R I e T := by
  rw [← cancel_mono (thickι I (e + 1) T), Category.assoc, Category.assoc, thickHom_ι, thickMap_ι,
    thickMap_ι_assoc, thickHom_ι]

variable {I}

theorem IsAdicColimit.hom_ext {T : Over (Spec (CommRingCat.of R))} (h : IsAdicColimit I T) {X : Scheme.{0}}
    {g g' : T.left ⟶ X} (e : ∀ e, thickι I e T ≫ g = thickι I e T ≫ g') : g = g' :=
  (h X (fun e => thickι I e T ≫ g') fun e => thickMap_ι_assoc I e T g').unique e fun _ => rfl

theorem IsAdicColimit.of_iso {T' T : Over (Spec (CommRingCat.of R))} (r : T' ≅ T) (h : IsAdicColimit I T') :
    IsAdicColimit I T := by
  intro X f hf
  obtain ⟨g, hg, hu⟩ := h X (fun e => thickHom I e r.hom ≫ f e) fun e => by
    rw [thickMap_thickHom_assoc, hf]
  refine ⟨r.inv.left ≫ g, fun e => ?_, fun g' hg' => ?_⟩
  · rw [← thickHom_ι_assoc, hg, ← Over.comp_left_assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  · rw [← hu (r.hom.left ≫ g') fun e => by rw [← thickHom_ι_assoc, hg'], ← Over.comp_left_assoc, Iso.inv_hom_id]
    exact (Category.id_comp _).symm

theorem isAdicColimit_of_factor {T : Over (Spec (CommRingCat.of R))} (n : ℕ)
    (σ : T.left ⟶ Spec (CommRingCat.of (R ⧸ I ^ (n + 1)))) (hσ : σ ≫ thick R I n = T.hom) : IsAdicColimit I T := by
  intro X f hf
  let s : T.left ⟶ (thickObj R I n T).left := pullback.lift (𝟙 _) σ ((Category.id_comp _).trans hσ.symm)
  have hs : s ≫ thickι I n T = 𝟙 _ := pullback.lift_fst _ _ _
  have key : ∀ (m k : ℕ) (W : Scheme.{0}) (a : W ⟶ (thickObj R I m T).left) (b : W ⟶ (thickObj R I (m + k) T).left),
      a ≫ thickι I m T = b ≫ thickι I (m + k) T → a ≫ f m = b ≫ f (m + k) := by
    intro m k
    induction k generalizing m with
    | zero => intro W a b h; rw [(cancel_mono _).1 h]; rfl
    | succ k ih =>
      intro W a b h
      have := ih (m + 1) W (a ≫ thickMap R I m T)
      rw [show m + 1 + k = m + (k + 1) by omega] at this
      rw [← this b (by rw [Category.assoc, thickMap_ι, h]), Category.assoc, hf]
  refine ⟨s ≫ f n, fun e => ?_, fun g hg => by rw [← hg n, reassoc_of% hs]⟩
  rw [← Category.assoc]
  rcases le_total e n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [← key e k _ (𝟙 _) _ (by rw [Category.assoc, hs, Category.id_comp, Category.comp_id]), Category.id_comp]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [key n k _ _ (𝟙 _) (by rw [Category.assoc, hs, Category.id_comp, Category.comp_id]), Category.id_comp]

end GlobalTheory.AdicColimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevZeroOfKHighest
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem lev_zero_of_kHighest : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (w : M), GlRel E → IsUnitary ε E → KHighest ε E (lowK ε μ) w → FiniteDimensional ℂ (kSpan ε E w) → Lev ε E μ 0 w := by
  intro M _ _ n ε E μ w hrel _ hhi hfin
  have hk : KRel ε E := glRel_kRel ε E hrel
  have hsq : ckv ε (lowK ε μ) ≤ (Real.sqrt (ckv ε (lowK ε μ)) + 4 * (n : ℝ) * ((0 : ℕ) : ℝ)) ^ 2 := by
    rcases le_total 0 (ckv ε (lowK ε μ)) with h | h
    · simp [Real.sq_sqrt h]
    · simp [Real.sqrt_eq_zero'.mpr h, h]
  refine ⟨⟨kSpan ε E w, hfin, ?_, mem_compact_span_self w, ?_⟩, ?_⟩
  · intro a b hab x hx
    exact compact_span_stable w a b hab x hx
  · intro x hx
    rw [compact_casimir_span_holds M n ε E (lowK ε μ) w hk hhi x hx, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    have hx2 : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_right hsq hx2)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    congr 1
    norm_cast
  · apply Submodule.subset_span
    exact ⟨lowK ε μ, by simp, hhi.1⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApply
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApply
open Formalism.REAL Finset
namespace GlobalTheory

theorem ofFn_prod_intertwine {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (ι : W →ₗ[ℂ] V) : ∀ (t : ℕ) (f : Fin t → Module.End ℂ V)
    (g : Fin t → Module.End ℂ W), (∀ k w, ι (g k w) = f k (ι w)) →
    ∀ w, ι ((List.ofFn g).prod w) = (List.ofFn f).prod (ι w) := by
  intro t
  induction t with
  | zero => intro f g _ w; simp
  | succ t ih =>
    intro f g h w
    simp only [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    rw [h, ih (fun i => f i.succ) (fun i => g i.succ) (fun k => h k.succ)]

theorem qminor_intertwine : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V), (∀ a b w, ι (E' a b w) = E a b (ι w)) → ∀ (a b : Fin t → Fin n) (u : ℂ) (w : W), ι (qminor E' a b u w) = qminor E a b u (ι w) := by
  intro V W _ _ _ _ n t E E' ι h a b u w
  have hT : ∀ (u : ℂ) (a b : Fin n) (w : W), ι (Tm E' u a b w) = Tm E u a b (ι w) := by
    intro u a b w
    unfold Tm
    split_ifs <;> simp [h, Module.algebraMap_end_apply]
  unfold qminor
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Module.End.intCast_apply, map_zsmul]
  congr 1
  exact ofFn_prod_intertwine ι t _ _ (fun k w => hT _ _ _ w) w

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QminorIntertwiningApplyStatement
open Formalism.REAL Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qminor_intertwining_apply : ∀ (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ W) (ι : W →ₗ[ℂ] V), (∀ a b w, ι (E' a b w) = E a b (ι w)) → ∀ (a b : Fin t → Fin n) (u : ℂ) (w : W), ι (qminor E' a b u w) = qminor E a b u (ι w) := by
  first | exact @GlobalTheory.qminor_intertwine | exact GlobalTheory.qminor_intertwine | (intros; apply GlobalTheory.qminor_intertwine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupTorsionTowerExactOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupTorsionTowerExactOrder
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem seq_eq_iff_modEq_of_op {K : Type*} (G : K → K → K) (τ : ℕ → K)
    (hG : ∀ i j, G (τ i) (τ j) = τ (i + j)) (q : ℕ) (hq : 0 < q) (h0 : τ q = τ 0)
    (hord : ∀ {M : Type} [AddMonoid M] (x : M), (∀ d : ℕ, d • x = 0 ↔ τ d = τ 0) →
      addOrderOf x = q) (i j : ℕ) :
    τ i = τ j ↔ i ≡ j [MOD q] := by
  have shift : ∀ a m, τ m = τ 0 → τ (a + m) = τ a := by
    intro a m hm
    rw [← hG a m, hm, hG a 0, Nat.add_zero]
  have mulS : ∀ s, τ s = τ 0 → ∀ n, τ (s * n) = τ 0 := by
    intro s hs n
    induction n with
    | zero => rw [Nat.mul_zero]
    | succ n ih => rw [Nat.mul_succ, shift _ _ hs, ih]
  have cancel : ∀ a k, τ (a + k) = τ a → τ k = τ 0 := by
    intro a k hak
    have e : (q - 1) * a + a = q * a := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel (Nat.succ_le_of_lt hq)]
    calc τ k = τ (k + q * a) := (shift k _ (mulS q h0 a)).symm
      _ = G (τ (a + k)) (τ ((q - 1) * a)) := by rw [hG, ← e]; congr 1; ac_rfl
      _ = G (τ a) (τ ((q - 1) * a)) := by rw [hak]
      _ = τ (q * a) := by rw [hG, Nat.add_comm, e]
      _ = τ 0 := mulS q h0 a
  classical
  have hex : ∃ r, 0 < r ∧ τ r = τ 0 := ⟨q, hq, h0⟩
  obtain ⟨r, hr, hmin⟩ : ∃ r, (0 < r ∧ τ r = τ 0) ∧ ∀ m < r, ¬ (0 < m ∧ τ m = τ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hdvd : ∀ d, τ d = τ 0 ↔ r ∣ d := by
    intro d
    constructor
    · intro hd
      have hmod : τ (d % r) = τ 0 := by
        have h := shift (d % r) (r * (d / r)) (mulS r hr.2 _)
        rw [Nat.mod_add_div] at h
        rw [← h, hd]
      by_contra hnd
      have hpos : 0 < d % r := Nat.pos_of_ne_zero (fun h => hnd (Nat.dvd_of_mod_eq_zero h))
      exact hmin _ (Nat.mod_lt d hr.1) ⟨hpos, hmod⟩
    · rintro ⟨c, rfl⟩
      exact mulS r hr.2 c
  have hrq : r = q := by
    have h := hord (M := ZMod r) (1 : ZMod r) (fun d => by
      rw [nsmul_eq_mul, mul_one, CharP.cast_eq_zero_iff (ZMod r) r, hdvd])
    rwa [ZMod.addOrderOf_one] at h
  have key : ∀ d, τ d = τ 0 ↔ q ∣ d := by
    intro d; rw [hdvd, hrq]
  wlog hij : i ≤ j generalizing i j with H
  · rw [eq_comm, Nat.ModEq.comm]; exact H j i (by omega)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [Nat.modEq_iff_dvd' hij, Nat.add_sub_cancel_left, ← key, eq_comm]
  exact ⟨cancel i k, fun h => shift i k h⟩

theorem tower_exact_order : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → (∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n)) ∧ (∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n)) ∧ ∀ n i j, ev1 (nMul F i) (t n) = ev1 (nMul F j) (t n) ↔ i ≡ j [MOD p ^ n] := by
  intro K _ _ _ p _ F hF t ht ht0 ht1 htp
  have base := (GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF).2
  have hA : ∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n) := by
    intro n j
    rw [← htp n, (base (t (n + 1)) (ht _)).2.2.2.2.1 j p, Nat.mul_comm p j]
  have hB : ∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n) := by
    intro n m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
      intro j
      rw [← Nat.add_assoc, pow_succ', Nat.mul_assoc, hA, ih]
  refine ⟨hA, hB, fun n i j => ?_⟩
  have hτ0 : ev1 (nMul F 0) (t n) = 0 := (base (t n) (ht n)).1
  have hpn : ev1 (nMul F (p ^ n)) (t n) = 0 := by
    have h := hB 0 n 1
    rw [Nat.mul_one, Nat.zero_add, (base (t 0) (ht 0)).2.1, ht0] at h
    exact h
  refine seq_eq_iff_modEq_of_op (fun a b => ev F.toPowerSeries ![a, b])
    (fun d => ev1 (nMul F d) (t n)) (base (t n) (ht n)).2.2.2.1 (p ^ n)
    (pow_pos (Fact.out : p.Prime).pos n) (by simp only [hpn, hτ0]) ?_ i j
  intro M _ x hx
  have hx' : ∀ d : ℕ, d • x = 0 ↔ ev1 (nMul F d) (t n) = 0 := by
    intro d; rw [hx d]; simp only [hτ0]
  rcases n with _ | k
  · have h := (hx' 1).2 (by rw [(base (t 0) (ht 0)).2.1, ht0])
    rw [one_nsmul] at h
    subst h
    simp
  · have h1k : ev1 (nMul F (p ^ k)) (t (k + 1)) = t 1 := by
      have h := hB 1 k 1
      rw [Nat.mul_one, Nat.add_comm 1 k, (base (t 1) (ht 1)).2.1] at h
      exact h
    exact addOrderOf_eq_prime_pow (fun h => ht1 (by rw [← h1k]; exact (hx' _).1 h)) ((hx' _).2 hpn)

end GlobalTheory.ConvSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupTorsionTowerExactOrderStatement
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_torsionTower_exact_order : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → (∀ n j, ev1 (nMul F (p * j)) (t (n + 1)) = ev1 (nMul F j) (t n)) ∧ (∀ n m j, ev1 (nMul F (p ^ m * j)) (t (n + m)) = ev1 (nMul F j) (t n)) ∧ ∀ n i j, ev1 (nMul F i) (t n) = ev1 (nMul F j) (t n) ↔ i ≡ j [MOD p ^ n] := by
  first | exact @GlobalTheory.ConvSer.tower_exact_order | exact GlobalTheory.ConvSer.tower_exact_order | (intros; apply GlobalTheory.ConvSer.tower_exact_order <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearOrthDecomp
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearOrthDecomp
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.WtOrth

theorem inner_eq_zero_of_ne {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsUnitary ε E) {ω ω' : Fin n → ℝ} {x y : M}
    (hx : IsWeight E ω x) (hy : IsWeight E ω' y) (hne : ω ≠ ω') : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h := hU a a x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right] at h
  simp only [Formalism.REAL.sgn, if_true, Complex.ofReal_one, one_mul, Complex.conj_ofReal] at h
  have h2 : ((ω a : ℂ) - (ω' a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h3)) ha
  · exact h3

theorem exists_decomp {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M) (hw : w ∈ WtNear E Λ t) :
    ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t) ∧
      (∀ ω, IsWeight E ω (x ω)) ∧ (∀ ω, ω ∉ T → x ω = 0) ∧ w = ∑ ω ∈ T, x ω := by
  classical
  unfold WtNear at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ω, h1, h2⟩ := hy
    refine ⟨{ω}, fun ω' => if ω' = ω then y else 0, ?_, ?_, ?_, ?_⟩
    · intro ω' h
      rw [Finset.mem_singleton.mp h]; exact h1
    · intro ω'
      by_cases h : ω' = ω
      · simp only [h, if_true]; exact h2
      · intro a; simp [h]
    · intro ω' h
      have : ω' ≠ ω := fun e => h (Finset.mem_singleton.mpr e)
      simp [this]
    · simp
  | zero => exact ⟨∅, fun _ => 0, by simp, fun ω a => by simp, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    obtain ⟨T', x', h1', h2', h3', h4'⟩ := hz
    refine ⟨T ∪ T', fun ω => x ω + x' ω, ?_, ?_, ?_, ?_⟩
    · intro ω h
      rcases Finset.mem_union.mp h with h | h
      · exact h1 ω h
      · exact h1' ω h
    · intro ω a
      simp only [map_add (f := _), h2 ω a, h2' ω a, smul_add]
    · intro ω h
      rw [Finset.mem_union, not_or] at h
      simp [h3 ω h.1, h3' ω h.2]
    · rw [Finset.sum_add_distrib, h4, h4']
      congr 1
      · exact Finset.sum_subset Finset.subset_union_left fun ω _ h => h3 ω h
      · exact Finset.sum_subset Finset.subset_union_right fun ω _ h => h3' ω h
  | smul c y _ hy =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    refine ⟨T, fun ω => c • x ω, h1, ?_, ?_, ?_⟩
    · intro ω a
      simp only [map_smul, h2 ω a]
      exact smul_comm _ _ _
    · intro ω h
      simp [h3 ω h]
    · rw [h4, Finset.smul_sum]

theorem wtNear_orth_decomp : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, h1, h2, _, h4⟩ := exists_decomp E Λ t w hw
  exact ⟨T, x, fun ω h => ⟨h1 ω h, h2 ω⟩, h4,
    fun ω _ ω' _ hne => inner_eq_zero_of_ne hU (h2 ω) (h2 ω') hne⟩

end GlobalTheory.WtOrth
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearOrthDecompStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_weight_decomp_of_mem_wtNear : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by
  first | exact @GlobalTheory.WtOrth.wtNear_orth_decomp | exact GlobalTheory.WtOrth.wtNear_orth_decomp | (intros; apply GlobalTheory.WtOrth.wtNear_orth_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBounds
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem wtdiag_pyth {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ι : Type} (T : Finset ι) (x : ι → M)
    (h : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ⟪x i, x j⟫_ℂ = 0) (c : ι → ℂ) :
    ‖∑ i ∈ T, c i • x i‖ ^ 2 = ∑ i ∈ T, ‖c i‖ ^ 2 * ‖x i‖ ^ 2 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ← ih (fun i hi j hj => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))]
    have h0 : ⟪c a • x a, ∑ i ∈ s, c i • x i⟫_ℂ = 0 := by
      rw [inner_sum]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [inner_smul_left, inner_smul_right, h a (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi)
        (fun e => ha (e ▸ hi))]
      simp
    rw [@norm_add_sq ℂ, h0, norm_smul]
    simp [mul_pow]

theorem wtNear_diag_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → (∀ m : ℝ, (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → m ≤ ∑ a, ω a ^ 2) → m * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2) ∧ (∀ (a : Fin n) (ζ : ℂ) (d : ℝ), 0 ≤ d → (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → d ≤ ‖ζ + (ω a : ℂ)‖) → d ^ 2 * ‖w‖ ^ 2 ≤ ‖ζ • w + E a a w‖ ^ 2) ∧ ∀ (a : Fin n) (D : ℝ), (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → |ω a| ≤ D) → ‖E a a w‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, hx, hsum, horth⟩ := GlobalTheory.T.exists_orthogonal_weight_decomp_of_mem_wtNear M n ε E Λ t w hU hw
  have P := wtdiag_pyth T x horth
  have hw2 : ‖w‖ ^ 2 = ∑ ω ∈ T, ‖x ω‖ ^ 2 := by
    have := P (fun _ => 1)
    simpa [← hsum] using this
  have hE : ∀ a, E a a w = ∑ ω ∈ T, (ω a : ℂ) • x ω := by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    exact Finset.sum_congr rfl fun ω hω => (hx ω hω).2 a
  have hE2 : ∀ a, ‖E a a w‖ ^ 2 = ∑ ω ∈ T, ω a ^ 2 * ‖x ω‖ ^ 2 := by
    intro a
    rw [hE a, P]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    simp_rw [hE2]
    rw [Finset.sum_comm, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hm ω (hx ω hω).1) (sq_nonneg _)
  · intro a ζ d hd h
    have e : ζ • w + E a a w = ∑ ω ∈ T, (ζ + (ω a : ℂ)) • x ω := by
      rw [hE a]
      conv_lhs => rw [hsum, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ω _ => (add_smul _ _ _).symm
    rw [e, P, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hd (h ω (hx ω hω).1) 2) (sq_nonneg _)
  · intro a D h
    rw [hE2, hw2, Finset.mul_sum]
    refine Finset.sum_le_sum fun ω hω => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h ω (hx ω hω).1) 2
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBoundsStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightNear_diagonalOperators_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → (∀ m : ℝ, (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → m ≤ ∑ a, ω a ^ 2) → m * ‖w‖ ^ 2 ≤ ∑ a, ‖E a a w‖ ^ 2) ∧ (∀ (a : Fin n) (ζ : ℂ) (d : ℝ), 0 ≤ d → (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → d ≤ ‖ζ + (ω a : ℂ)‖) → d ^ 2 * ‖w‖ ^ 2 ≤ ‖ζ • w + E a a w‖ ^ 2) ∧ ∀ (a : Fin n) (D : ℝ), (∀ ω : Fin n → ℝ, ∑ a, |ω a - Λ a| ≤ t → |ω a| ≤ D) → ‖E a a w‖ ^ 2 ≤ D ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.wtNear_diag_bounds | exact GlobalTheory.wtNear_diag_bounds | (intros; apply GlobalTheory.wtNear_diag_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleIsHW
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsStableSubmoduleTopWeightLine
open Formalism.REAL

namespace GlobalTheory

inductive LoweringWord {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) : ℕ → V → Prop
  | base : LoweringWord E v 0 v
  | step {N : ℕ} {x : V} (a b : Fin n) (h : b < a) :
      LoweringWord E v N x → LoweringWord E v (N + (a.val - b.val)) (E a b x)

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
  {E : Fin n → Fin n → Module.End ℂ V} {ν : Fin n → ℂ} {v : V}

theorem glRel_apply_comm (hE : GlRel E) (a b c d : Fin n) (y : V) :
    E a b (E c d y) = E c d (E a b y) + (if b = c then E a d y else 0)
      - (if d = a then E c b y else 0) := by
  have h := congrArg (fun f : Module.End ℂ V => f y) (hE a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  have h1 : (if b = c then E a d else 0) y = if b = c then E a d y else 0 := by
    split_ifs <;> simp
  have h2 : (if d = a then E c b else 0) y = if d = a then E c b y else 0 := by
    split_ifs <;> simp
  rw [h1, h2] at h
  rw [add_sub_assoc, ← h]
  abel

theorem loweringWord_span_lower (a b : Fin n) (hab : b < a) :
    ∀ x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x},
      E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨N, hN⟩ := hx
    exact Submodule.subset_span ⟨_, hN.step a b hab⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem loweringWord_apply_mem (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    ∀ a b, E a b x ∈ Submodule.span ℂ {x | ∃ N, LoweringWord E v N x} := by
  induction hx with
  | base =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.2 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.1 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, LoweringWord.base⟩)
    · exact Submodule.subset_span ⟨_, LoweringWord.base.step a b h⟩
  | step c d h _ ih =>
    intro a b
    rw [glRel_apply_comm hE]
    refine Submodule.sub_mem _ (Submodule.add_mem _ (loweringWord_span_lower c d h _ (ih a b)) ?_) ?_
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _
    · split_ifs
      · exact ih _ _
      · exact Submodule.zero_mem _

theorem loweringWord_height (hE : GlRel E) (hv : IsHW E ν v) {N : ℕ} {x : V}
    (hx : LoweringWord E v N x) :
    (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) x
      = ((∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a) + (N : ℂ)) • x := by
  induction hx with
  | base =>
    simp [LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
  | @step N y c d h _ ih =>
    have key : (∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) (E c d y)
        = E c d ((∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a) y)
          + ((c.val : ℕ) : ℂ) • E c d y - ((d.val : ℕ) : ℂ) • E c d y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
      simp only [glRel_apply_comm hE _ _ c d y, smul_sub, smul_add, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    rw [key, ih, map_smul]
    have hle : d.val ≤ c.val := le_of_lt h
    push_cast [Nat.cast_sub hle]
    module

theorem loweringWord_zero_or_pos {N : ℕ} {x : V} (hx : LoweringWord E v N x) :
    x = v ∨ 0 < N := by
  cases hx with
  | base => exact Or.inl rfl
  | step c d h _ =>
    right
    have : d.val < c.val := h
    omega

end

theorem exists_stable_submodule_topWeight_line :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
      (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v →
      ∃ S : Submodule ℂ V, (∀ a b, ∀ x ∈ S, E a b x ∈ S) ∧ v ∈ S ∧
        ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v := by
  intro V _ _ n E ν v hE hv
  refine ⟨Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}, ?_,
    Submodule.subset_span ⟨0, LoweringWord.base⟩, ?_⟩
  · intro a b x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨N, hN⟩ := hx
      exact loweringWord_apply_mem hE hv hN a b
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · intro x hx hw
    set H : Module.End ℂ V := ∑ a : Fin n, ((a.val : ℕ) : ℂ) • E a a with hH
    set h : ℂ := ∑ a : Fin n, ((a.val : ℕ) : ℂ) * ν a with hh
    have hle : Submodule.span ℂ {x | ∃ N, LoweringWord E v N x}
        ≤ Submodule.span ℂ {v} ⊔ ⨆ (μ : ℂ) (_ : μ ≠ h), H.eigenspace μ := by
      rw [Submodule.span_le]
      rintro y ⟨N, hN⟩
      rcases loweringWord_zero_or_pos hN with rfl | hpos
      · exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
      · refine Submodule.mem_sup_right ?_
        have hne : h + (N : ℂ) ≠ h := by
          have : (N : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
          simpa using this
        refine Submodule.mem_iSup_of_mem (h + (N : ℂ)) (Submodule.mem_iSup_of_mem hne ?_)
        rw [Module.End.mem_eigenspace_iff]
        exact loweringWord_height hE hv hN
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (hle hx)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hxe : x ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hw, Finset.sum_smul, mul_smul]
    have hve : v ∈ H.eigenspace h := by
      rw [Module.End.mem_eigenspace_iff]
      simp [hH, hh, LinearMap.sum_apply, hv.1, Finset.sum_smul, mul_smul]
    have hze : z ∈ H.eigenspace h := by
      have : z = x - c • v := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxe (Submodule.smul_mem _ _ hve)
    have hd := Module.End.eigenspaces_iSupIndep H h
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd) z hze hz
    exact ⟨c, by rw [← hyz, hz0, add_zero]⟩

end GlobalTheory
end

open Formalism.REAL

namespace GlobalTheory

theorem stable_submodule_proj_bijective {U V₁ V₂ : Type} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ U) (E₁ : Fin n → Fin n → Module.End ℂ V₁)
    (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v : U)
    (p : U →ₗ[ℂ] V₁) (q : U →ₗ[ℂ] V₂)
    (hp : ∀ a b x, p (E a b x) = E₁ a b (p x)) (hq : ∀ a b x, q (E a b x) = E₂ a b (q x))
    (hpq : ∀ x, p x = 0 → q x = 0 → x = 0)
    (h₁ : ∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (h₂ : ∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hw : ∀ a, E₁ a a (p v) = ν a • p v) (hv₁ : p v ≠ 0) (hv₂ : q v ≠ 0)
    (S : Submodule ℂ U) (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (hvS : v ∈ S)
    (htop : ∀ x ∈ S, (∀ a, E a a x = ν a • x) → ∃ c : ℂ, x = c • v) :
    Function.Bijective (q.comp S.subtype) := by
  constructor
  · have hK := h₁ ((S ⊓ LinearMap.ker q).map p) (by
      rintro a b _ ⟨x, ⟨hxS, hxq⟩, rfl⟩
      refine ⟨E a b x, ⟨hS a b x hxS, ?_⟩, hp a b x⟩
      have hxq' : q x = 0 := hxq
      show q (E a b x) = 0
      rw [hq, hxq', map_zero])
    rcases hK with hK | hK
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have hx' : q x = 0 := hx
      have hm : p x ∈ (S ⊓ LinearMap.ker q).map p := ⟨x, ⟨x.2, hx'⟩, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact Subtype.ext (hpq _ hm hx')
    · exfalso
      have hm : p v ∈ (S ⊓ LinearMap.ker q).map p := by rw [hK]; trivial
      obtain ⟨x, ⟨hxS, hxq⟩, hxp⟩ := hm
      have hxq' : q x = 0 := hxq
      obtain ⟨c, hc⟩ := htop x hxS (fun a => by
        rw [← sub_eq_zero]
        apply hpq
        · rw [map_sub, hp, map_smul, hxp, hw, sub_self]
        · rw [map_sub, hq, map_smul, hxq', map_zero, smul_zero, sub_self])
      rw [hc, map_smul, smul_eq_zero] at hxq'
      rcases hxq' with h0 | h0
      · apply hv₁
        rw [← hxp, hc, h0, zero_smul, map_zero]
      · exact hv₂ h0
  · have hK := h₂ (S.map q) (by
      rintro a b _ ⟨x, hxS, rfl⟩
      exact ⟨E a b x, hS a b x hxS, hq a b x⟩)
    rcases hK with hK | hK
    · exfalso
      have hm : q v ∈ S.map q := ⟨v, hvS, rfl⟩
      rw [hK, Submodule.mem_bot] at hm
      exact hv₂ hm
    · intro y
      have hm : y ∈ S.map q := by rw [hK]; trivial
      obtain ⟨x, hxS, rfl⟩ := hm
      exact ⟨⟨x, hxS⟩, rfl⟩

theorem exists_linearEquiv_of_irreducible_isHW :
    ∀ (V₁ : Type) [AddCommGroup V₁] [Module ℂ V₁] (V₂ : Type) [AddCommGroup V₂] [Module ℂ V₂] (n : ℕ) (E₁ : Fin n → Fin n → Module.End ℂ V₁) (E₂ : Fin n → Fin n → Module.End ℂ V₂) (ν : Fin n → ℂ) (v₁ : V₁) (v₂ : V₂), GlRel E₁ → GlRel E₂ → (∀ S : Submodule ℂ V₁, (∀ a b, ∀ x ∈ S, E₁ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → (∀ S : Submodule ℂ V₂, (∀ a b, ∀ x ∈ S, E₂ a b x ∈ S) → S = ⊥ ∨ S = ⊤) → IsHW E₁ ν v₁ → IsHW E₂ ν v₂ → v₁ ≠ 0 → v₂ ≠ 0 → ∃ T : V₁ ≃ₗ[ℂ] V₂, ∀ a b x, T (E₁ a b x) = E₂ a b (T x) := by
  intro V₁ _ _ V₂ _ _ n E₁ E₂ ν v₁ v₂ hE₁ hE₂ h₁ h₂ hw₁ hw₂ hv₁ hv₂
  let E : Fin n → Fin n → Module.End ℂ (V₁ × V₂) := fun a b => (E₁ a b).prodMap (E₂ a b)
  have hEap : ∀ a b (x : V₁ × V₂), E a b x = (E₁ a b x.1, E₂ a b x.2) := fun _ _ _ => rfl
  have hE : GlRel E := by
    intro a b c d
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hEap]
    rw [glRel_apply_comm hE₁ a b c d, glRel_apply_comm hE₂ a b c d]
    split_ifs <;> simp [hEap]
    all_goals (constructor <;> abel)
  have hw : IsHW E ν (v₁, v₂) := by
    refine ⟨fun a => ?_, fun a b h => ?_⟩
    · rw [hEap, hw₁.1, hw₂.1]; rfl
    · rw [hEap, hw₁.2 a b h, hw₂.2 a b h]; rfl
  obtain ⟨S, hS, hvS, htop⟩ := exists_stable_submodule_topWeight_line _ n E ν _ hE hw
  have b₂ := stable_submodule_proj_bijective E E₁ E₂ ν (v₁, v₂) (LinearMap.fst ℂ V₁ V₂)
    (LinearMap.snd ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h h') h₁ h₂ hw₁.1 hv₁ hv₂ S hS hvS htop
  have b₁ := stable_submodule_proj_bijective E E₂ E₁ ν (v₁, v₂) (LinearMap.snd ℂ V₁ V₂)
    (LinearMap.fst ℂ V₁ V₂) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun x h h' => Prod.ext h' h) h₂ h₁ hw₂.1 hv₂ hv₁ S hS hvS htop
  refine ⟨(LinearEquiv.ofBijective _ b₁).symm.trans (LinearEquiv.ofBijective _ b₂), ?_⟩
  intro a b x
  obtain ⟨y, rfl⟩ := (LinearEquiv.ofBijective _ b₁).surjective x
  have h : E₁ a b (LinearEquiv.ofBijective _ b₁ y)
      = LinearEquiv.ofBijective _ b₁ ⟨E a b y, hS a b y y.2⟩ := rfl
  rw [h]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WtNearLeOfAddDistLe
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem wtNear_le_of_add_dist_le :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M) (Λ Λ' : Fin n → ℝ) (t t' : ℝ),
      t + ∑ a, |Λ a - Λ' a| ≤ t' → WtNear E Λ t ≤ WtNear E Λ' t' := by
  intro M _ _ n _ E Λ Λ' t t' h
  unfold WtNear
  apply Submodule.span_mono
  rintro x ⟨ω, hω, hx⟩
  refine ⟨ω, ?_, hx⟩
  have h1 : ∑ a, |ω a - Λ' a| ≤ ∑ a, (|ω a - Λ a| + |Λ a - Λ' a|) :=
    Finset.sum_le_sum fun a _ => abs_sub_le _ _ _
  rw [Finset.sum_add_distrib] at h1
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasKIsSymmetricAndForm
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasKIsSymmetricAndForm
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem inner_casK_eq_sum {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (h : KUnit ε E) (x y : M) :
    ⟪x, CasK ε E y⟫_ℂ = ∑ a, ∑ b, if ε a = ε b then ⟪E a b x, E a b y⟫_ℂ else 0 := by
  unfold CasK
  rw [Finset.sum_comm]
  simp only [LinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [if_pos hab.symm, if_pos hab, Module.End.mul_apply, h a b hab]
  · rw [if_neg (fun e => hab e.symm), if_neg hab]
    simp

theorem casK_isSymmetric_and_form :
    ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool)
      (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E →
      LinearMap.IsSymmetric (CasK ε E) ∧
        ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  intro M _ _ n ε E h
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [← inner_conj_symm, inner_casK_eq_sum h, inner_casK_eq_sum h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [inner_conj_symm]
    · simp
  · rw [inner_casK_eq_sum h]
    simp only [Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasKIsSymmetricAndFormStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casK_isSymmetric_and_inner_re_eq : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → LinearMap.IsSymmetric (CasK ε E) ∧ ∀ x, (⟪x, CasK ε E x⟫_ℂ).re = ∑ a, ∑ b, if ε a = ε b then ‖E a b x‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.casK_isSymmetric_and_form | exact GlobalTheory.casK_isSymmetric_and_form | (intros; apply GlobalTheory.casK_isSymmetric_and_form <;> assumption)
end
end
