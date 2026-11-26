module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterOnTorsionPointsEqSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SeriesTwoPointsEqSumMul
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SeriesTwoPointsEqSumMul
namespace GlobalTheory

namespace SeriesTensor

private theorem mem_smul_top_iff {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ (I • ⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  constructor
  · intro hx i
    have hle : (I • ⊤ : Submodule R M) ≤ Submodule.comap (b.coord i) I :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

private theorem isAdicComplete_of_basis {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (b : Module.Basis ι R M) (I : Ideal R) [hI : IsAdicComplete I R] :
    IsAdicComplete I M := by
  have htop : ∀ k : ℕ, (I ^ k • ⊤ : Submodule R R) = I ^ k := fun k => by
    rw [smul_eq_mul, Ideal.mul_top]
  have hH : IsHausdorff I M := by
    refine ⟨fun x hx => ?_⟩
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun n => ?_
    have := hx n
    rw [SModEq.zero, mem_smul_top_iff b] at this
    rw [SModEq.zero, htop]
    exact this i
  have hP' : IsPrecomplete I M := by
    rw [isPrecomplete_iff]
    intro F hF
    have hP := hI.toIsPrecomplete
    rw [isPrecomplete_iff] at hP
    have hc : ∀ i, ∃ L : R, ∀ k, b.repr (F k) i ≡ L [SMOD (I ^ k • ⊤ : Submodule R R)] := by
      intro i
      refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
      have := hF hmn
      rw [SModEq.sub_mem, mem_smul_top_iff b] at this
      rw [SModEq.sub_mem, htop]
      simpa using this i
    choose L hL using hc
    refine ⟨∑ i, L i • b i, fun k => ?_⟩
    rw [SModEq.sub_mem, mem_smul_top_iff b]
    intro i
    have := hL i k
    rw [SModEq.sub_mem, htop] at this
    have hr : b.repr (∑ j, L j • b j) i = L i := by
      have h := congrFun (b.equivFun.apply_symm_apply L) i
      rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
    rw [map_sub, Finsupp.sub_apply, hr]
    exact this
  exact { toIsHausdorff := hH, toIsPrecomplete := hP' }

private theorem exists_pow_mem {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {a c : O} (ha : algebraMap O C a ≠ 0) (hc : ¬ IsUnit c) :
    ∃ n : ℕ, c ^ n ∈ Ideal.span {a} := by
  have h1 : v (algebraMap O C c) < 1 :=
    lt_of_le_of_ne (hv.map_le_one c) fun h => hc (hv.isUnit_iff_valuation_eq_one.2 h)
  have h0 : 0 < v (algebraMap O C a) := pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 ha)
  obtain ⟨n, hn⟩ := NNReal.exists_pow_lt_of_lt_one h0 h1
  refine ⟨n, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩
  rw [map_pow, map_pow]
  exact hn.le

private theorem exists_pow_X_mem {O σ A : Type} [CommRing O] [IsLocalRing O] [CommRing A]
    [Algebra O A] [Algebra.IsIntegral O A] (I : Ideal O)
    (hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I) (π : MvPowerSeries σ O →ₐ[O] A)
    (hπ : Function.Surjective π) (j : σ) :
    ∃ M : ℕ, π (MvPowerSeries.X j) ^ M ∈ I.map (algebraMap O A) := by
  change π (MvPowerSeries.X j) ∈ (I.map (algebraMap O A)).radical
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro (P : Ideal A) ⟨hIP, hP⟩
  have hmax : (Ideal.comap (algebraMap O A) P).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal O ≤ Ideal.comap (algebraMap O A) P := by
      intro c hc
      obtain ⟨n, hn⟩ := hI c hc
      have : c ^ n ∈ Ideal.comap (algebraMap O A) P := (Ideal.map_le_iff_le_comap.1 hIP) hn
      exact (Ideal.comap_isPrime _ P).mem_of_pow_mem n this
    have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_isPrime _ P).ne_top hle
    rw [← this]
    exact IsLocalRing.maximalIdeal.isMaximal O
  have hPm : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P hmax
  have h2 : (Ideal.comap (π : MvPowerSeries σ O →+* A) P).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (π : MvPowerSeries σ O →+* A) hπ
  have h3 := IsLocalRing.eq_maximalIdeal h2
  have h4 : (MvPowerSeries.X j : MvPowerSeries σ O) ∈ IsLocalRing.maximalIdeal _ := by
    intro hu
    rw [MvPowerSeries.isUnit_iff_constantCoeff, MvPowerSeries.constantCoeff_X] at hu
    exact not_isUnit_zero hu
  rw [← h3] at h4
  exact h4

private theorem pow_mem_map {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A]
    [Algebra O B] (I : Ideal O) (e : A →ₐ[O] B) {x : A}
    (h : ∃ M : ℕ, x ^ M ∈ I.map (algebraMap O A)) :
    ∃ M : ℕ, e x ^ M ∈ I.map (algebraMap O B) := by
  obtain ⟨M, hM⟩ := h
  refine ⟨M, ?_⟩
  have := Ideal.mem_map_of_mem (e : A →+* B) hM
  rw [Ideal.map_map, AlgHom.comp_algebraMap, map_pow] at this
  exact this

end SeriesTensor

end GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem SeriesTensor.ev_pt_X {R : Type} [CommRing R] {d : ℕ} (k : Fin 2) (i : Fin d) :
    ev (n := 2) ![pt R d k] (MvPowerSeries.X ((0 : Fin 1), i)) = MvPowerSeries.X (k, i) := by
  unfold ev
  rw [MvPowerSeries.subst_X]
  · rfl
  · refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
    rintro ⟨a, l⟩
    fin_cases a
    exact MvPowerSeries.constantCoeff_X _


open SeriesTensor in
theorem series_two_points_eq_sum_mul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (J : Ideal (PS O 1 d)), Module.Free O (PS O 1 d ⧸ J) → Module.Finite O (PS O 1 d ⧸ J) → ∀ f : PS O 2 d, ∃ (m : ℕ) (g h : Fin m → PS O 1 d), ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → (∀ u ∈ J, φ u = 0) → (∀ u ∈ J, φ' u = 0) → Φ f = ∑ i, φ (g i) * φ' (h i) := by
  intro p _ C _ _ _ v O _ _ hv _ _ d J hfree hfin f
  have hdom : IsDomain O := hv.hom_inj.isDomain _
  have := ValuationRing.of_integers v hv
  set I : Ideal O := Ideal.span {(p : O)}
  have hp0 : algebraMap O C (p : O) ≠ 0 := by
    rw [map_natCast]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hI : ∀ c : O, ¬ IsUnit c → ∃ n : ℕ, c ^ n ∈ I := fun c hc => exists_pow_mem hv hp0 hc
  let Q := PS O 1 d ⧸ J
  let π : PS O 1 d →ₐ[O] Q := Ideal.Quotient.mkₐ O J
  have hπ : Function.Surjective π := Ideal.Quotient.mkₐ_surjective O J
  let A := Q ⊗[O] Q
  have hA : IsAdicComplete (I.map (algebraMap O A)) A := by
    rw [IsAdicComplete.map_algebraMap_iff]
    exact isAdicComplete_of_basis (Module.Free.chooseBasis O A) I
  let e : Fin 2 → (Q →ₐ[O] A) :=
    ![Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]
  let a : Fin 2 × Fin d → A := fun q => e q.1 (π (MvPowerSeries.X (0, q.2)))
  have ha : ∀ q, ∃ M : ℕ, a q ^ M ∈ I.map (algebraMap O A) := fun q =>
    pow_mem_map (A := Q) (B := A) I (e q.1) (exists_pow_X_mem (A := Q) I hI π hπ (0, q.2))
  obtain ⟨Ψ, hΨ⟩ := (mvPowerSeries_eval_of_pow_mem A _ _ a ha).1 hA O
  obtain ⟨m, x, y, hxy⟩ := TensorProduct.exists_sum_tmul_eq (Ψ f)
  choose g hg using fun i => hπ (x i)
  choose h hh using fun i => hπ (y i)
  refine ⟨m, g, h, fun Φ φ φ' h0 h1 hJ hJ' => ?_⟩
  let ψ : Q →ₐ[O] O := Ideal.Quotient.liftₐ J φ hJ
  let ψ' : Q →ₐ[O] O := Ideal.Quotient.liftₐ J φ' hJ'
  let T : A →ₐ[O] O := Algebra.TensorProduct.lift ψ ψ' fun _ _ => Commute.all _ _
  have hsurj : Function.Surjective Φ := fun c => ⟨algebraMap O _ c, Φ.commutes c⟩
  have hnil := fun q => exists_pow_X_mem I hI Φ hsurj q
  have hH : IsHausdorff (I.map (algebraMap O O)) O := by
    rw [IsHausdorff.map_algebraMap_iff]
    infer_instance
  have key := (mvPowerSeries_eval_of_pow_mem O _ _ _ hnil).2 hH O
    (Φ : PS O 2 d →+* O) (T.comp Ψ : PS O 2 d →+* O)
    (fun t => (Φ.commutes t).trans ((T.comp Ψ).commutes t).symm) (fun _ => rfl) (by
      rintro ⟨k, i⟩
      change T (Ψ (MvPowerSeries.X (k, i))) = _
      rw [hΨ, ← ev_pt_X k i]
      fin_cases k
      · refine Eq.trans ?_ (h0 _).symm
        change T (π _ ⊗ₜ 1) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
        rfl
      · refine Eq.trans ?_ (h1 _).symm
        change T (1 ⊗ₜ π _) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
        rfl)
  have hf : Φ f = T (Ψ f) := RingHom.congr_fun key f
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, hxy, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hg, ← hh]
  exact Algebra.TensorProduct.lift_tmul _ _ _ _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SeriesTwoPointsEqSumMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_mul_eval_two_points_of_free_finite_quotient : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (J : Ideal (PS O 1 d)), Module.Free O (PS O 1 d ⧸ J) → Module.Finite O (PS O 1 d ⧸ J) → ∀ f : PS O 2 d, ∃ (m : ℕ) (g h : Fin m → PS O 1 d), ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → (∀ u ∈ J, φ u = 0) → (∀ u ∈ J, φ' u = 0) → Φ f = ∑ i, φ (g i) * φ' (h i) := by
  first | exact @GlobalTheory.series_two_points_eq_sum_mul | exact GlobalTheory.series_two_points_eq_sum_mul | (intros; apply GlobalTheory.series_two_points_eq_sum_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterMemLatticeOfComul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private def latConv {C N : Type} [Field C] [Add N] (φ ψ : (N → C) →ₗ[C] C) :
    (N → C) →ₗ[C] C where
  toFun f := φ (fun x => ψ (fun y => f (x + y)))
  map_add' f g := by
    rw [← map_add (f := _)]; congr 1; funext x
    rw [Pi.add_apply, ← map_add (f := _)]; rfl
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; funext x
    rw [Pi.smul_apply, ← map_smul]; rfl

private theorem latConv_sum {C N : Type} [Field C] [Add N] (φ ψ : (N → C) →ₗ[C] C)
    {m : ℕ} (f : N → C) (g h : Fin m → N → C) (hf : ∀ x y, f (x + y) = ∑ i, g i x * h i y) :
    latConv φ ψ f = ∑ i, φ (g i) * ψ (h i) := by
  have h1 : ∀ x, (fun y => f (x + y)) = ∑ i, g i x • h i := by
    intro x; funext y; simp [hf, Finset.sum_apply]
  have h2 : (fun x => ψ (fun y => f (x + y))) = ∑ i, ψ (h i) • g i := by
    funext x; rw [h1]; simp [Finset.sum_apply, mul_comm]
  change φ (fun x => ψ (fun y => f (x + y))) = _
  rw [h2]; simp [mul_comm]

private theorem lat_bound {C V : Type} [Field C] [AddCommGroup V] [Module C V]
    (v : Valuation C NNReal) (S : Set V) {k : V} (hk : k ∈ Submodule.span C S) :
    ∃ M : NNReal, ∀ φ : V →ₗ[C] C, (∀ f ∈ S, v (φ f) ≤ 1) → v (φ k) ≤ M := by
  induction hk using Submodule.span_induction with
  | mem x hx => exact ⟨1, fun φ hφ => hφ x hx⟩
  | zero => exact ⟨0, fun φ _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨M, hM⟩ := hx
    obtain ⟨M', hM'⟩ := hy
    refine ⟨max M M', fun φ hφ => ?_⟩
    rw [map_add (f := _)]
    exact (v.map_add _ _).trans (max_le_max (hM φ hφ) (hM' φ hφ))
  | smul c x _ hx =>
    obtain ⟨M, hM⟩ := hx
    refine ⟨v c * M, fun φ hφ => ?_⟩
    rw [map_smul, smul_eq_mul, map_mul]
    gcongr
    exact hM φ hφ

private theorem lat_dual {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {N : Type} (A : Submodule O (N → C)) (hfg : A.FG)
    (hsp : Submodule.span C (A : Set (N → C)) = ⊤) (k : N → C)
    (hk : ∀ φ : (N → C) →ₗ[C] C, (∀ f ∈ A, v (φ f) ≤ 1) → v (φ k) ≤ 1) : k ∈ A := by
  classical
  have := hv.hom_inj.isDomain
  have := ValuationRing.of_integers v hv
  have := hv.isFractionRing
  have : Module.Finite O A := Module.Finite.iff_fg.2 hfg
  have : Module.Flat O A := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro ⟨x, hxA⟩ hx
    rw [Submodule.mem_bot]
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hx
    have h' : ((a : O) • x : N → C) = 0 := congrArg Subtype.val ha
    rw [← algebraMap_smul C (a : O) x] at h'
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2))
  have : Module.Free O A := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O A
  let w : Module.Free.ChooseBasisIndex O A → N → C := fun i => (b i : N → C)
  have hR : LinearIndependent O w := b.linearIndependent.map' A.subtype (Submodule.ker_subtype _)
  have hC : LinearIndependent C w := (LinearIndependent.iff_fractionRing O C).1 hR
  have hspR : Submodule.span O (Set.range w) = A := by
    have : Set.range w = A.subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  have hspC : Submodule.span C (Set.range w) = ⊤ := by
    rw [← Submodule.span_span_of_tower O, hspR, hsp]
  let bC := Module.Basis.mk hC (by rw [hspC])
  have hb : ∀ i, bC i = w i := fun i => Module.Basis.mk_apply _ _ _
  have hco : ∀ i, ∀ f ∈ A, v (bC.coord i f) ≤ 1 := by
    intro i f hf
    rw [← hspR] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← hb, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact v.map_add_le hx hy
    | smul c x _ hx =>
      rw [← algebraMap_smul C c x, map_smul, smul_eq_mul, map_mul]
      exact mul_le_one' (hv.map_le_one c) hx
  rw [← bC.sum_repr k]
  refine A.sum_mem fun i _ => ?_
  obtain ⟨o, ho⟩ := hv.exists_of_le_one (hk _ (hco i))
  have ho' : bC.repr k i = algebraMap O C o := ho.symm
  rw [ho', algebraMap_smul, hb]
  exact A.smul_mem _ (b i).2

theorem character_mem_lattice_of_comul : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (N : Type) [AddCommMonoid N] [Finite N] (A : Submodule O (N → C)), A.FG → Submodule.span C (A : Set (N → C)) = ⊤ → (∀ f ∈ A, ∃ (m : ℕ) (g h : Fin m → N → C), (∀ i, g i ∈ A) ∧ (∀ i, h i ∈ A) ∧ ∀ x y, f (x + y) = ∑ i, g i x * h i y) → (∀ f ∈ A, ∃ o : O, algebraMap O C o = f 0) → ∀ κ : N → C, κ 0 = 1 → (∀ x y, κ (x + y) = κ x * κ y) → κ ∈ A := by
  intro C _ v O _ _ hv N _ _ A hfg hsp hco h0 k hk0 hk
  refine lat_dual v hv A hfg hsp k fun φ hφ => ?_
  obtain ⟨M, hM⟩ := lat_bound v (A : Set (N → C)) (k := k) (by rw [hsp]; trivial)
  have hpow : ∀ n : ℕ, ∃ ψ : (N → C) →ₗ[C] C, (∀ f ∈ A, v (ψ f) ≤ 1) ∧ ψ k = φ k ^ n := by
    intro n
    induction n with
    | zero =>
      refine ⟨LinearMap.proj 0, fun f hf => ?_, by simpa using hk0⟩
      obtain ⟨o, ho⟩ := h0 f hf
      rw [LinearMap.proj_apply, ← ho]
      exact hv.map_le_one o
    | succ n ih =>
      obtain ⟨ψ, hψ, hψk⟩ := ih
      refine ⟨latConv ψ φ, fun f hf => ?_, ?_⟩
      · obtain ⟨m, g, h, hg, hh, hf⟩ := hco f hf
        rw [latConv_sum ψ φ f g h hf]
        refine v.map_sum_le fun i _ => ?_
        rw [map_mul]
        exact mul_le_one' (hψ _ (hg i)) (hφ _ (hh i))
      · rw [latConv_sum ψ φ k (fun _ : Fin 1 => k) (fun _ => k) (by simpa using hk)]
        simp [hψk, pow_succ]
  by_contra hlt
  push_neg at hlt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hlt
  obtain ⟨ψ, hψ, hψk⟩ := hpow n
  have := hM ψ hψ
  rw [hψk, map_pow] at this
  exact absurd hn (not_lt.2 this)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterOnTorsionPointsEqSeries
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem character_on_torsion_points_eq_series : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (k : ℕ) (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Killed F.F (p ^ k) φ → Killed F.F (p ^ k) φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, ∀ φ, Killed F.F (p ^ k) φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH k κ hmul hone
  obtain ⟨inst, hsum, hzero, hkill⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  letI := inst
  obtain ⟨hfree, hfin, -⟩ := hFH k
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  haveI : IsDomain O := hinj.isDomain (algebraMap O C)
  set J : Ideal (PS O 1 d) := Ideal.span (Set.range (mulF F.F (p ^ k))) with hJ
  let N : AddSubmonoid (PS O 1 d →ₐ[O] O) :=
    { carrier := {φ | (p ^ k) • φ = 0}
      zero_mem' := nsmul_zero _
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [nsmul_add, ha, hb, add_zero] }
  have hN : ∀ n : N, Killed F.F (p ^ k) n.1 := fun n => (hkill _ _).1 n.2
  have hNJ : ∀ n : N, ∀ u ∈ J, n.1 u = 0 := by
    intro n u hu
    have hle : J ≤ RingHom.ker n.1 := by
      rw [hJ, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact hN n j
    exact hle hu
  let L : N → (QF F.F (p ^ k) →ₐ[O] O) := fun n => Ideal.Quotient.liftₐ J n.1 (hNJ n)
  have hL : ∀ (n : N) (u : PS O 1 d), L n (Ideal.Quotient.mk J u) = n.1 u := fun n u => rfl
  have hLinj : Function.Injective L := by
    intro a b hab
    apply Subtype.ext
    apply AlgHom.ext
    intro u
    rw [← hL, ← hL, hab]
  haveI : Finite N := Finite.of_injective L hLinj
  let T : QF F.F (p ^ k) →ₗ[O] (N → C) :=
    LinearMap.pi fun n => (Algebra.linearMap O C).comp (L n).toLinearMap
  have hmem : ∀ f : N → C, f ∈ LinearMap.range T ↔
      ∃ u : PS O 1 d, ∀ n : N, algebraMap O C (n.1 u) = f n := by
    intro f
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact ⟨u, fun n => rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨Ideal.Quotient.mk J u, funext hu⟩
  have hfg : (LinearMap.range T).FG := Module.Finite.iff_fg.1 inferInstance
  have hspan : Submodule.span C ((LinearMap.range T : Submodule O (N → C)) : Set (N → C)) = ⊤ := by
    let e : N → (PS O 1 d →* C) := fun n =>
      ((algebraMap O C).comp (n.1 : PS O 1 d →+* O) : PS O 1 d →+* C).toMonoidHom
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      apply AlgHom.ext
      intro u
      exact hinj (DFunLike.congr_fun hab u)
    have hli : LinearIndependent C (fun n : N => (e n : PS O 1 d → C)) :=
      (linearIndependent_monoidHom (PS O 1 d) C).comp e he
    have htop := span_flip_eq_top_iff_linearIndependent.2 hli
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨u, rfl⟩
    exact (hmem _).2 ⟨u, fun n => rfl⟩
  have key := GlobalTheory.character_mem_lattice_of_comul C v O hv N (LinearMap.range T) hfg hspan ?_ ?_
    (fun n => κ n.1) (hone _ hzero)
    (fun x y => hmul _ _ _ (hN x) (hN y) ((hsum _ _ _).2 rfl))
  · obtain ⟨u, hu⟩ := (hmem _).1 key
    exact ⟨u, fun φ hφ => hu ⟨φ, (hkill _ _).2 hφ⟩⟩
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    obtain ⟨m, g, h, hgh⟩ := GlobalTheory.T.exists_sum_mul_eval_two_points_of_free_finite_quotient p C v O hv d J hfree hfin (ev (n := 2) ![F.F] u)
    refine ⟨m, fun i n => algebraMap O C (n.1 (g i)), fun i n => algebraMap O C (n.1 (h i)),
      fun i => (hmem _).2 ⟨g i, fun n => rfl⟩, fun i => (hmem _).2 ⟨h i, fun n => rfl⟩, ?_⟩
    intro x y
    obtain ⟨Φ, h0, h1, h2⟩ := (hsum x.1 y.1 (x + y).1).2 rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hu, ← h2, hgh Φ x.1 y.1 h0 h1 (hNJ x) (hNJ y), map_sum]
    simp only [map_mul]
  · intro f hf
    obtain ⟨u, hu⟩ := (hmem _).1 hf
    exact ⟨_, hu 0⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterOnTorsionPointsEqSeriesStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_series_eq_character_on_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (k : ℕ) (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Killed F.F (p ^ k) φ → Killed F.F (p ^ k) φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, ∀ φ, Killed F.F (p ^ k) φ → algebraMap O C (φ u) = κ φ := by
  first | exact @GlobalTheory.character_on_torsion_points_eq_series | exact GlobalTheory.character_on_torsion_points_eq_series | (intros; apply GlobalTheory.character_on_torsion_points_eq_series <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalDiscPointsValuationIntegersStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalDisc_points_valuationIntegers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (κ : Type) [Finite κ], (∀ c : κ → O, (∀ q, ¬ IsUnit (c q)) → ∃! Φ : MvPowerSeries κ O →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q) ∧ (∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f)) ∧ ∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (n : ℕ), ∃ N : ℕ, ∀ f ∈ ((Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* MvPowerSeries κ O) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ O))) ^ N, Φ f ∈ Ideal.span {(p : O) ^ n} := by
  first | exact @GlobalTheory.ChF.formalDisc_points_integers | exact GlobalTheory.ChF.formalDisc_points_integers | (intros; apply GlobalTheory.ChF.formalDisc_points_integers <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfForallPairPointsValuationIntegersStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqZeroOfForallPairPointsValuationIntegers
namespace GlobalTheory.ChF

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section

variable {O : Type} [CommRing O] {d : ℕ}

private theorem exists_algHom_ev (j : Fin 2) : ∃ E : PS O 1 d →ₐ[O] PS O 2 d,
    (∀ u, E u = ev (n := 2) ![pt O d j] u) ∧ ∀ q, E (X q) = X (j, q.2) := by
  have h : HasSubst (fun q : Fin 1 × Fin d => (![pt O d j] : Fin 1 → Pt O 2 d) q.1 q.2) :=
    hasSubst_of_constantCoeff_zero fun q => by simp [pt, Matrix.cons_val_fin_one]
  refine ⟨substAlgHom h, fun u => by rw [coe_substAlgHom]; rfl, fun q => ?_⟩
  rw [coe_substAlgHom, subst_X h]
  simp [pt, Matrix.cons_val_fin_one]

private theorem exists_ringHom_eval {A B σ : Type} [CommRing A] [CommRing B] [Finite σ]
    (J : Ideal B) (hJ : IsAdicComplete J B) (E : A →+* B) (b : σ → B)
    (hb : ∀ q, ∃ M : ℕ, b q ^ M ∈ J) :
    ∃ T : MvPowerSeries σ A →+* B, (∀ u, T (C u) = E u) ∧ ∀ q, T (X q) = b q := by
  letI : Algebra A B := E.toAlgebra
  obtain ⟨T, hT⟩ := (mvPowerSeries_eval_of_pow_mem B J σ b hb).1 hJ A
  exact ⟨T.toRingHom, fun u => T.commutes u, hT⟩

private theorem exists_curry :
    ∃ S : PS O 2 d →ₐ[O] MvPowerSeries (Fin 1 × Fin d) (PS O 1 d), Function.Injective S ∧
      (∀ u, S (ev (n := 2) ![pt O d 0] u) = MvPowerSeries.map (C : O →+* PS O 1 d) u) ∧
      ∀ u, S (ev (n := 2) ![pt O d 1] u) = C u := by
  obtain ⟨E₀, hE₀, hX₀⟩ := exists_algHom_ev (O := O) (d := d) 0
  obtain ⟨E₁, hE₁, hX₁⟩ := exists_algHom_ev (O := O) (d := d) 1
  have hA := (mem_sup_span_X_pow_iff_and_isAdicComplete O ⊥ (Fin 1 × Fin d)).2 inferInstance
  have hP := (mem_sup_span_X_pow_iff_and_isAdicComplete O ⊥ (Fin 2 × Fin d)).2 inferInstance
  have hB := (mem_sup_span_X_pow_iff_and_isAdicComplete (PS O 1 d) _ (Fin 1 × Fin d)).2 hA
  set I : Ideal (PS O 1 d) := (⊥ : Ideal O).map (C : O →+* PS O 1 d) ⊔
    Ideal.span (Set.range (X : Fin 1 × Fin d → PS O 1 d)) with hI
  set J : Ideal (PS O 2 d) := (⊥ : Ideal O).map (C : O →+* PS O 2 d) ⊔
    Ideal.span (Set.range (X : Fin 2 × Fin d → PS O 2 d)) with hJ
  set K : Ideal (MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) := I.map C ⊔
    Ideal.span (Set.range X) with hK
  have hXK : ∀ q : Fin 1 × Fin d, ∃ M : ℕ,
      (X q : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) ^ M ∈ K := fun q =>
    ⟨1, by rw [pow_one]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)⟩
  have hCK : ∀ q : Fin 1 × Fin d, ∃ M : ℕ,
      (C (X q) : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) ^ M ∈ K := fun q =>
    ⟨1, by
      rw [pow_one]
      exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _
        (Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)))⟩
  have hXJ : ∀ q : Fin 2 × Fin d, ∃ M : ℕ, (X q : PS O 2 d) ^ M ∈ J := fun q =>
    ⟨1, by rw [pow_one]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨q, rfl⟩)⟩
  obtain ⟨S, hS⟩ := (mvPowerSeries_eval_of_pow_mem _ K (Fin 2 × Fin d)
    (fun q => if q.1 = 0 then X (0, q.2) else C (X (0, q.2))) fun q => by
      split_ifs
      exacts [hXK _, hCK _]).1 hB O
  have hq : ∀ q : Fin 1 × Fin d, ((0 : Fin 1), q.2) = q := fun q =>
    Prod.ext (Subsingleton.elim _ _) rfl
  have hc : ∀ t : O, algebraMap O (MvPowerSeries (Fin 1 × Fin d) (PS O 1 d)) t = C (C t) :=
    fun t => MvPowerSeries.algebraMap_apply
  have h0 : S.toRingHom.comp E₀.toRingHom = MvPowerSeries.map (C : O →+* PS O 1 d) := by
    refine (mvPowerSeries_eval_of_pow_mem _ K (Fin 1 × Fin d) X hXK).2 inferInstance O _ _
      (fun t => ?_) (fun q => ?_) (fun q => map_X _ q)
    · rw [map_C]
      exact ((S.comp E₀).commutes t).trans (hc t)
    · change S (E₀ (X q)) = _
      rw [hX₀, hS, if_pos rfl, hq]
  have h1 : S.toRingHom.comp E₁.toRingHom = C := by
    refine (mvPowerSeries_eval_of_pow_mem _ K (Fin 1 × Fin d) (fun q => C (X q)) hCK).2
      inferInstance O _ _ (fun t => ?_) (fun q => ?_) (fun q => rfl)
    · exact ((S.comp E₁).commutes t).trans (hc t)
    · change S (E₁ (X q)) = _
      rw [hX₁, hS, if_neg (by simp), hq]
  refine ⟨S, ?_, fun u => ?_, fun u => ?_⟩
  · obtain ⟨T, hTC, hTX⟩ : ∃ T : MvPowerSeries (Fin 1 × Fin d) (PS O 1 d) →+* PS O 2 d,
        (∀ u, T (C u) = E₁ u) ∧ ∀ q, T (X q) = X (0, q.2) :=
      exists_ringHom_eval J hP E₁.toRingHom _ fun q => hXJ _
    have hTS : T.comp S.toRingHom = RingHom.id _ := by
      refine (mvPowerSeries_eval_of_pow_mem _ J (Fin 2 × Fin d) X hXJ).2 inferInstance O _ _
        (fun t => ?_) (fun q => ?_) (fun q => rfl)
      · change T (S (algebraMap O _ t)) = _
        rw [S.commutes, hc]
        exact (hTC (C t)).trans (E₁.commutes t)
      · change T (S (X q)) = _
        obtain ⟨j, i⟩ := q
        rw [hS]
        fin_cases j
        · simp [hTX]
        · simp [hTC, hX₁]
    exact Function.LeftInverse.injective (g := T) fun f => DFunLike.congr_fun hTS f
  · rw [← hE₀]
    exact DFunLike.congr_fun h0 u
  · rw [← hE₁]
    exact DFunLike.congr_fun h1 u

theorem eq_zero_of_forall_pair_points (W : (PS O 1 d →ₐ[O] O) → Prop)
    (hW : ∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) (f : PS O 2 d)
    (hf : ∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O),
      (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) →
        W φ → W φ' → Φ f = 0) : f = 0 := by
  obtain ⟨S, hS, h0, h1⟩ := exists_curry (O := O) (d := d)
  refine hS ?_
  rw [map_zero]
  ext1 e
  rw [map_zero]
  refine hW _ fun φ' hφ' => ?_
  have hC : φ'.toRingHom.comp (C : O →+* PS O 1 d) = RingHom.id O :=
    RingHom.ext fun t => φ'.commutes t
  have key : MvPowerSeries.map φ'.toRingHom (S f) = 0 := by
    refine hW _ fun φ hφ => ?_
    refine hf (φ.comp ((MvPowerSeries.mapAlgHom φ').comp S)) φ φ' (fun u => ?_) (fun u => ?_)
      hφ hφ'
    · change φ (MvPowerSeries.map φ'.toRingHom (S _)) = _
      rw [h0, ← RingHom.comp_apply, ← MvPowerSeries.map_comp, hC, MvPowerSeries.map_id]
      rfl
    · change φ (MvPowerSeries.map φ'.toRingHom (S _)) = _
      rw [h1, map_C]
      exact φ.commutes _
  have := congrArg (coeff e) key
  rwa [coeff_map, map_zero] at this

end

theorem eq_zero_of_forall_pair_points_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (W : (PS O 1 d →ₐ[O] O) → Prop), (∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) → ∀ f : PS O 2 d, (∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → W φ → W φ' → Φ f = 0) → f = 0 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ W hW f hf => eq_zero_of_forall_pair_points W hW f hf

end GlobalTheory.ChF
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_forall_pair_points_valuationIntegers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (W : (PS O 1 d →ₐ[O] O) → Prop), (∀ f : PS O 1 d, (∀ φ, W φ → φ f = 0) → f = 0) → ∀ f : PS O 2 d, (∀ (Φ : PS O 2 d →ₐ[O] O) (φ φ' : PS O 1 d →ₐ[O] O), (∀ u, Φ (ev (n := 2) ![pt O d 0] u) = φ u) → (∀ u, Φ (ev (n := 2) ![pt O d 1] u) = φ' u) → W φ → W φ' → Φ f = 0) → f = 0 := by
  first | exact @GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers | exact GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers | (intros; apply GlobalTheory.ChF.eq_zero_of_forall_pair_points_integers <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsChOfTors
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem apply_eq_zero_of_killed {R : Type} [CommRing R] {d : ℕ} {F : Fin d → PS R 2 d} {N : ℕ}
    {φ : PS R 1 d →ₐ[R] R} (h : Killed F N φ) {f : PS R 1 d}
    (hf : f ∈ Ideal.span (Set.range (mulF F N))) : φ f = 0 := by
  have hle : Ideal.span (Set.range (mulF F N)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact h j
  exact hle hf

private theorem killed_pow_mono {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (p : ℕ) {m n : ℕ}
    (hmn : m ≤ n) {φ : PS R 1 d →ₐ[R] R} (h : Killed F.F (p ^ m) φ) : Killed F.F (p ^ n) φ := by
  intro j
  apply apply_eq_zero_of_killed h
  have hn : p ^ n = p ^ (n - m) * p ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [hn]
  exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow R d F).2.2.1 _ _ (Ideal.subset_span ⟨j, rfl⟩)

private theorem addOf_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  unfold addOf ev
  have h : (fun q : Fin 2 × Fin d => (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) q.1 q.2)
      = MvPowerSeries.X := by
    funext ⟨a, b⟩
    fin_cases a <;> rfl
  rw [h, MvPowerSeries.subst_self]
  rfl

private theorem hasSubst_law {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) :
    MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![F.F] : Fin 1 → Pt R 2 d) q.1 q.2) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  rintro ⟨a, b⟩
  fin_cases a
  exact F.const b

theorem exists_isCh_of_tors : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Tors p F.F φ → Tors p F.F φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, IsCh F.F u ∧ ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH κ hmul hone
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  choose w hw using fun k : ℕ => GlobalTheory.T.exists_series_eq_character_on_torsion p C v O hv d F hFH k κ
    (fun φ φ' ψ h h' hs => hmul φ φ' ψ ⟨k, h⟩ ⟨k, h'⟩ hs) hone
  obtain ⟨hsep, hsepT⟩ := GlobalTheory.T.formalGroup_series_separated_by_torsion p C v O hv d F hFH
  have hsame : ∀ {m n : ℕ}, m ≤ n → ∀ φ, Killed F.F (p ^ m) φ → φ (w m) = φ (w n) := by
    intro m n hmn φ h
    apply hinj
    rw [hw m φ h, hw n φ (killed_pow_mono F p hmn h)]
  set J : Ideal (PS O 1 d) := (Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* PS O 1 d) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS O 1 d)) with hJ
  have hcomp : IsAdicComplete J (PS O 1 d) :=
    (mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2 inferInstance
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → w m ≡ w n [SMOD (J ^ m • ⊤ : Submodule (PS O 1 d) (PS O 1 d))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h1 := hsep m (w m - w n) (fun φ h => by rw [map_sub, hsame hmn φ h, sub_self])
    have h2 : Ideal.span (Set.range (mulF F.F (p ^ m))) ≤ J ^ (m + 1) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact (GlobalTheory.T.mulF_span_mul_le_and_mulF_pow_mem_ideal_pow O d F).2.2.2 p m j
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (h2 h1)
  obtain ⟨u, hu⟩ := hcomp.toIsPrecomplete.prec hcauchy
  have hval : ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
    rintro φ ⟨k, hk⟩
    rw [← hw k φ hk]
    congr 1
    have hH : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
    rw [← sub_eq_zero]
    apply hH.haus
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    obtain ⟨N, hN⟩ := (GlobalTheory.T.formalDisc_points_valuationIntegers p C v O hv (Fin 1 × Fin d)).2.2 φ n
    have h1 := hu (max N k)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := hN _ (Ideal.pow_le_pow_right (le_max_left N k) h1)
    rw [map_sub, ← hsame (le_max_right N k) φ hk] at h2
    rw [← neg_sub]
    exact neg_mem h2
  obtain ⟨inst, hinst⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  letI := inst
  obtain ⟨hsum, hzero, hkill⟩ := hinst
  refine ⟨u, ⟨?_, ?_⟩, hval⟩
  · apply hinj
    rw [← hzero u, hval _ ⟨0, (hkill _ _).1 (smul_zero _)⟩, hone _ hzero, map_one]
  · rw [addOf_pt, ← sub_eq_zero]
    apply GlobalTheory.T.eq_zero_of_forall_pair_points_valuationIntegers p C v O hv d (Tors p F.F) hsepT
    intro Φ φ φ' h0 h1 hφ hφ'
    let ψ : PS O 1 d →ₐ[O] O := Φ.comp (MvPowerSeries.substAlgHom (hasSubst_law F))
    have hψ : ∀ f, Φ (ev (n := 2) ![F.F] f) = ψ f := by
      intro f
      simp only [ψ, AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]
      rfl
    have hs : IsSum F.F φ φ' ψ := ⟨Φ, h0, h1, hψ⟩
    have hT : Tors p F.F ψ := by
      obtain ⟨k, hk⟩ := hφ
      obtain ⟨k', hk'⟩ := hφ'
      refine ⟨max k k', (hkill _ _).1 ?_⟩
      rw [(hsum _ _ _).1 hs, smul_add, (hkill _ _).2 (killed_pow_mono F p (le_max_left k k') hk),
        (hkill _ _).2 (killed_pow_mono F p (le_max_right k k') hk'), add_zero]
    apply hinj
    rw [map_sub, map_mul, hψ, h0, h1, map_sub, map_mul, hval _ hT, hval _ hφ, hval _ hφ',
      hmul _ _ _ hφ hφ' hs, sub_self, map_zero]

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsChOfTorsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCh_eq_character_on_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Tors p F.F φ → Tors p F.F φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, IsCh F.F u ∧ ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
  first | exact @GlobalTheory.ChF.exists_isCh_of_tors | exact GlobalTheory.ChF.exists_isCh_of_tors | (intros; apply GlobalTheory.ChF.exists_isCh_of_tors <;> assumption)
end
