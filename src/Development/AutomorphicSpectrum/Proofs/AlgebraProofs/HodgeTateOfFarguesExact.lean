module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrasadVolumeSU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeTateCokerSharp
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open TensorProduct GlobalTheory.PDivGroup

def HodgeTateCokerSharp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Algebra ℤ_[p] O], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O → ∀ G : PDivGroup p O,
    ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) →
      ∀ w : G.dual.omega, κ • w ∈ LinearMap.range (hodgeTateLinear G)

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XXgzFarOfExact
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateCokernelSharp
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Farsharp
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpA
noncomputable section

open TensorProduct Coalgebra WithConv GlobalTheory.GroupLikeDerivation

namespace PositivityTheory.HtPt.Farsharp

section Norm

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
  {O : Type} [CommRing O] [Algebra O C] (hO : ∀ o : O, ‖algebraMap O C o‖ ≤ 1)
  {M : Type} [AddCommGroup M] [Module O M]


include hO in
theorem norm_le_of_mem_span (f : M →ₗ[O] C) {s : Set M} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m ∈ s, ‖f m‖ ≤ r) {m : M} (hm : m ∈ Submodule.span O s) : ‖f m‖ ≤ r := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using hr
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul o x _ hx =>
    rw [map_smul, Algebra.smul_def, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hO o)).trans hx


include hO in
theorem bddAbove_norm [Module.Finite O M] (f : M →ₗ[O] C) :
    BddAbove (Set.range fun m => ‖f m‖) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine ⟨∑ m ∈ s, ‖f m‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  refine norm_le_of_mem_span hO f (s := s) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun m hm => Finset.single_le_sum (f := fun m => ‖f m‖) (fun _ _ => norm_nonneg _) hm) ?_
  rw [hs]; trivial

def supN (f : WithConv (M →ₗ[O] C)) : ℝ := ⨆ m, ‖f.ofConv m‖


include hO in
theorem le_supN [Module.Finite O M] (f : WithConv (M →ₗ[O] C)) (m : M) :
    ‖f.ofConv m‖ ≤ supN f := le_ciSup (bddAbove_norm hO f.ofConv) m


omit [IsUltrametricDist C] in
theorem supN_le {f : WithConv (M →ₗ[O] C)} {r : ℝ} (h : ∀ m, ‖f.ofConv m‖ ≤ r) :
    supN f ≤ r := ciSup_le h


omit [IsUltrametricDist C] in
theorem supN_nonneg (f : WithConv (M →ₗ[O] C)) : 0 ≤ supN f :=
  Real.iSup_nonneg fun _ => norm_nonneg _


omit [IsUltrametricDist C] in
theorem supN_smul (c : C) (f : WithConv (M →ₗ[O] C)) :
    supN (c • f) = ‖c‖ * supN f := by
  rw [supN, supN, Real.mul_iSup_of_nonneg (norm_nonneg c)]
  congr 1
  ext m
  rw [← norm_mul]
  rfl


include hO in
theorem supN_add_le [Module.Finite O M] (f g : WithConv (M →ₗ[O] C)) :
    supN (f + g) ≤ max (supN f) (supN g) :=
  supN_le fun m => (IsUltrametricDist.norm_add_le_max (f.ofConv m) (g.ofConv m)).trans
    (max_le_max (le_supN hO f m) (le_supN hO g m))


include hO in
theorem supN_mul_le [Module.Finite O M] [Coalgebra O M]
    (f g : WithConv (M →ₗ[O] C)) : supN (f * g) ≤ supN f * supN g := by
  refine supN_le fun m => ?_
  have h := (Coalgebra.Repr.arbitrary O m).convMul_apply f g
  rw [h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (supN_nonneg _) (supN_nonneg _)) fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_supN hO f _) (le_supN hO g _) (norm_nonneg _) (supN_nonneg _)

theorem supN_le_of_tmul {f : WithConv (M ⊗[O] M →ₗ[O] C)} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ a b, ‖f.ofConv (a ⊗ₜ b)‖ ≤ r) : supN f ≤ r := by
  refine supN_le fun t => ?_
  induction t with
  | tmul a b => exact h a b
  | add x y hx hy =>
    rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)


include hO in
theorem supN_eq_mul [Module.Finite O M] (f g : WithConv (M →ₗ[O] C))
    (h : WithConv (M ⊗[O] M →ₗ[O] C))
    (hh : ∀ a b, h.ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b) :
    supN h = supN f * supN g := by
  apply le_antisymm
  · refine supN_le_of_tmul (mul_nonneg (supN_nonneg _) (supN_nonneg _)) fun a b => ?_
    rw [hh, norm_mul]
    exact mul_le_mul (le_supN hO f _) (le_supN hO g _) (norm_nonneg _) (supN_nonneg _)
  · rw [supN.eq_1 f, Real.iSup_mul_of_nonneg (supN_nonneg g)]
    refine ciSup_le fun a => ?_
    rw [supN.eq_1 g, Real.mul_iSup_of_nonneg (norm_nonneg _)]
    refine ciSup_le fun b => ?_
    rw [← norm_mul, ← hh]
    exact le_supN hO h _


include hO in
theorem exists_supN_pow_le [Module.Finite O M] [Coalgebra O M]
    [IsCocomm O M] {y : WithConv (M →ₗ[O] C)} (hy : IsIntegral O y) :
    ∃ K : ℝ, ∀ k : ℕ, supN (y ^ k) ≤ K := by
  obtain ⟨s, hs⟩ := hy.fg_adjoin_singleton
  refine ⟨∑ f ∈ s, supN f, fun k => supN_le fun m => ?_⟩
  have hk : y ^ k ∈ Submodule.span O (s : Set (WithConv (M →ₗ[O] C))) := by
    rw [hs]
    exact pow_mem (Algebra.self_mem_adjoin_singleton _ y) k
  let ev : WithConv (M →ₗ[O] C) →ₗ[O] C :=
    { toFun := fun f => f.ofConv m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact norm_le_of_mem_span hO ev (Finset.sum_nonneg fun _ _ => supN_nonneg _)
    (fun f hf => (le_supN hO f m).trans
      (Finset.single_le_sum (f := fun f => supN f) (fun _ _ => supN_nonneg _) hf)) hk

end Norm

theorem dvd_mul_of_norm (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (O : Type) [CommRing O] [Algebra O C] (hinj : Function.Injective (algebraMap O C))
    (hO : ∀ x : C, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O C).range)
    (hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range)
    (A : Type) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (q : O) (hq : q ≠ 0) (D : A →ₗ[O] O)
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := O) a * D b -
      Coalgebra.counit (R := O) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem O u → q ∣ D u)
    (c : O) (hc : ‖algebraMap O C c‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) (a : A) :
    q ∣ c * D a := by
  have hO' : ∀ o : O, ‖algebraMap O C o‖ ≤ 1 := fun o => (hO _).2 ⟨o, rfl⟩
  have hq' : algebraMap O C q ≠ 0 := fun h => hq (hinj (by rw [h, map_zero]))
  have hdvd : ∀ x : O, q ∣ x ↔ ‖(algebraMap O C q)⁻¹ * algebraMap O C x‖ ≤ 1 := fun x => by
    constructor
    · rintro ⟨z, rfl⟩
      rw [map_mul, inv_mul_cancel_left₀ hq']
      exact hO' z
    · intro h
      obtain ⟨z, hz⟩ := (hO _).1 h
      refine ⟨z, hinj ?_⟩
      rw [map_mul, hz, mul_inv_cancel_left₀ hq']
  set y : WithConv (A →ₗ[O] C) := (algebraMap O C q)⁻¹ • extendHom O C A (toConv D) with hy
  have hya : ∀ a, y.ofConv a = (algebraMap O C q)⁻¹ * algebraMap O C (D a) := fun _ => rfl
  have : IsScalarTower O C (WithConv (A →ₗ[O] C)) := ⟨fun o x f =>
    WithConv.ext (LinearMap.ext fun a => smul_assoc o x (f.ofConv a))⟩
  have hint : IsIntegral O y :=
    GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul_of_closed (B₀ := GlobalTheory.CartierDual O A) hinj hcl
      (extendHom O C A) (toConv D) q hq fun χ => by
        obtain ⟨u, h1, h2⟩ := exists_isGroupLikeElem χ
        rw [← h2]
        exact hu u h1
  have key := GlobalTheory.T.norm_smul_le_one_of_primitive_bounded_powers C p hp _ _ supN supN (mulHom O C A)
    (inlHom O C A) (inrHom O C A) supN_smul supN_smul supN_nonneg
    supN_nonneg (supN_add_le hO') (supN_mul_le hO')
    (fun f => supN_le fun t => le_supN hO' f _)
    (fun f g => supN_eq_mul hO' f g _ fun a b => by rw [inlHom_mul_inrHom, extProd_tmul])
    y (exists_supN_pow_le hO' hint)
    (supN_le_of_tmul zero_le_one fun a b => by
      have h := (hdvd _).1 (hD a b)
      convert h using 2
      change y.ofConv (a * b) - (extProd y 1).ofConv (a ⊗ₜ b) - (extProd 1 y).ofConv (a ⊗ₜ b) = _
      rw [extProd_tmul, extProd_tmul, hya, hya, hya, LinearMap.convOne_apply,
        LinearMap.convOne_apply]
      simp only [map_sub, map_mul]
      ring)
    (algebraMap O C c) hc
  rw [hdvd]
  have h : (algebraMap O C q)⁻¹ * algebraMap O C (c * D a) = (algebraMap O C c • y).ofConv a := by
    change _ = algebraMap O C c * y.ofConv a
    rw [hya, map_mul]
    ring
  rw [h]
  exact (le_supN hO' _ a).trans key

def powAbs {C : Type} [Field C] (v : Valuation C NNReal) (s : ℝ) (hs : 0 < s) : AbsoluteValue C ℝ where
  toFun x := ((v x : NNReal) : ℝ) ^ s
  map_mul' x y := by
    rw [map_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  nonneg' x := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero (NNReal.coe_nonneg _) hs.ne']
    simp
  add_le' x y := by
    rcases le_max_iff.1 (v.map_add x y) with h | h
    · exact (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg (NNReal.coe_nonneg _) _))
    · exact (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (NNReal.coe_nonneg _) _))

theorem dvd_mul_of_val (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
    (hp : v (p : C) < 1)
    (A : Type) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (q : O) (hq : q ≠ 0) (D : A →ₗ[O] O)
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := O) a * D b -
      Coalgebra.counit (R := O) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem O u → q ∣ D u)
    (c : O) (hc : v (algebraMap O C c) ^ (p - 1) ≤ v (p : C)) (a : A) :
    q ∣ c * D a := by
  have hpp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hp0 : (0 : ℝ) < ((v (p : C) : NNReal) : ℝ) := by
    have : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
    exact NNReal.coe_pos.2 ((Valuation.pos_iff v).2 this)
  have hlog : Real.log ((v (p : C) : NNReal) : ℝ) < 0 := Real.log_neg hp0 (by exact_mod_cast hp)
  let s : ℝ := Real.log p / (-Real.log ((v (p : C) : NNReal) : ℝ))
  have hs : 0 < s := div_pos (Real.log_pos hp1) (neg_pos.2 hlog)
  letI : NormedField C := (powAbs v s hs).toNormedField
  have hn : ∀ x : C, ‖x‖ = ((v x : NNReal) : ℝ) ^ s := fun _ => rfl
  have hpn : ‖(p : C)‖ = (p : ℝ)⁻¹ := by
    rw [hn, Real.rpow_def_of_pos hp0]
    have : Real.log ((v (p : C) : NNReal) : ℝ) * s = -Real.log p := by
      have := hlog.ne
      simp only [s]
      field_simp
    rw [this, Real.exp_neg, Real.exp_log (by linarith)]
  letI : NontriviallyNormedField C :=
    { non_trivial := ⟨(p : C)⁻¹, by rw [norm_inv, hpn, inv_inv]; exact hp1⟩ }
  haveI : IsUltrametricDist C := IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    fun x y => by
      rw [hn, hn, hn]
      rcases le_max_iff.1 (v.map_add x y) with h | h
      · exact le_max_of_le_left
          (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le)
      · exact le_max_of_le_right
          (Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 h) hs.le)
  refine dvd_mul_of_norm C p hpn O hv.hom_inj (fun x => ?_)
    (fun z hz => hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 hz)) A q hq D hD hu c ?_ a
  · rw [hn]
    constructor
    · intro h
      refine hv.exists_of_le_one ?_
      by_contra h1
      exact absurd h (not_le.2 (Real.one_lt_rpow (by exact_mod_cast not_le.1 h1) hs))
    · rintro ⟨o, rfl⟩
      exact Real.rpow_le_one (NNReal.coe_nonneg _) (by exact_mod_cast hv.map_le_one o) hs.le
  · have h1 : ‖algebraMap O C c‖ ^ (p - 1) ≤ (p : ℝ)⁻¹ := by
      rw [← hpn, ← norm_pow, hn, hn, map_pow]
      exact Real.rpow_le_rpow (NNReal.coe_nonneg _) (NNReal.coe_le_coe.2 hc) hs.le
    have h2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have h3 : (((p - 1 : ℕ) : ℝ)) = (p : ℝ) - 1 := by rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
    have h4 := Real.rpow_le_rpow (pow_nonneg (norm_nonneg _) _) h1 (one_div_pos.2 h2).le
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), h3, mul_one_div_cancel h2.ne',
      Real.rpow_one, Real.inv_rpow (by linarith), ← Real.rpow_neg (by linarith)] at h4
    exact h4

end PositivityTheory.HtPt.Farsharp
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.FarsharpB
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

theorem mem_of_forall_dvd {O A : Type} [CommRing O] [IsDomain O] [ValuationRing O] [AddCommGroup A]
    [Module O A] [Module.IsTorsionFree O A] (N : Submodule O A) (hN : N.FG) {q : O} (hq : q ≠ 0)
    (hqN : ∀ a, q • a ∈ N) (x : A)
    (h : ∀ φ : A →ₗ[O] O, (∀ y ∈ N, q ∣ φ y) → q ∣ φ x) : x ∈ N := by
  classical
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hN
  haveI : Module.Flat O N := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2
    (Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance)
  haveI : Module.Free O N := Module.free_of_flat_of_isLocalRing
  let b := Module.Free.chooseBasis O N
  let ψ : A →ₗ[O] N := LinearMap.codRestrict N (q • LinearMap.id) (fun a => hqN a)
  have hψ : ∀ a, (ψ a : A) = q • a := fun a => rfl
  have key : ∀ i, q ∣ b.coord i (ψ x) := by
    intro i
    apply h ((b.coord i).comp ψ)
    intro y hy
    have hy' : ψ y = q • (⟨y, hy⟩ : N) := Subtype.ext (hψ y)
    rw [LinearMap.comp_apply, hy', map_smul, smul_eq_mul]
    exact dvd_mul_right _ _
  choose d hd using key
  let z : N := ∑ i, d i • b i
  have hz : ψ x = q • z := by
    apply b.ext_elem
    intro i
    have := hd i
    simp only [Module.Basis.coord_apply] at this
    simp [z, this, Finset.smul_sum, smul_smul, Finsupp.single_apply]
  have hxz : x = (z : A) := by
    have h1 : q • x = q • (z : A) := by
      rw [← hψ, hz]; rfl
    exact Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hq) h1
  rw [hxz]
  exact z.2

variable {p : ℕ} {O : Type} [CommRing O]

theorem dUnit_mulBy {A : Type} [CommRing A] [Bialgebra O A] [IsCocomm O A] (k : ℕ) (a : A) :
    dUnit (R := O) (mulBy O A k a) = (k : O) • dUnit (R := O) a := by
  rw [← cotMap_d]
  show cotMap ((toConv (BialgHom.id O A) ^ k).ofConv) (dUnit (R := O) a) = _
  rw [cotMap_pow, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  simp [cotMap_id]

theorem dUnit_of_mem_torsionIdeal {A : Type} [CommRing A] [Bialgebra O A] [IsCocomm O A] (k : ℕ)
    {t : A} (ht : t ∈ torsionIdeal (R := O) (A := A) k) : ∃ y, dUnit (R := O) t = (k : O) • y := by
  suffices H : counitAlgHom O A t = 0 ∧ ∃ y, dUnit (R := O) t = (k : O) • y from H.2
  change t ∈ Ideal.span _ at ht
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨?_, dUnit (R := O) a, dUnit_mulBy k a⟩
    have ha' : counitAlgHom O A a = 0 := ha
    simpa using ha'
  | zero => exact ⟨by simp, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨hx0, u, hu⟩ := hx
    obtain ⟨hy0, v, hv⟩ := hy
    exact ⟨by rw [map_add (f := _), hx0, hy0, add_zero], u + v, by simp [hu, hv, smul_add]⟩
  | smul c x _ hx =>
    obtain ⟨hx0, u, hu⟩ := hx
    refine ⟨by rw [smul_eq_mul, map_mul, hx0, mul_zero], counitAlgHom O A c • u, ?_⟩
    show AugCot.d _ (c * x) = _
    rw [AugCot.d_mul, hx0, zero_smul, add_zero]
    change _ • dUnit (R := O) x = _
    rw [hu, smul_comm]

theorem exists_of_cotMap_res_eq_zero (G : PDivGroup p O) (n : ℕ) (y : Cot O (G.A (n + 1)))
    (hy : cotMap (G.res n) y = 0) : ∃ y', y = (p : O) ^ n • y' := by
  unfold cotMap at hy
  obtain ⟨x, hx⟩ := (AugCot.exact_kerMap_map _ _ (G.res_surjective n) y).1 hy
  have hx' : dUnit (R := O) (x : G.A (n + 1)) = y := by
    rw [← hx]
    exact (AugCot.kerMap_apply _ _ x).symm
  have hxmem : (x : G.A (n + 1)) ∈ torsionIdeal (R := O) (A := G.A (n + 1)) (p ^ n) := by
    rw [← G.ker_res n]
    exact x.2
  obtain ⟨y', hy'⟩ := dUnit_of_mem_torsionIdeal (p ^ n) hxmem
  refine ⟨y', ?_⟩
  rw [← hx', ← Nat.cast_pow]
  exact hy'

def lev (G : PDivGroup p O) (n : ℕ) : G.omega →ₗ[O] Cot O (G.A n) :=
  LinearMap.proj n ∘ₗ G.omegaSub.subtype

theorem lev_apply (G : PDivGroup p O) (n : ℕ) (w : G.omega) : lev G n w = w.1 n := rfl

private theorem prime_pow_smul_cot_eq_zero (G : PDivGroup p O) (n : ℕ) (y : Cot O (G.A n)) :
    (p : O) ^ n • y = 0 := by
  obtain ⟨b, rfl⟩ := AugCot.d_surjective _ y
  obtain ⟨a, rfl⟩ := G.res_surjective n b
  set r := counitAlgHom O (G.A (n + 1)) a
  have hmem : mulBy O (G.A (n + 1)) (p ^ n) (a - algebraMap O _ r) ∈ RingHom.ker (G.res n) := by
    rw [G.ker_res n]
    apply Ideal.mem_map_of_mem
    show a - algebraMap O _ r ∈ RingHom.ker (counitAlgHom O (G.A (n + 1)))
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp [r]
  have h2 : G.res n (mulBy O _ (p ^ n) a) = algebraMap O _ r := by
    rw [RingHom.mem_ker] at hmem
    have := hmem
    simp only [map_sub, AlgHomClass.commutes, sub_eq_zero] at this
    exact this
  rw [← Nat.cast_pow]
  change ((p ^ n : ℕ) : O) • dUnit (R := O) (G.res n a) = 0
  rw [← dUnit_mulBy, ← map_mulBy, h2]
  exact AugCot.d_algebraMap _ _

theorem smul_mem_of_levels [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O)
    (L : Submodule O G.omega) (hL : L.FG) (κ : O)
    (hκ : ∀ n (y : Cot O (G.A n)), κ • y ∈ L.map (lev G n))
    (hp : ∀ n (y : Cot O (G.A n)), (p : O) • y ∈ L.map (lev G n)) (w : G.omega) : κ • w ∈ L := by
  classical
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL
  let g : (Fin m → O) →ₗ[O] G.omega := Fintype.linearCombination O s
  have hg : LinearMap.range g = L := by rw [Fintype.range_linearCombination, hs]
  let Φ : (k : ℕ) → (Fin m → O) →ₗ[O] Cot O (G.A k) := fun k => (lev G k).comp g
  have compat : ∀ k (v : G.omega), cotMap (G.res k) (lev G (k + 1) v) = lev G k v := by
    intro k v
    rw [lev_apply, lev_apply]
    exact v.2 k
  have compatΦ : ∀ k c, cotMap (G.res k) (Φ (k + 1) c) = Φ k c := fun k c => compat k (g c)
  have lift : ∀ k (y : Cot O (G.A k)), y ∈ L.map (lev G k) → ∃ c, Φ k c = y := by
    intro k y hy
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hy
    rw [← hg] at hv
    obtain ⟨c, rfl⟩ := hv
    exact ⟨c, rfl⟩
  let W : (k : ℕ) → Cot O (G.A k) := fun k => lev G k w
  have hWc : ∀ k, cotMap (G.res k) (κ • W (k + 1)) = κ • W k := by
    intro k
    rw [map_smul, compat]
  have step : ∀ n (c : {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)}),
      ∃ c' : {c : Fin m → O // Φ (n + 2) c = κ • W (n + 2)},
        ∃ f : Fin m → O, c'.1 = c.1 + (p : O) ^ n • f := by
    intro n c
    obtain ⟨d, hd⟩ := lift (n + 2) _ (hκ (n + 2) (W (n + 2)))
    have hd1 : Φ (n + 1) d = κ • W (n + 1) := by
      rw [← compatΦ, hd, hWc]
    have he : cotMap (G.res (n + 1)) (Φ (n + 2) (d - c.1)) = 0 := by
      rw [compatΦ, map_sub, hd1, c.2, sub_self]
    obtain ⟨y', hy'⟩ := exists_of_cotMap_res_eq_zero G (n + 1) _ he
    obtain ⟨f, hf⟩ := lift (n + 2) _ (hp (n + 2) y')
    refine ⟨⟨c.1 + (p : O) ^ n • f, ?_⟩, f, rfl⟩
    have key : Φ (n + 2) (d - c.1) = Φ (n + 2) ((p : O) ^ n • f) := by
      rw [hy', map_smul, hf, smul_smul, ← pow_succ]
    have : c.1 + (p : O) ^ n • f = d - (d - c.1) + (p : O) ^ n • f := by abel
    rw [this, map_add (f := _), map_sub, key, hd]
    abel
  choose nxt hnxt using step
  obtain ⟨c0, hc0⟩ := lift 1 _ (hκ 1 (W 1))
  let seq : (n : ℕ) → {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)} :=
    fun n => @Nat.rec (fun n => {c : Fin m → O // Φ (n + 1) c = κ • W (n + 1)}) ⟨c0, hc0⟩
      (fun k ck => nxt k ck) n
  have seq_succ : ∀ n, seq (n + 1) = nxt n (seq n) := fun n => rfl
  have diff : ∀ a b, a ≤ b → ∃ t : Fin m → O, (seq b).1 = (seq a).1 + (p : O) ^ a • t := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨0, by simp⟩
    | succ b hab ih =>
      obtain ⟨t, ht⟩ := ih
      obtain ⟨f, hf⟩ := hnxt b (seq b)
      refine ⟨t + (p : O) ^ (b - a) • f, ?_⟩
      rw [seq_succ, hf, ht, smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hab, add_assoc]
  have hpre : ∀ j, ∃ l : O, ∀ n, (seq n).1 j ≡ l [SMOD ((Ideal.span {(p : O)}) ^ n • ⊤ : Submodule O O)] := by
    intro j
    apply IsPrecomplete.prec inferInstance
    intro a b hab
    obtain ⟨t, ht⟩ := diff a b hab
    rw [SModEq.sub_mem, ht]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sub_add_cancel_left, Ideal.mul_top]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) a))
  choose l hl using hpre
  have close : ∀ N, ∃ t : Fin m → O, l = (seq N).1 + (p : O) ^ N • t := by
    intro N
    have : ∀ j, ∃ a : O, a * (p : O) ^ N = l j - (seq N).1 j := by
      intro j
      have h1 := (SModEq.sub_mem.1 (hl j N).symm)
      simp only [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow] at h1
      exact Ideal.mem_span_singleton'.1 h1
    choose t ht using this
    refine ⟨t, funext fun j => ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ht]
    ring
  have good : ∀ n, Φ (n + 1) l = κ • W (n + 1) := by
    intro n
    obtain ⟨t, ht⟩ := close (n + 1)
    have h1 : Φ (n + 1) (seq (n + 1)).1 = κ • W (n + 1) := by
      rw [← compatΦ, (seq (n + 1)).2, hWc]
    rw [ht, map_add (f := _), h1, map_smul, prime_pow_smul_cot_eq_zero, add_zero]
  have good' : ∀ n, Φ n l = κ • W n := by
    intro n
    cases n with
    | zero => rw [← compatΦ, good 0, hWc]
    | succ n => exact good n
  have hgl : g l = κ • w := by
    apply Subtype.ext
    funext k
    have := good' k
    simp only [Φ, W, LinearMap.comp_apply, lev_apply] at this
    rw [this]
    rfl
  rw [← hg, ← hgl]
  exact LinearMap.mem_range_self g l

end PositivityTheory.HtPt.Farsharp
end
end

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace PositivityTheory.HtPt.Farsharp

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
  (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O)
  (hp : v (p : C) < 1)


include hv hp in
theorem smul_dUnit_mem (A : Type) [CommRing A] [Bialgebra O A] [IsCocomm O A] [Module.Finite O A]
    [Module.Projective O A] (hfin : {u : A | IsGroupLikeElem O u}.Finite) (q : O) (hq : q ≠ 0)
    (M : Submodule O (Cot O A)) (hM : ∀ u, IsGroupLikeElem O u → dUnit (R := O) u ∈ M)
    (hqM : ∀ y, q • y ∈ M) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C))
    (y : Cot O A) : κ • y ∈ M := by
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have : ValuationRing O := by
    refine @ValuationRing.mk O _ _ ⟨fun a b => ?_⟩
    rcases le_total (v (algebraMap O C a)) (v (algebraMap O C b)) with h | h
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inr hc.symm⟩
    · obtain ⟨c, hc⟩ := hv.dvd_iff_le.2 h
      exact ⟨c, Or.inl hc.symm⟩
  let ε := counitAlgHom O A
  let π : A →ₗ[O] A := LinearMap.id - Algebra.linearMap O A ∘ₗ ε.toLinearMap
  have hπ : ∀ a, π a = a - algebraMap O A (ε a) := fun _ => rfl
  let μ : A ⊗[O] A →ₗ[O] A := LinearMap.mul' O A ∘ₗ TensorProduct.map π π
  have hμ : ∀ a b, μ (a ⊗ₜ b) = π a * π b := fun a b => by simp [μ]
  let N : Submodule O A := Submodule.span O {u : A | IsGroupLikeElem O u} ⊔
    (LinearMap.range μ ⊔ LinearMap.range (q • (LinearMap.id : A →ₗ[O] A)))
  have hN : N.FG := (Submodule.fg_span hfin).sup ((Submodule.fg_range _).sup (Submodule.fg_range _))
  have hNM : N ≤ M.comap (AugCot.d ε) := by
    refine sup_le (Submodule.span_le.2 hM) (sup_le ?_ ?_)
    · rintro _ ⟨t, rfl⟩
      induction t with
      | tmul a b =>
        have h0 : ∀ a, ε (π a) = 0 := fun a => by rw [hπ]; simp
        rw [Submodule.mem_comap, hμ, AugCot.d_mul, h0, h0, zero_smul, zero_smul, add_zero]
        exact zero_mem _
      | add x y hx hy =>
        change AugCot.d ε (μ (x + y)) ∈ M
        rw [map_add, map_add]
        exact add_mem hx hy
    · rintro _ ⟨a, rfl⟩
      rw [Submodule.mem_comap, LinearMap.smul_apply, map_smul]
      exact hqM _
  obtain ⟨a, rfl⟩ := AugCot.d_surjective _ y
  rw [← map_smul]
  refine hNM (mem_of_forall_dvd N hN hq
    (fun a => Submodule.mem_sup_right (Submodule.mem_sup_right ⟨a, rfl⟩)) _ fun φ hφ => ?_)
  have hu : ∀ u : A, IsGroupLikeElem O u → q ∣ φ u := fun u hu =>
    hφ u (Submodule.mem_sup_left (Submodule.subset_span hu))
  rw [map_smul]
  refine dvd_mul_of_val p C v O hv hp A q hq φ (fun a b => ?_) hu κ hκ a
  have h1 := hφ _ (Submodule.mem_sup_right (Submodule.mem_sup_left ⟨a ⊗ₜ b, rfl⟩))
  have h2 := (hu 1 IsGroupLikeElem.one).mul_left (ε a * ε b)
  have h3 : μ (a ⊗ₜ b) = a * b - ε a • b - ε b • a + (ε a * ε b) • (1 : A) := by
    rw [hμ, hπ, hπ]
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h3, map_add (f := _), map_sub, map_sub, map_smul, map_smul, map_smul] at h1
  exact (dvd_add_left h2).1 h1


include hv hp in
theorem smul_mem_range_dlogLinear [Algebra ℤ_[p] O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (w : G.omega) :
    κ • w ∈ LinearMap.range (dlogLinear G) := by
  have hpp : p.Prime := Fact.out
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩
  have := G.dual.finite_tate C
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap O C) h
    rw [map_natCast, map_zero] at h1
    exact Nat.cast_ne_zero.2 hpp.ne_zero h1
  have : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have key : ∀ κ : O, v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) → ∀ n (y : Cot O (G.A n)),
      κ • y ∈ (LinearMap.range (dlogLinear G)).map (lev G n) := fun κ hκ n y => by
    have hch : ∀ u (hu : IsGroupLikeElem O u),
        charFun O (G.A n) (toConv (evalPoint u hu)) = u := fun u hu =>
      CartierDual.eq_of_forall_apply (R := O) fun φ => apply_charFun _ φ
    have : Finite (CartierDual O (G.A n) →ₐ[O] O) :=
      Nat.finite_of_card_ne_zero ((G.dual.natCard_pts_eq C n).trans_ne (pow_ne_zero _ hpp.ne_zero))
    refine smul_dUnit_mem p C v O hv hp (G.A n)
      ((Set.finite_range fun χ : CartierDual O (G.A n) →ₐ[O] O =>
        charFun O (G.A n) (toConv χ)).subset fun u hu => ⟨_, hch u hu⟩)
      ((p : O) ^ n) (pow_ne_zero _ hp0) _ (fun u hu => ?_)
      (fun y => by rw [pow_smul_cot]; exact zero_mem _) κ hκ y
    obtain ⟨χ, hχ⟩ := G.dual.pt_surjective C n (evalPoint u hu)
    refine ⟨dlog G χ, ⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩, ?_⟩
    rw [lev_apply, dlog_val, ← hch u hu, ← hχ]
    rfl
  refine smul_mem_of_levels G _ (Submodule.fg_range _) κ (key κ hκ) (key p ?_) w
  rw [map_natCast]
  exact pow_le_of_le_one zero_le hp.le (Nat.sub_pos_of_lt hpp.one_lt).ne'

theorem hodgeTateCokerSharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO G κ hκ w
  obtain ⟨z, hz⟩ := smul_mem_range_dlogLinear p C v O hv hp G.dual κ hκ w
  rw [← hz]
  clear hz
  induction z with
  | tmul c χ =>
    obtain ⟨t, rfl⟩ := (tateCongr O G.bidual).surjective χ
    exact ⟨c ⊗ₜ t, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩

end PositivityTheory.HtPt.Farsharp
end
end

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem hodge_tate_cokernel_sharp : GlobalTheory.CompanionTheory.Ar.HT.HodgeTateCokerSharp :=
  PositivityTheory.HtPt.Farsharp.hodgeTateCokerSharp

end GlobalTheory.CompanionTheory.Ar.HT
end

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi

theorem PositivityTheory.Xgn.farguesHodgeTate_of_farguesExact : HT.FarguesExact → HT.FarguesHodgeTate := by
  intro hE p _ C _ _ _ v O _ _ _ hv hp hc G
  refine ⟨fun κ hκ w => HT.hodge_tate_cokernel_sharp p C v O hv hp hc G κ ?_ w, hE p C v O hv hp hc G⟩
  split_ifs at hκ with h2
  · subst h2
    have h4 : (4 : C) = ((2 : ℕ) : C) * ((2 : ℕ) : C) := by norm_num
    rw [h4, map_mul] at hκ
    have h1 : (2 - 1 : ℕ) = 1 := rfl
    rw [h1, pow_one]
    exact hκ.trans (mul_le_of_le_one_left' hp.le)
  · exact hκ
end

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Indef.Tree
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GlobalTheory.CompHt.fintypePsi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_tate_of_fargues_exact : HT.FarguesExact → HT.FarguesHodgeTate := by
  first | exact @PositivityTheory.Xgn.farguesHodgeTate_of_farguesExact | exact PositivityTheory.Xgn.farguesHodgeTate_of_farguesExact
