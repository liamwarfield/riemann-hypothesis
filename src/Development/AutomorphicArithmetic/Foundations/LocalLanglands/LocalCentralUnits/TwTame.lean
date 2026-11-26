module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.FinrankK
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TameRecAll

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TwTame
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Zero.LLC

section SlopeTestRemainingChoices

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem val_det_sub_one_lt {g : GL (Fin n) k} (hg : g ∈ KOne k (Fin n)) :
    valuation k ((GeneralLinearGroup.det g : kˣ) - 1 : k) < 1 := by
  classical
  rw [GlobalTheory.StepData.mem_KOne] at hg
  unfold GlobalTheory.StepData.MaxM at hg
  have hint : ∀ i j, (g : Matrix (Fin n) (Fin n) k) i j ∈ 𝒪[k] := by
    intro i j
    have h1 := hg i j
    rw [Matrix.sub_apply] at h1
    have h2 : valuation k ((1 : Matrix (Fin n) (Fin n) k) i j) ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    rw [Valuation.mem_integer_iff]
    calc valuation k ((g : Matrix (Fin n) (Fin n) k) i j)
        = valuation k (((g : Matrix (Fin n) (Fin n) k) i j - (1 : Matrix (Fin n) (Fin n) k) i j)
            + (1 : Matrix (Fin n) (Fin n) k) i j) := by rw [sub_add_cancel]
      _ ≤ max _ _ := Valuation.map_add _ _ _
      _ ≤ 1 := max_le h1.le h2
  let M : Matrix (Fin n) (Fin n) 𝒪[k] := fun i j => ⟨(g : Matrix (Fin n) (Fin n) k) i j, hint i j⟩
  have hdet : ((M.det : 𝒪[k]) : k) = ((GeneralLinearGroup.det g : kˣ) : k) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    have h3 := RingHom.map_det (𝒪[k].subtype) M
    rw [Subring.coe_subtype] at h3
    rw [h3]
    congr 1
  have hres : IsLocalRing.residue 𝒪[k] M.det = IsLocalRing.residue 𝒪[k] 1 := by
    rw [RingHom.map_det, map_one]
    have hM : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
      ext i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
      have h5 : IsLocalRing.residue 𝒪[k] (M i j)
          = IsLocalRing.residue 𝒪[k] (if i = j then 1 else 0) := by
        rw [GlobalTheory.StepData.residue_eq_iff_lt]
        have h6 := hg i j
        rw [Matrix.sub_apply, Matrix.one_apply] at h6
        split_ifs at h6 ⊢ <;> simpa [M] using h6
      rw [h5]
      split_ifs <;> simp
    rw [hM, Matrix.det_one]
  have h4 := (GlobalTheory.StepData.residue_eq_iff_lt _ _).mp hres
  rw [hdet] at h4
  simpa using h4

private theorem fixed_ne_bot {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) {H : Subgroup G} {v : V}
    (hv : v ∈ fixed ρ H) (h0 : v ≠ 0) : fixed σ H ≠ ⊥ := by
  intro hbot
  have hm : e v ∈ fixed σ H := by
    rw [GlobalTheory.Parabolic.mem_fixed] at hv ⊢
    intro u hu
    have := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap u v
    simp only [Representation.Equiv.coe_toIntertwiningMap] at this
    rw [← this, hv u hu]
  rw [hbot, Submodule.mem_bot] at hm
  exact h0 ((map_eq_zero_iff e (EquivLike.injective e)).mp hm)

private def dOf (i₀ : Fin n) (u : kˣ) : GL (Fin n) k :=
  ⟨diagonal (Function.update (fun _ => (1 : k)) i₀ u), diagonal (Function.update (fun _ => (1 : k)) i₀ (u⁻¹ : kˣ)),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h; simp
      · simp [Function.update_of_ne h],
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      by_cases h : i = i₀
      · subst h; simp
      · simp [Function.update_of_ne h]⟩

private theorem det_dOf (i₀ : Fin n) (u : kˣ) : GeneralLinearGroup.det (dOf i₀ u) = u := by
  ext
  simp [dOf, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal, Finset.prod_update_of_mem]

private theorem dOf_mem {i₀ : Fin n} {u : kˣ} (hu : valuation k ((u : k) - 1) < 1) : dOf i₀ u ∈ KOne k (Fin n) := by
  rw [GlobalTheory.StepData.mem_KOne]
  unfold GlobalTheory.StepData.MaxM
  intro i j
  simp only [dOf, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    by_cases h : i = i₀
    · subst h
      simpa using hu
    · simp [Function.update_of_ne h]
  · simp [hij]

private theorem dOf_comm (i₀ : Fin n) (u : kˣ) (μ : Fin n → ℤ) :
    dOf i₀ u * GroundTheory.Automorphic.Cartan.diagPow k n μ = GroundTheory.Automorphic.Cartan.diagPow k n μ * dOf i₀ u := by
  apply Units.ext
  simp only [Units.val_mul, GroundTheory.Automorphic.Cartan.coe_diagPow, dOf, diagonal_mul_diagonal, mul_comm]

end SlopeTestRemainingChoices

private theorem tame_of_dz {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (y : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (h0 : 0 < y.1) (hy : DZ y) (ht : DZ (y.tw χ hχ)) : TameChar χ := by
  classical
  unfold DZ at hy ht
  unfold TameChar
  intro u hu
  by_contra hne
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hy
  have ht' : fixed (twist y.rep (detChar (Fin y.fst) χ)) (KOne k (Fin y.fst)) ≠ ⊥ := by
    obtain ⟨w', hw', hw0'⟩ := (Submodule.ne_bot_iff _).mp ht
    exact fixed_ne_bot (y.twEquiv χ hχ).symm hw' hw0'
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp ht'
  set σ := twist y.rep (detChar (Fin y.fst) χ) with hσ
  set K := KOne k (Fin y.fst) with hK
  let i₀ : Fin y.fst := ⟨0, h0⟩
  have hd : dOf i₀ u ∈ K := dOf_mem hu
  set c : ℂ := ((χ u : ℂˣ) : ℂ) with hc
  have hc0 : c ≠ 0 := Units.ne_zero _
  have hc1 : c⁻¹ - 1 ≠ 0 := by
    intro h
    apply hne
    apply Units.ext
    rw [Units.val_one]
    exact inv_eq_one.mp (sub_eq_zero.mp h)
  have key : ∀ x ∈ fixed σ K, ∀ μ : Fin y.fst → ℤ,
      y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x ∈ twKer y.rep K 1 := by
    intro x hx μ
    rw [GlobalTheory.Parabolic.mem_fixed] at hx
    have hdx : c • y.rep (dOf i₀ u) x = x := by
      have h1 := hx (dOf i₀ u) hd
      rwa [hσ, twist_apply, detChar_apply, det_dOf] at h1
    have hdx' : y.rep (dOf i₀ u) x = c⁻¹ • x := by
      calc y.rep (dOf i₀ u) x = c⁻¹ • (c • y.rep (dOf i₀ u) x) := by
            rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
        _ = c⁻¹ • x := by rw [hdx]
    have hz : y.rep (dOf i₀ u) (y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x)
        = c⁻¹ • y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x := by
      rw [← Module.End.mul_apply, ← map_mul, dOf_comm, map_mul, Module.End.mul_apply, hdx', map_smul]
    have hgen : y.rep (dOf i₀ u) (y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x)
        - (((1 : ↥K →* ℂˣ) ⟨dOf i₀ u, hd⟩ : ℂˣ) : ℂ) • y.rep (GroundTheory.Automorphic.Cartan.diagPow k y.fst μ) x
        ∈ twKer y.rep K 1 := by
      unfold twKer
      exact Submodule.subset_span ⟨⟨dOf i₀ u, hd⟩, _, rfl⟩
    rw [hz, MonoidHom.one_apply, Units.val_one, one_smul] at hgen
    rw [show ∀ z : y.snd.rep.V, c⁻¹ • z - z = (c⁻¹ - 1) • z from
      fun z => by rw [sub_smul, one_smul]] at hgen
    have h2 := Submodule.smul_mem _ (c⁻¹ - 1)⁻¹ hgen
    rwa [smul_smul, inv_mul_cancel₀ hc1, one_smul] at h2
  have hall : ∀ g, y.rep g w ∈ twKer y.rep K 1 := by
    intro g
    obtain ⟨μ, -, k1, hk1, k2, hk2, rfl⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagPow_mul k y.fst g
    rw [← GlobalTheory.CompanionTheory.SphSupp.KO_eq_integralGL] at hk1 hk2
    have hx := GlobalTheory.DepthZeroJac.apply_mem_fixed (π := σ) hw hk2
    have h3 := key _ hx μ
    rw [hσ, twist_apply, map_smul] at h3
    have h4 := Submodule.smul_mem _ (((detChar (Fin y.fst) χ) k2 : ℂˣ) : ℂ)⁻¹ h3
    rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at h4
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact GlobalTheory.DepthZeroJac.apply_mem_twKer_of_normalizer (GlobalTheory.DepthZeroJac.mem_normalizer_KOne hk1) h4
  haveI : y.rep.IsIrreducible := y.snd.rep.irr
  have htop := GroundTheory.Automorphic.SchurOrthogonality.span_orbit_eq_top (π := y.rep) hw0
  have hvk : v ∈ twKer y.rep K 1 := by
    have h5 : v ∈ Submodule.span ℂ (Set.range fun g => y.rep g w) := by
      rw [htop]
      exact Submodule.mem_top
    exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact hall g) h5
  exact hv0 (GlobalTheory.IwahoriInj.eq_zero_of_fixed y.snd.rep.smooth GlobalTheory.DepthZeroJac.isCompact_KOne hv hvk)

private theorem dz_of_tame {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (y : IrrGL (k := k)) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (hy : DZ y) (ht : TameChar χ) : DZ (y.tw χ hχ) := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hy
  refine fixed_ne_bot (y.twEquiv χ hχ) (v := v) (GlobalTheory.Parabolic.mem_fixed.2 fun g hg => ?_) hv0
  have h1 : χ (GeneralLinearGroup.det g) = 1 := ht _ (val_det_sub_one_lt (n := y.1) hg)
  rw [twist_apply, detChar_apply, h1]
  simpa using GlobalTheory.Parabolic.mem_fixed.1 hv g hg

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.twTame :
    UpperTheory.Zero.LLC.TwTame := by
  unfold TwTame
  intro k _ _ _ _ _ y χ hχ h0 hy
  exact ⟨fun ht => tame_of_dz y χ hχ h0 hy ht, fun ht => dz_of_tame y χ hχ hy ht⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeIff
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem restrict_mem_ine {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
    [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
    (A : ValuationSubring Ω) (t : G E' Ω) (ht : t ∈ Ine (F := E') A) :
    AlgEquiv.restrictScalars E t ∈ Ine (F := E) A := by
  refine ⟨?_, fun x hx => ht.2 x hx⟩
  show AlgEquiv.restrictScalars E t • A = A
  have hd : t • A = A := ht.1
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← hd]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact Iff.rfl

end UpperTheory.Zero.LLC

theorem UpperTheory.Zero.LLC.typeIff :
    UpperTheory.Zero.LLC.TypeIff := by
  intro E Ω _ _ _ _ _ A w h rc
  constructor
  · intro H x g _ i hi n hn D R hR θ hθ τ hτ hNm σ hσ hinf
    subst hσ
    have main := H D.E' g D.w' D.h' i hi n hn D.unr D.card D.a' D.ha' D.K D.red D.surj D.ker θ hθ τ hτ hNm σ hinf
    refine ⟨main.1, fun t => ?_⟩
    obtain ⟨t', ht', e⟩ := DiscreteGroups.sglob.DzType.ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
    obtain ⟨x, hx⟩ := DiscreteGroups.sglob.DzType.exists_int_approx_compl D.w' _
      (DiscreteGroups.sglob.DzType.val_artin_ine D.ha' (⟨t', ht'⟩ : Ine (F := D.E') A)).le
    have hne := DiscreteGroups.sglob.DzType.red_ne_zero_of_approx D.ha' D.ker hx
    have hz : R t = Units.mk0 (D.red x) hne := hR t ⟨t', ht'⟩ x _ e.symm rfl hx
    have key := main.2 ⟨t', ht'⟩ x (Units.mk0 _ hne) rfl hx
    rw [hz, ← e]
    exact key
  · intro H E' _ _ _ _ _ _ g _ w' h' i hi n hn unr card a' ha' K _ _ red surj ker θ hθ τ hτ hNm σ hinf
    let D : Ext h g n :=
      { E' := E', w' := w', h' := h', unr := unr, card := card, a' := a', ha' := ha', K := K, red := red,
        surj := surj, ker := ker }
    obtain ⟨R, hR⟩ := (UpperTheory.Zero.LLC.resEx E Ω A w h g i hi n hn D).1
    have main := H (cls σ) g i hi n hn D R hR θ hθ τ hτ hNm σ rfl hinf
    refine ⟨main.1, fun t x z hz hx => ?_⟩
    have hm := restrict_mem_ine (E := E) A (t : G E' Ω) t.2
    have e : R ⟨_, hm⟩ = z := hR ⟨_, hm⟩ t x z rfl hz hx
    have key := main.2 ⟨_, hm⟩
    rw [e] at key
    exact key

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ResBase
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
  GlobalTheory.PRep GlobalTheory.SplitWeil Module ValuativeRel DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Zero.LLC

private theorem base_cong {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E']
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    (g : ℕ) [Fact g.Prime] (n : ℕ) (hn : 0 < n) (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A w')
    (hgv : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (hgv2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2)
    (hgw : ((g : ℕ) : 𝓞 E') ∈ w'.asIdeal) (hgw2 : ((g : ℕ) : 𝓞 E') ∉ w'.asIdeal ^ 2)
    (hvN : normV w = g) (hwN : normV w' = g ^ n)
    (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha' : IsLocalArtin h' a')
    (π : Ω) (hπ : π ^ (g ^ n - 1) = (g : Ω))
    (s : Ine (F := E) A) (t' : Ine (F := E') A) (htt : ∀ z : Ω, (s : G E Ω) z = (t' : G E' Ω) z)
    (y : 𝓞 E) (hy : Valued.v ((a (ineIncl h s) : w.adicCompletion E) - algebraMap E (w.adicCompletion E) (y : E)) < 1)
    (x : 𝓞 E') (hx : Valued.v ((a' (ineIncl h' t') : w'.adicCompletion E') -
      algebraMap E' (w'.adicCompletion E') (x : E')) < 1) :
    A.valuation (algebraMap E Ω (y : E) - algebraMap E' Ω (x : E') ^ ((g ^ n - 1) / (g - 1))) < 1 := by
  have hTR := tameRecAll
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hdvd : (g - 1) ∣ (g ^ n - 1) := by
    simpa using Nat.sub_dvd_pow_sub_pow g 1 n
  set e := (g ^ n - 1) / (g - 1) with he
  have hπE : (π ^ e) ^ (normV w - 1) = (g : Ω) := by
    rw [hvN, ← pow_mul, he, Nat.div_mul_cancel hdvd, hπ]
  have h1 := hTR E Ω g A w h hgv hgv2 a ha (π ^ e) hπE s y hy
  have h2 := hTR E' Ω g A w' h' hgw hgw2 a' ha' π (by rw [hwN]; exact hπ) t' x hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have hπ0 : π ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by have := Nat.one_lt_pow hn.ne' hg1; omega)] at hπ
    exact (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero) hπ.symm
  have e1 : (s : G E Ω) (π ^ e) / π ^ e = ((t' : G E' Ω) π / π) ^ e := by
    rw [map_pow, htt, div_pow]
  rw [e1] at h1
  have hr1 : A.valuation ((t' : G E' Ω) π / π) ≤ 1 := by
    have hd : ((t' : G E' Ω) : G E' Ω) ∈ Dec (F := E') A := Ine_le_Dec A t'.2
    exact (val_ratio hd hπ0).le
  have hx1 : A.valuation (algebraMap E' Ω (x : E')) ≤ 1 := by
    rw [A.valuation_le_one_iff]
    have h3 : IsIntegral ℤ (algebraMap E' Ω (x : E')) := x.2.map (algebraMap E' Ω).toIntAlgHom
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h3.tower_top (A := A))
    exact hz ▸ z.2
  have h3 := cong_pow hr1 hx1 h2 e
  have e2 : algebraMap E Ω (y : E) - algebraMap E' Ω (x : E') ^ e =
      (((t' : G E' Ω) π / π) ^ e - algebraMap E' Ω (x : E') ^ e) - (((t' : G E' Ω) π / π) ^ e - algebraMap E Ω (y : E)) := by
    ring
  rw [e2]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h3 h1)

theorem resBase : ResBase := by
  intro E Ω _ _ _ _ _ A w h a ha g _ i hi n hn D R hR t
  classical
  have hg1 : 1 < g := (Fact.out : g.Prime).one_lt
  have hq : normV w = g := normV_eq_of_padic w g i hi
  have hgw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal := natCast_mem_of_normV w g 1 one_pos (by rw [hq, pow_one])
  have hgw2 : ((g : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2 := g_not_mem_sq w g i hi
  have hgw' : ((g : ℕ) : 𝓞 D.E') ∈ D.w'.asIdeal := natCast_mem_of_normV D.w' g n hn D.card
  obtain ⟨t'0, ht'0, hres⟩ := ine_lift g A w h D.w' D.h' n hn D.unr D.card (t : G E Ω) t.2
  let t' : Ine (F := D.E') A := ⟨t'0, ht'0⟩
  have htt : ∀ z : Ω, (t : G E Ω) z = (t' : G D.E' Ω) z := fun z => by
    show (t : G E Ω) z = t'0 z
    rw [← hres]; rfl
  obtain ⟨x', hx'⟩ := exists_int_approx_compl D.w' _ (val_artin_ine D.ha' t').le
  have hx0 : D.red x' ≠ 0 := red_ne_zero_of_approx D.ha' D.ker hx'
  have hRt : R t = Units.mk0 (D.red x') hx0 := hR t t' x' _ hres.symm rfl hx'

  have hva : Valued.v ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := val_artin_ine ha t
  obtain ⟨xq, hixq⟩ : ∃ xq, i xq = ((a (ineIncl h t) : (w.adicCompletion E)ˣ) : w.adicCompletion E) :=
    ⟨_, RingEquiv.apply_symm_apply i _⟩
  have hnorm1 : ‖xq‖ = 1 := by
    have h1 : ‖i xq‖ ≤ 1 := by rw [hixq, Valued.toNormedField.norm_le_one_iff, hva]
    have h2 : ¬ ‖i xq‖ < 1 := by rw [hixq, Valued.toNormedField.norm_lt_one_iff, hva]; exact lt_irrefl _
    rw [DiscreteGroups.sglob.DzIso.norm_le_iff i hi] at h1
    rw [DiscreteGroups.sglob.DzIso.norm_lt_iff i hi] at h2
    exact le_antisymm h1 (not_lt.mp h2)
  have huqv : (((PadicInt.mkUnits hnorm1 : ℤ_[g]ˣ) : ℤ_[g]) : ℚ_[g]) = xq := PadicInt.mkUnits_eq hnorm1
  refine ⟨PadicInt.mkUnits hnorm1, by rw [huqv, hixq], ?_⟩
  generalize (PadicInt.mkUnits hnorm1 : ℤ_[g]ˣ) = uq at huqv

  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℕ, (a₀ : ZMod g) = PadicInt.toZMod (uq : ℤ_[g]) := ⟨_, ZMod.natCast_zmod_val _⟩
  have happ : Valued.v (((a (ineIncl h t)) : w.adicCompletion E) -
      algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E)) < 1 := by
    have hmem : (uq : ℤ_[g]) - (a₀ : ℤ_[g]) ∈ IsLocalRing.maximalIdeal ℤ_[g] := by
      rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_natCast, ha₀, sub_self]
    have h5 : ‖xq - (a₀ : ℚ_[g])‖ < 1 := by
      have h := (PadicInt.mem_nonunits).mp hmem
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast, huqv] at h
      exact h
    have h6 := val_lt_one_of_norm_lt_one w g i hi _ h5
    rw [map_sub, hixq, map_natCast] at h6
    rw [show algebraMap E (w.adicCompletion E) (((a₀ : 𝓞 E)) : E) = (a₀ : w.adicCompletion E) by simp]
    exact h6

  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hpos : 0 < g ^ n - 1 := by have := Nat.one_lt_pow hn.ne' hg1; omega
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (g : Ω) hpos
  have hb := base_cong g n hn A w h D.w' D.h' hgw hgw2 hgw' D.unr hq D.card a ha D.a' D.ha' π hπ t t' htt
    (a₀ : 𝓞 E) happ x' hx'
  set e := (g ^ n - 1) / (g - 1) with he
  have hmem' : ((a₀ : 𝓞 D.E') - x' ^ e) ∈ D.w'.asIdeal := by
    rw [← D.h']
    have e1 : algebraMap D.E' Ω ((((a₀ : 𝓞 D.E') - x' ^ e : 𝓞 D.E')) : D.E') =
        algebraMap E Ω (((a₀ : 𝓞 E)) : E) - algebraMap D.E' Ω (x' : D.E') ^ e := by
      rw [show ((((a₀ : 𝓞 D.E') - x' ^ e : 𝓞 D.E')) : D.E') = (a₀ : D.E') - (x' : D.E') ^ e by push_cast; ring,
        map_sub, map_pow, map_natCast, show (((a₀ : 𝓞 E)) : E) = (a₀ : E) by push_cast; rfl, map_natCast]
    rw [e1]; exact hb
  have hred : ((a₀ : D.K)) = D.red x' ^ e := by
    have h7 : D.red ((a₀ : 𝓞 D.E') - x' ^ e) = 0 := by rw [← RingHom.mem_ker, D.ker]; exact hmem'
    rw [map_sub, map_pow, map_natCast, sub_eq_zero] at h7
    exact h7
  have hprod : ∏ j ∈ Finset.range n, ((R t ^ g ^ j : D.Kˣ) : D.K) = D.red x' ^ e := by
    rw [hRt]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [Finset.prod_pow_eq_pow_sum, he, Nat.geomSum_eq (Fact.out : g.Prime).two_le]
  rw [hprod, ← hred, ← ha₀, map_natCast]

end UpperTheory.Zero.LLC

end
end
