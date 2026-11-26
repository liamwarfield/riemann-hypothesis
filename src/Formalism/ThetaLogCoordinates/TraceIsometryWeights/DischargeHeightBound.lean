module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.InvInv
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.PolLeISupIsoW
public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.Discharge

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.WeylInt
namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames

section gen

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem wl_pow_coe (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (a b : Fin n) (k : ℕ) (x : U) :
    ((((res G U hU).E a b ^ k) x : U) : V) = (G.E a b ^ k) (x : V) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    exact congrArg (G.E a b) ih

theorem wl_iso_stable (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) : G.Stable (IsoW G W la) :=
  G.gS_stable _

theorem wl_iso_le (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (la : Fin n → ℤ) : IsoW G W la ≤ W :=
  G.gS_le (fun _ hv => hv.2) hW

theorem wl_iso_le_iSup (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) :
    IsoW G W la ≤ ⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)} :=
  G.gS_le (fun v hv => Submodule.mem_iSup_of_mem (⟨v, hv⟩ : {v : V // G.IsHW la v ∧ v ∈ W})
    (G.subset_gS _ (Set.mem_singleton v))) (GlX.iSup_stable G fun _ => G.gS_stable _)

theorem wl_iso_wt (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) {x : V} (hx : x ∈ IsoW G W la)
    {ν : Fin n → ℤ} (hν : ¬ Dle ν la) : G.comp ν x = 0 := by
  refine Submodule.iSup_induction _ (motive := fun x => G.comp ν x = 0) (wl_iso_le_iSup G W la hx)
    (fun v y hy => ?_) (by simp) (fun y z hy hz => by rw [map_add (f := _), hy, hz, add_zero])
  by_contra h
  exact hν (G.wt_le_of_mem v.2.1 hy h)

theorem wl_comp_hw (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) {x : V} (hx : x ∈ IsoW G W la) :
    G.IsHW la (G.comp la x) := by
  refine ⟨G.isWt_comp la x, fun a b hab => ?_⟩
  have e := G.shift a b (la + dl a b) x
  rw [add_sub_cancel_right] at e
  rw [← e]
  refine wl_iso_wt G W la (G.gS_stable _ a b x hx) (fun hle => ?_)
  have := Dle_antisymm hle (Dle_raise la hab)
  exact dl_ne_zero (ne_of_lt hab) (by simpa using this)

theorem wl_comp_comm {U : Type} [AddCommGroup U] [Module K U] (G₁ : GlW K U n) (G₂ : GlW K V n) (θ : U →ₗ[K] V)
    (hθ : ∀ c x, θ (G₁.E c c x) = G₂.E c c (θ x)) (μ : Fin n → ℤ) (x : U) :
    θ (G₁.comp μ x) = G₂.comp μ (θ x) := by
  classical
  have hwt : ∀ ν, G₂.IsWt ν (θ (G₁.comp ν x)) := fun ν => GlX.isWt_of_eig G₂ (fun c => by
    rw [← hθ, G₁.diag, map_smul])
  obtain ⟨S, hS⟩ := G₁.dec x
  have hx' := G₁.sum_comp x (insert μ S) (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_rhs => rw [← hx']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_eq_single μ (fun ν _ hν => by rw [G₂.comp_of_isWt (hwt ν), if_neg (Ne.symm hν)])
    (fun h => absurd (Finset.mem_insert_self μ S) h), G₂.comp_of_isWt (hwt μ), if_pos rfl]

theorem wl_transport (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin n → ℤ}
    {h h' : V} (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    ∃ θ : G.gS {h} →ₗ[K] V, (∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x)) ∧
      (∀ y, θ y ∈ G.gS {h'}) ∧ ∀ m ∈ G.gS {h'}, ∃ y, θ y = m := by
  have hk := GlX.ker_le G hW hWf hh hh' hhW hh'W h0
  refine ⟨GlX.tr G hk ∘ₗ (LinearEquiv.ofEq _ _ (GlX.range_Lv G h).symm).toLinearMap, fun a b x => ?_, fun y => ?_,
    fun m hm => ?_⟩
  · exact GlX.tr_E G hk a b (LinearEquiv.ofEq _ _ (GlX.range_Lv G h).symm x) _
  · rw [← GlX.range_Lv]
    exact GlX.tr_mem G hk _
  · rw [← GlX.range_Lv] at hm
    obtain ⟨c, rfl⟩ := hm
    refine ⟨⟨GlX.Lv G h c, by rw [← GlX.range_Lv]; exact LinearMap.mem_range_self _ c⟩, ?_⟩
    exact GlX.tr_apply G hk c

theorem wl_trace (G : GlW K V n) {la : Fin n → ℤ} {h : V} (hh : G.IsHW la h) (h0 : h ≠ 0)
    [FiniteDimensional K (G.gS {h})] :
    LinearMap.trace K _ ((res G _ (G.gS_stable {h})).comp la) = 1 := by
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have hp : LinearMap.IsProj (K ∙ (⟨h, hmem⟩ : G.gS {h})) ((res G _ (G.gS_stable {h})).comp la) := by
    refine ⟨fun x => ?_, fun x hx => ?_⟩
    · obtain ⟨c, hc⟩ := G.comp_top_of_mem hh x.2
      exact Submodule.mem_span_singleton.mpr ⟨c, Subtype.ext hc.symm⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul]
      congr 1
      exact Subtype.ext hh.1
  rw [hp.trace, finrank_span_singleton (fun e => h0 (congrArg Subtype.val e)), Nat.cast_one]

def topC (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) : IsoW G W la →ₗ[K] V :=
  G.comp la ∘ₗ (IsoW G W la).subtype

theorem wl_key (hNat : InvNat) (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) (l : ℕ) {h : V}
    (hh : G.IsHW la h) (h0 : h ≠ 0) [FiniteDimensional K (G.gS {h})]
    (hSch : ∀ φ : (G.gS {h}) →ₗ[K] (G.gS {h}),
      (∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c φ = 0) →
      InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ =
        (LinearMap.trace K _ φ / (Module.finrank K (G.gS {h}) : K)) • LinearMap.id)
    (θ : G.gS {h} →ₗ[K] V) (hθ : ∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x))
    (hθY : ∀ y, θ y ∈ IsoW G W la) (y : G.gS {h}) :
    InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la) ⟨θ y, hθY y⟩ =
      ((Module.finrank K (G.gS {h}) : K))⁻¹ • θ y := by
  have e1 := hNat K (IsoW G W la →ₗ[K] V) (G.gS {h} →ₗ[K] V) (Fin n)
    (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) (homAct (res G _ (G.gS_stable {h})).E G.E)
    (LinearMap.lcomp K V (θ.codRestrict (IsoW G W la) hθY))
    (fun a b φ => homAct_precomp (res G (IsoW G W la) (wl_iso_stable G W la)).E (res G _ (G.gS_stable {h})).E G.E
      (θ.codRestrict (IsoW G W la) hθY) (fun a b x => Subtype.ext (hθ a b x)) a b φ)
    l (List.finRange n) (topC G W la)
  have e2 := hNat K (G.gS {h} →ₗ[K] G.gS {h}) (G.gS {h} →ₗ[K] V) (Fin n)
    (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) (homAct (res G _ (G.gS_stable {h})).E G.E)
    (LinearMap.llcomp K _ _ V θ)
    (fun a b φ => homAct_postcomp (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E G.E θ hθ a b φ)
    l (List.finRange n) ((res G _ (G.gS_stable {h})).comp la)
  have e3 : LinearMap.lcomp K V (θ.codRestrict (IsoW G W la) hθY) (topC G W la) =
      LinearMap.llcomp K _ _ V θ ((res G _ (G.gS_stable {h})).comp la) := by
    ext x
    exact (wl_comp_comm (res G _ (G.gS_stable {h})) G θ (fun c x => hθ c c x) la x).symm
  have h0' : ∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c
      ((res G _ (G.gS_stable {h})).comp la) = 0 := by
    intro c
    ext x
    rw [homAct_apply, (res G _ (G.gS_stable {h})).diag, (res G _ (G.gS_stable {h})).comp_Ecc, sub_self]
    rfl
  rw [e3, ← e2, hSch _ h0', wl_trace G hh h0, map_smul, one_div] at e1
  exact LinearMap.congr_fun e1 y

end gen

section padic

variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] {n : ℕ}

theorem subset_deltaLat (G : GlW ℚ_[p] V n) (s : Set V) : s ⊆ DeltaLat p G s := by
  intro x hx
  rw [SetLike.mem_coe, DeltaLat, AddSubgroup.mem_sInf]
  exact fun L hL => hL.1 hx

theorem deltaLat_closed (G : GlW ℚ_[p] V n) (s : Set V) : ZpClosed p (DeltaLat p G s) := by
  intro c hc x hx
  rw [DeltaLat, AddSubgroup.mem_sInf] at hx ⊢
  exact fun L hL => hL.2.1 c hc x (hx L hL)

theorem deltaLat_div (G : GlW ℚ_[p] V n) (s : Set V) : DivStable G.E (DeltaLat p G s) := by
  intro a b hab k x hx
  rw [DeltaLat, AddSubgroup.mem_sInf] at hx ⊢
  exact fun L hL => hL.2.2 a b hab k x (hx L hL)

end padic

theorem weylInt_of (hNat : InvNat) (hSchur : SchurTrace) : WeylInt := by
  intro p _ V _ _ n G W M l D la x hx hxM
  by_cases hex : ∃ h, G.IsHW la h ∧ h ∈ W ∧ h ≠ 0
  swap
  · push Not at hex
    have hbot : IsoW G W la ≤ ⊥ := G.gS_le (fun v hv => by
      rw [SetLike.mem_coe, Submodule.mem_bot]; exact hex v hv.1 hv.2) G.bot_stable
    rw [(Submodule.mem_bot _).mp (hbot hx), smul_zero]
    exact AddSubgroup.zero_mem _
  obtain ⟨h, hh, hhW, h0⟩ := hex
  have hUW : G.gS {h} ≤ W := G.gS_le (by simpa using hhW) D.stable
  have := D.fd
  have : FiniteDimensional ℚ_[p] (G.gS {h}) := Submodule.finiteDimensional_of_le hUW
  have hmem : h ∈ G.gS {h} := G.subset_gS {h} rfl
  have : Nontrivial (G.gS {h}) := ⟨⟨⟨h, hmem⟩, 0, fun e => h0 (congrArg Subtype.val e)⟩⟩
  have hfr : (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ_[p]) (M := G.gS {h})).ne'
  set Δ := DeltaLat p G {h | G.IsHW la h ∧ h ∈ W ∧ h ∈ M} with hΔ
  have hΔZ : ZpClosed p Δ := deltaLat_closed p G _
  have hΔD : DivStable G.E Δ := deltaLat_div p G _

  have hid : ∀ z : IsoW G W la,
      InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la) z =
        ((Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]))⁻¹ • (z : V) := by
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        Submodule.map (IsoW G W la).subtype (LinearMap.eqLocus
          (InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la))
          (((Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]))⁻¹ • (IsoW G W la).subtype)) := by
      refine iSup_le fun v m hm => ?_
      obtain ⟨θ, hθ, hθm, hsur⟩ := wl_transport G D.stable D.finW hh v.2.1 hhW v.2.2 h0
      have hvY : G.gS {(v : V)} ≤ IsoW G W la :=
        G.gS_le (by
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact G.subset_gS _ v.2) (G.gS_stable _)
      obtain ⟨y, rfl⟩ := hsur m hm
      exact ⟨⟨θ y, hvY (hθm y)⟩, wl_key hNat G W la l hh h0
        (fun φ hφ => hSchur ℚ_[p] V n G W l D.stable D.fd D.finW D.bound la h hh hhW h0 φ hφ) θ hθ
        (fun y => hvY (hθm y)) y, rfl⟩
    intro z
    obtain ⟨z', hz', hzz⟩ := hle (wl_iso_le_iSup G W la z.2)
    have : z' = z := Subtype.ext hzz
    rw [← this]
    exact hz'

  have hLd : DivStable (res G (IsoW G W la) (wl_iso_stable G W la)).E (M.comap (IsoW G W la).subtype.toAddMonoidHom) := by
    intro a b hab j y hy
    show ((((j.factorial : ℚ_[p]))⁻¹ • ((res G (IsoW G W la) (wl_iso_stable G W la)).E a b ^ j) y : IsoW G W la) : V) ∈ M
    rw [Submodule.coe_smul, wl_pow_coe]
    exact D.div a b hab j _ hy
  obtain ⟨hHZ, hHD⟩ := hom_divided_holds p (IsoW G W la) V (Fin n) (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E
    (M.comap (IsoW G W la).subtype.toAddMonoidHom) Δ hΔZ hLd hΔD
  have hrel := hom_relation_holds ℚ_[p] (IsoW G W la) V (Fin n) (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E
    (glRel_of (res G (IsoW G W la) (wl_iso_stable G W la))) (glRel_of G)
  have hφ : topC G W la ∈ HomLat (K := ℚ_[p]) (M.comap (IsoW G W la).subtype.toAddMonoidHom) Δ := by
    intro y hy
    exact subset_deltaLat p G _ ⟨wl_comp_hw G W la y.2,
      G.graded_of D.stable la _ (wl_iso_le G D.stable la y.2), D.graded la _ hy⟩
  have h2 := invariant_integral_holds p _ (Fin n) _ hrel _ hHZ hHD l (List.finRange n) (List.nodup_finRange n) _ hφ
  rw [List.length_finRange] at h2
  have h3 := h2 ⟨x, hx⟩ hxM
  rw [LinearMap.smul_apply, hid] at h3
  have h4 := hΔZ (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p])
    (by simpa using Padic.norm_int_le_one (p := p) (Module.finrank ℚ_[p] (G.gS {h}) : ℤ)) _ h3
  rwa [smul_comm, smul_smul (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]), mul_inv_cancel₀ hfr, one_smul] at h4

theorem weyl_integral_holds : WeylInt := weylInt_of invariant_natural_holds (schurTrace_of invariant_inverse_holds)

end Formalism.InvariantFactorPaths.PW
end

section -- merged from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.LatticeBasisPolynomial
namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M

namespace LatticeBasis

variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem mem_intPol_iff (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by
  constructor
  · rintro ⟨f0, rfl⟩ m
    simp only [AlgHom.toLinearMap_apply, mapAlgHom_apply, coeff_map]
    exact PadicInt.norm_le_one (AddMonoidAlgebra.coeff f0 m)
  · intro h
    have : (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
      intro a ha
      rw [Finset.mem_coe, mem_coeffs_iff] at ha
      obtain ⟨m, _, rfl⟩ := ha
      exact ⟨⟨x.coeff m, h m⟩, rfl⟩
    rw [← mem_range_map_iff_coeffs_subset] at this
    simpa [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply, mapAlgHom_apply, Set.mem_range] using this

theorem exists_unit_coeff (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (hU : U ≠ ⊥) :
    ∃ x₀ ∈ U, ∃ m, x₀.coeff m = 1 ∧ x₀ ∈ IntPol p σ := by
  obtain ⟨x, hxU, hx0⟩ := (Submodule.ne_bot_iff U).mp hU
  have hne : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hx0 (support_eq_empty.mp h)
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image x.support (fun m => ‖x.coeff m‖) hne
  have ha : x.coeff m ≠ 0 := mem_support_iff.mp hm
  refine ⟨(x.coeff m)⁻¹ • x, U.smul_mem _ hxU, m, ?_, ?_⟩
  · rw [coeff_smul, smul_eq_mul, inv_mul_cancel₀ ha]
  · rw [mem_intPol_iff]
    intro n
    rw [coeff_smul, smul_eq_mul, norm_mul, norm_inv]
    have hpos : 0 < ‖x.coeff m‖ := norm_pos_iff.mpr ha
    rw [inv_mul_le_iff₀ hpos, mul_one]
    by_cases hn : n ∈ x.support
    · exact hmax n hn
    · rw [notMem_support_iff.mp hn, norm_zero]
      exact hpos.le

theorem exists_family (d : ℕ) : ∀ (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])), FiniteDimensional ℚ_[p] U →
    Module.finrank ℚ_[p] U = d →
    ∃ (k : ℕ) (b : Fin k → MvPolynomial σ ℚ_[p]), LinearIndependent ℚ_[p] b ∧
      Submodule.span ℚ_[p] (Set.range b) = U ∧ (∀ i, b i ∈ IntPol p σ) ∧
      ∀ x ∈ U, x ∈ IntPol p σ → ∃ c : Fin k → ℚ_[p], (∀ i, ‖c i‖ ≤ 1) ∧ x = ∑ i, c i • b i := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hfd hd
    by_cases hU : U = ⊥
    · subst hU
      refine ⟨0, Fin.elim0, linearIndependent_empty_type, by simp, fun i => i.elim0, ?_⟩
      intro x hx _
      exact ⟨Fin.elim0, fun i => i.elim0, by simpa using hx⟩
    · obtain ⟨x₀, hx₀U, m, hm1, hx₀I⟩ := exists_unit_coeff U hU
      set U' : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p]) := U ⊓ LinearMap.ker (lcoeff ℚ_[p] m) with hU'
      have hle : U' ≤ U := inf_le_left
      have hx₀U' : x₀ ∉ U' := by
        intro h
        have : x₀.coeff m = 0 := by simpa using (Submodule.mem_inf.mp h).2
        rw [hm1] at this
        exact one_ne_zero this
      have hlt : U' < U := lt_of_le_of_ne hle (fun h => hx₀U' (h ▸ hx₀U))
      have hfd' : FiniteDimensional ℚ_[p] U' := Submodule.finiteDimensional_of_le hle
      have hrk : Module.finrank ℚ_[p] U' < d := hd ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨k, b, hli, hsp, hbI, hco⟩ := ih _ hrk U' hfd' rfl
      have hsplit : ∀ x ∈ U, x - x.coeff m • x₀ ∈ U' := by
        intro x hx
        refine Submodule.mem_inf.mpr ⟨U.sub_mem hx (U.smul_mem _ hx₀U), ?_⟩
        simp [hm1]
      refine ⟨k + 1, Fin.cons x₀ b, ?_, ?_, ?_, ?_⟩
      · rw [linearIndependent_finCons]
        exact ⟨hli, by rw [hsp]; exact hx₀U'⟩
      · rw [Fin.range_cons, Submodule.span_insert, hsp]
        apply le_antisymm
        · exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₀U) hle
        · intro x hx
          have : x = x.coeff m • x₀ + (x - x.coeff m • x₀) := by abel
          rw [this]
          exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)) (hsplit x hx)
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx₀I
        · simpa using hbI j
      · intro x hx hxI
        have hc : ‖x.coeff m‖ ≤ 1 := (mem_intPol_iff x).mp hxI m
        have hI' : x - x.coeff m • x₀ ∈ IntPol p σ := by
          rw [mem_intPol_iff]
          intro n
          rw [coeff_sub, coeff_smul, smul_eq_mul, sub_eq_add_neg]
          refine (Padic.nonarchimedean _ _).trans (max_le ((mem_intPol_iff x).mp hxI n) ?_)
          rw [norm_neg, norm_mul]
          exact mul_le_one₀ hc (norm_nonneg _) ((mem_intPol_iff x₀).mp hx₀I n)
        obtain ⟨c, hc1, hxc⟩ := hco _ (hsplit x hx) hI'
        refine ⟨Fin.cons (x.coeff m) c, ?_, ?_⟩
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hc
          · simpa using hc1 j
        · rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          rw [← hxc]
          abel

end LatticeBasis

theorem lattice_basis_polynomial : LatBasisPol := by
  intro p _ σ U hfd
  obtain ⟨k, b, hli, hsp, hbI, hco⟩ := LatticeBasis.exists_family (p := p) (σ := σ) _ U hfd rfl
  subst hsp
  refine ⟨k, Module.Basis.span hli, ?_, ?_⟩
  · intro i
    rw [Module.Basis.span_apply]
    exact hbI i
  · intro x hx i
    obtain ⟨c, hc1, hxc⟩ := hco x.1 x.2 hx
    have hx' : x = ∑ j, c j • Module.Basis.span hli j := by
      apply Subtype.ext
      rw [hxc]
      simp [Module.Basis.span_apply]
    rw [hx', Module.Basis.repr_sum_self]
    exact hc1 i

end Formalism.InvariantFactorPaths.PW
end

section -- merged from Formalism.ThetaLogCoordinates.TraceIsometryWeights.SchurTraceProofs.TypeInt
namespace Formalism.InvariantFactorPaths.PW

open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames

section gen

variable {K U V : Type} [Field K] [CharZero K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}

theorem glRel_ofT (G : GlW K V n) : GlRel G.E := by
  intro a b c d
  ext x
  have hx := G.comm a b c d x
  split_ifs at hx ⊢ <;> simpa using hx

def pr0 (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) : Module.End K (U →ₗ[K] V) :=
  ∑ ν ∈ S, postC (G₂.comp ν) * preC (G₁.comp ν)

theorem scalar_projection_apply (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (φ : U →ₗ[K] V) (x : U) :
    pr0 G₁ G₂ S φ x = ∑ ν ∈ S, G₂.comp ν (φ (G₁.comp ν x)) := by
  simp [pr0, postC_apply, preC_apply]

theorem weightZeroProj_weight (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (φ : U →ₗ[K] V) (c : Fin n) :
    homAct G₁.E G₂.E c c (pr0 G₁ G₂ S φ) = 0 := by
  ext x
  have hd : dl c c = 0 := sub_self _
  change G₂.E c c (pr0 G₁ G₂ S φ x) - pr0 G₁ G₂ S φ (G₁.E c c x) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [scalar_projection_apply, scalar_projection_apply, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [G₂.diag, G₁.shift, hd, sub_zero, G₁.diag, map_smul, map_smul]

theorem weightZeroProj_mem (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) {W : Submodule K V} (hW : G₂.Graded W)
    {φ : U →ₗ[K] V} (hφ : ∀ x, φ x ∈ W) (x : U) : pr0 G₁ G₂ S φ x ∈ W := by
  rw [scalar_projection_apply]
  exact Submodule.sum_mem _ fun ν _ => hW ν _ (hφ _)

theorem weightZeroProj_mem_homLat (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) {L : AddSubgroup U} {M : AddSubgroup V}
    (hL : ∀ μ, ∀ x ∈ L, G₁.comp μ x ∈ L) (hM : ∀ μ, ∀ x ∈ M, G₂.comp μ x ∈ M)
    {φ : U →ₗ[K] V} (hφ : φ ∈ HomLat (K := K) L M) : pr0 G₁ G₂ S φ ∈ HomLat (K := K) L M := by
  have hφ' : ∀ x ∈ L, φ x ∈ M := hφ
  show ∀ x ∈ L, pr0 G₁ G₂ S φ x ∈ M
  intro x hx
  rw [scalar_projection_apply]
  exact AddSubgroup.sum_mem _ fun ν _ => hM ν _ (hφ' _ (hL ν x hx))

theorem comp_comm2 (G₁ : GlW K U n) (G₂ : GlW K V n) (θ : U →ₗ[K] V)
    (hθ : ∀ c x, θ (G₁.E c c x) = G₂.E c c (θ x)) (μ : Fin n → ℤ) (x : U) :
    θ (G₁.comp μ x) = G₂.comp μ (θ x) := by
  have hw : ∀ ν, G₂.comp ν (θ (G₁.comp ν x)) = θ (G₁.comp ν x) := fun ν =>
    GlX.isWt_of_eig (G := G₂) (fun c => by rw [← hθ, G₁.diag, map_smul])
  obtain ⟨S, hS⟩ := G₁.dec x
  have hx : ∑ ν ∈ insert μ S, G₁.comp ν x = x :=
    G₁.sum_comp x _ (fun ν hν => hS ν (fun h => hν (Finset.mem_insert_of_mem h)))
  conv_rhs => rw [← hx]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_eq_single μ]
  · exact (hw μ).symm
  · intro ν _ hne
    rw [← hw ν, G₂.idem, if_neg (Ne.symm hne)]
  · intro h
    exact absurd (Finset.mem_insert_self μ S) h

theorem weightZeroProj_comp (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (θ : U →ₗ[K] V)
    (hθ : ∀ μ x, θ (G₁.comp μ x) = G₂.comp μ (θ x)) (φ : U →ₗ[K] U) :
    pr0 G₁ G₂ S (θ ∘ₗ φ) = θ ∘ₗ pr0 G₁ G₁ S φ := by
  ext x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, scalar_projection_apply, map_sum, hθ]

theorem weightZeroProj_trace (G₁ : GlW K U n) (S : Finset (Fin n → ℤ)) (hS : ∀ x, ∀ μ ∉ S, G₁.comp μ x = 0) (φ : U →ₗ[K] U) :
    LinearMap.trace K U (pr0 G₁ G₁ S φ) = LinearMap.trace K U φ := by
  classical
  have hsum : ∑ ν ∈ S, G₁.comp ν = 1 := by
    ext x
    simpa using G₁.sum_comp x S (hS x)
  have hidem : ∀ ν, G₁.comp ν * G₁.comp ν = G₁.comp ν := by
    intro ν
    ext x
    simp [G₁.idem]
  have hp : pr0 G₁ G₁ S φ = ∑ ν ∈ S, G₁.comp ν * (φ * G₁.comp ν) := by
    ext x
    simp [scalar_projection_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hp, map_sum]
  calc ∑ ν ∈ S, LinearMap.trace K U (G₁.comp ν * (φ * G₁.comp ν))
      = ∑ ν ∈ S, LinearMap.trace K U (φ * G₁.comp ν) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [LinearMap.trace_mul_comm, mul_assoc, hidem ν]
    _ = LinearMap.trace K U φ := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, ← Finset.mul_sum, hsum, mul_one]

def Psi (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) : Module.End K (U →ₗ[K] V) :=
  InvOp (homAct G₁.E G₂.E) l (List.finRange n) * pr0 G₁ G₂ S

noncomputable def QQ (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) : V →ₗ[K] V :=
  (k : K) • ∑ i, LinearMap.applyₗ (b i) ∘ₗ Psi G₁ G₂ S l ∘ₗ LinearMap.smulRightₗ (b.coord i)

theorem QQ_apply (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) (m : V) :
    QQ G₁ G₂ S l b m = (k : K) • ∑ i, Psi G₁ G₂ S l ((b.coord i).smulRight m) (b i) := by
  simp only [QQ, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.smulRightₗ_apply, LinearMap.applyₗ_apply_apply]

theorem QQ_zero (hHom : HomInv) (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) {W : Submodule K V} (hW : G₂.Stable W) (hb : WtBound2 G₁ G₂ W l)
    (h0 : ∀ ψ : U →ₗ[K] V, (∀ a b x, ψ (G₁.E a b x) = G₂.E a b (ψ x)) → (∀ x, ψ x ∈ W) → ψ = 0)
    {m : V} (hm : m ∈ W) : QQ G₁ G₂ S l b m = 0 := by
  rw [QQ_apply]
  have hWg : G₂.Graded W := G₂.graded_of hW
  have hz : ∀ i, Psi G₁ G₂ S l ((b.coord i).smulRight m) = 0 := by
    intro i
    have hφW : ∀ x, pr0 G₁ G₂ S ((b.coord i).smulRight m) x ∈ W := fun x =>
      weightZeroProj_mem G₁ G₂ S hWg (fun y => by rw [LinearMap.smulRight_apply]; exact W.smul_mem _ hm) x
    obtain ⟨h1, h2, -⟩ := hHom K U V n G₁ G₂ W l hW hb _ hφW (weightZeroProj_weight G₁ G₂ S _)
    exact h0 _ h1 h2
  simp [hz]

theorem QQ_id (hNat : InvNat) (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) K U) (hS : ∀ x, ∀ μ ∉ S, G₁.comp μ x = 0)
    (hSch : ∀ φ : U →ₗ[K] U, (∀ c, homAct G₁.E G₁.E c c φ = 0) →
      InvOp (homAct G₁.E G₁.E) l (List.finRange n) φ = (LinearMap.trace K U φ / (k : K)) • LinearMap.id)
    (hk : k ≠ 0) (θ : U →ₗ[K] V) (hθ : ∀ a b x, θ (G₁.E a b x) = G₂.E a b (θ x)) (y : U) :
    QQ G₁ G₂ S l b (θ y) = θ y := by
  have hk' : (k : K) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hθc : ∀ μ x, θ (G₁.comp μ x) = G₂.comp μ (θ x) := fun μ x =>
    comp_comm2 G₁ G₂ θ (fun c x => hθ c c x) μ x
  let θ' : (U →ₗ[K] U) →ₗ[K] (U →ₗ[K] V) :=
    { toFun := fun χ => θ ∘ₗ χ
      map_add' := fun χ ψ => by ext x; simp
      map_smul' := fun c χ => by ext x; simp }
  have hθ'a : ∀ χ, θ' χ = θ ∘ₗ χ := fun χ => rfl
  have hcomm : ∀ a b χ, θ' (homAct G₁.E G₁.E a b χ) = homAct G₁.E G₂.E a b (θ' χ) := fun a b χ => by
    rw [hθ'a, hθ'a]
    exact homAct_postcomp G₁.E G₁.E G₂.E θ hθ a b χ
  have htr : ∀ i, LinearMap.trace K U ((b.coord i).smulRight y) = b.coord i y := by
    intro i
    rw [LinearMap.trace_eq_matrix_trace K b, Matrix.trace]
    simp [LinearMap.toMatrix_apply, Finsupp.single_apply]
    simp [Matrix.vecMulVec_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have key : ∀ i, Psi G₁ G₂ S l ((b.coord i).smulRight (θ y)) (b i) = (b.coord i y / (k : K)) • θ (b i) := by
    intro i
    have h1 : (b.coord i).smulRight (θ y) = θ' ((b.coord i).smulRight y) := by
      ext x
      simp [hθ'a]
    have h2 : Psi G₁ G₂ S l (θ' ((b.coord i).smulRight y)) =
        θ' (InvOp (homAct G₁.E G₁.E) l (List.finRange n) (pr0 G₁ G₁ S ((b.coord i).smulRight y))) := by
      have hp : pr0 G₁ G₂ S (θ' ((b.coord i).smulRight y)) = θ' (pr0 G₁ G₁ S ((b.coord i).smulRight y)) :=
        weightZeroProj_comp G₁ G₂ S θ hθc _
      show InvOp (homAct G₁.E G₂.E) l (List.finRange n) (pr0 G₁ G₂ S (θ' ((b.coord i).smulRight y))) = _
      rw [hp]
      exact (hNat K _ _ (Fin n) (homAct G₁.E G₁.E) (homAct G₁.E G₂.E) θ' hcomm l (List.finRange n) _).symm
    rw [h1, h2, hSch _ (weightZeroProj_weight G₁ G₁ S _), weightZeroProj_trace G₁ S hS, hθ'a, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_apply, map_smul, htr]
  have hsc : ∀ i, (k : K) • ((b.coord i y / (k : K)) • θ (b i)) = θ (b.repr y i • b i) := by
    intro i
    have hc : (k : K) * (b.coord i y / (k : K)) = b.repr y i := by
      rw [Module.Basis.coord_apply]
      field_simp
    rw [smul_smul, hc, map_smul]
  rw [QQ_apply, Finset.smul_sum]
  simp_rw [key, hsc]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, b.sum_repr]

end gen

section iso

variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem res_E_coe (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (a b : Fin n) (x : U) :
    (((res G U hU).E a b x : U) : V) = G.E a b (x : V) := rfl

theorem res_comp_coe (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (μ : Fin n → ℤ) (x : U) :
    (((res G U hU).comp μ x : U) : V) = G.comp μ (x : V) := rfl

theorem res_pow_coe (G : GlW K V n) (U : Submodule K V) (hU : G.Stable U) (a b : Fin n) (k : ℕ) (x : U) :
    ((((res G U hU).E a b ^ k) x : U) : V) = (G.E a b ^ k) (x : V) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ']
    show (((res G U hU).E a b (((res G U hU).E a b ^ k) x) : U) : V) = G.E a b ((G.E a b ^ k) (x : V))
    rw [res_E_coe, ih]

theorem IsoW_le (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (la : Fin n → ℤ) : IsoW G W la ≤ W := G.gS_le (fun v hv => (show G.IsHW la v ∧ v ∈ W from hv).2) hW

theorem IsoW_le_iSup (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) :
    IsoW G W la ≤ ⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)} := by
  refine G.gS_le (fun v hv => ?_) ?_
  · exact (le_iSup (fun v : {v : V // G.IsHW la v ∧ v ∈ W} => G.gS {(v : V)}) ⟨v, hv⟩)
      (G.subset_gS _ (Set.mem_singleton v))
  · intro a b x hx
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}).comap (G.E a b) :=
      iSup_le fun i y hy =>
        (le_iSup (fun v : {v : V // G.IsHW la v ∧ v ∈ W} => G.gS {(v : V)}) i) (G.gS_stable _ a b y hy)
    exact hle hx

theorem hw_IsoW_zero (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la mu : Fin n → ℤ}
    (hne : mu ≠ la) {x : V} (hx : G.IsHW la x) (hxI : x ∈ IsoW G W mu) : x = 0 := by
  by_contra hx0
  have hxw : G.comp la x = x ∧ ∀ a b, a < b → G.E a b x = 0 := hx
  have hbot : G.Stable (⊥ : Submodule K V) := by
    intro a b y hy
    rw [Submodule.mem_bot] at hy ⊢
    rw [hy, map_zero]
  have hr : ∀ a b, a < b → G.E a b x ∈ (⊥ : Submodule K V) := fun a b hab => by
    rw [hxw.2 a b hab]
    exact Submodule.zero_mem _
  have hxW : x ∈ W := IsoW_le G hW mu hxI
  have hdom : DomW la := G.dom_of_hwmod hbot hW hWf hxW (by rwa [Submodule.mem_bot]) hxw.1 hr
  obtain ⟨S, hS⟩ := hWf
  have hkill : ∀ y ∈ IsoW G W mu, G.cprod (GlX.qlist S (GlW.casI la)) (G.comp la y) = 0 := by
    intro y hy
    have hle : (⨆ v : {v : V // G.IsHW mu v ∧ v ∈ W}, G.gS {(v : V)}) ≤
        LinearMap.ker ((G.cprod (GlX.qlist S (GlW.casI la))) ∘ₗ G.comp la) := by
      refine iSup_le fun v => ?_
      by_cases hv0 : (v : V) = 0
      · intro z hz
        have hz0 : z ∈ (⊥ : Submodule K V) := G.gS_le (by
          intro w hw
          rw [Set.mem_singleton_iff] at hw
          rw [hw, hv0]
          exact Submodule.zero_mem _) hbot hz
        rw [Submodule.mem_bot] at hz0
        rw [hz0]
        exact Submodule.zero_mem _
      · intro z hz
        exact LinearMap.mem_ker.mpr (GlX.gen_kill (G := G) hW hS v.2.1 v.2.2 hv0 hdom
          ⟨fun _ => le_refl _, rfl⟩ (fun _ => hne) z hz)
    exact LinearMap.mem_ker.mp (hle (IsoW_le_iSup G W mu hy))
  have h1 := hkill x hxI
  rw [hxw.1] at h1
  have h2 := GlX.cprod_mod (G := G) (μ := la) hbot hxw.1 hr (GlX.qlist S (GlW.casI la))
  rw [h1, zero_sub, neg_mem_iff, Submodule.mem_bot] at h2
  have hprod : ((GlX.qlist S (GlW.casI la)).map (fun c => ((GlW.casI la - c : ℤ) : K))).prod ≠ 0 := by
    refine List.prod_ne_zero ?_
    intro hmem
    obtain ⟨c, hc, hc0⟩ := List.mem_map.mp hmem
    have hc1 : GlW.casI la - c = 0 := by exact_mod_cast hc0
    have hc2 : c ∈ (S.image GlW.casI).erase (GlW.casI la) := Finset.mem_toList.mp hc
    exact (Finset.mem_erase.mp hc2).1 (by omega)
  rcases smul_eq_zero.mp h2 with h | h
  · exact hprod h
  · exact hx0 h

theorem equiv_zero (G : GlW K V n) (h : V) (ψ : G.gS {h} →ₗ[K] V)
    (hψ : ∀ a b x, ψ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (ψ x))
    (h0 : ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = 0) : ψ = 0 := by
  have key : G.gS {h} ≤ Submodule.map (G.gS {h}).subtype (LinearMap.ker ψ) := by
    refine G.gS_le ?_ ?_
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact Submodule.mem_map.mpr ⟨⟨h, G.subset_gS _ (Set.mem_singleton h)⟩, LinearMap.mem_ker.mpr h0, rfl⟩
    · intro a b y hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
      refine Submodule.mem_map.mpr ⟨(res G _ (G.gS_stable {h})).E a b z, ?_, rfl⟩
      rw [LinearMap.mem_ker, hψ, LinearMap.mem_ker.mp hz, map_zero]
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp (key x.2)
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx', LinearMap.zero_apply]
  exact LinearMap.mem_ker.mp hz

theorem exists_transport (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin n → ℤ}
    {h h' : V} (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    ∃ θ : G.gS {h} →ₗ[K] V, (∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x)) ∧
      ∀ m ∈ G.gS {h'}, ∃ y, θ y = m := by
  have hbot : G.Stable (⊥ : Submodule K V) := by
    intro a b y hy
    rw [Submodule.mem_bot] at hy ⊢
    rw [hy, map_zero]
  by_cases h0' : h' = 0
  · refine ⟨0, fun a b x => by simp, fun m hm => ⟨0, ?_⟩⟩
    have hm0 : m ∈ (⊥ : Submodule K V) := G.gS_le (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw, h0']
      exact Submodule.zero_mem _) hbot hm
    rw [Submodule.mem_bot] at hm0
    rw [hm0, map_zero]
  have hUW : G.gS {h} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hhW) hW
  have hU'W : G.gS {h'} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hh'W) hW
  obtain ⟨S, hS⟩ := hWf
  by_cases hdis : G.gS {h} ⊓ G.gS {h'} = ⊥
  · have hind : iSupIndep (fun i : Bool => if i then G.gS {h'} else G.gS {h}) := by
      rw [iSupIndep_pair (i := true) (j := false) (by decide) (fun k => by cases k <;> simp), disjoint_iff]
      show G.gS {h'} ⊓ G.gS {h} = ⊥
      rw [inf_comm]
      exact hdis
    have hRW : ∀ i : Bool, (if i then G.gS {h'} else G.gS {h}) ≤ G.gS {h} ⊔ G.gS {h'} := by
      intro i
      cases i <;> simp
    have hWR : G.gS {h} ⊔ G.gS {h'} ≤ ⨆ i : Bool, (if i then G.gS {h'} else G.gS {h}) :=
      sup_le (le_iSup (fun i : Bool => if i then G.gS {h'} else G.gS {h}) false)
        (le_iSup (fun i : Bool => if i then G.gS {h'} else G.gS {h}) true)
    obtain ⟨π, hπ1, hπ2, hπ3⟩ := proj_exists (W := G.gS {h} ⊔ G.gS {h'})
      (fun i : Bool => if i then G.gS {h'} else G.gS {h}) hind hRW hWR
    have hEq : ∀ i, ∀ x ∈ G.gS {h} ⊔ G.gS {h'}, ∀ c d, π i (G.E c d x) = G.E c d (π i x) := by
      intro i x hx c d
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      have hy' : G.E c d y ∈ G.gS {h} := G.gS_stable _ c d y hy
      have hz' : G.E c d z ∈ G.gS {h'} := G.gS_stable _ c d z hz
      simp only [map_add (f := _)]
      cases i
      · rw [hπ2 false _ hy', hπ2 false _ hy, hπ3 false true (by decide) _ hz', hπ3 false true (by decide) _ hz,
          map_zero]
      · rw [hπ3 true false (by decide) _ hy', hπ3 true false (by decide) _ hy, hπ2 true _ hz', hπ2 true _ hz,
          map_zero]
    have hW' : G.Stable (G.gS {h} ⊔ G.gS {h'}) := by
      intro a b x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (G.gS_stable _ a b y hy))
        (Submodule.mem_sup_right (G.gS_stable _ a b z hz))
    have hWf' : G.FinW (G.gS {h} ⊔ G.gS {h'}) := ⟨S, fun x hx => hS x (sup_le hUW hU'W hx)⟩
    obtain ⟨θ₁, θ₁', hθ1, -, -, hθE', hinv⟩ := GlX.exists_theta G (W := G.gS {h} ⊔ G.gS {h'}) hW' hWf'
      (h := h') (h' := h) hh' hh (Submodule.mem_sup_right (G.subset_gS _ (Set.mem_singleton h')))
      (Submodule.mem_sup_left (G.subset_gS _ (Set.mem_singleton h))) h0' h0 (π true) (π false)
      (hπ1 true) (hπ2 true) (hEq true) (hπ1 false) (hπ2 false) (hEq false)
    refine ⟨θ₁' ∘ₗ (G.gS {h}).subtype, fun a b x => ?_, fun m hm => ⟨⟨θ₁ m, hθ1 m⟩, hinv m hm⟩⟩
    show θ₁' (G.E a b (x : V)) = G.E a b (θ₁' (x : V))
    exact hθE' _ (Submodule.mem_sup_left x.2) a b
  · have hI : G.Stable (G.gS {h} ⊓ G.gS {h'}) := by
      intro a b x hx
      rw [Submodule.mem_inf] at hx ⊢
      exact ⟨G.gS_stable _ a b x hx.1, G.gS_stable _ a b x hx.2⟩
    obtain ⟨v, hvI, hv0, μ, hvw, hvr⟩ := G.exists_hwmod (U := ⊥) (G.graded_of hI)
      (fun a b _ x hx => hI a b x hx) ⟨S, fun x hx => hS x (hUW (Submodule.mem_inf.mp hx).1)⟩
      (fun hle => hdis (le_bot_iff.mp hle))
    have hvHW : G.comp μ v = v ∧ ∀ a b, a < b → G.E a b v = 0 := ⟨hvw, fun a b hab => by
      have hq := hvr a b hab
      rwa [Submodule.mem_bot] at hq⟩
    have hv0' : v ≠ 0 := fun hq => hv0 (by rw [hq]; exact Submodule.zero_mem _)
    obtain ⟨-, c', hc'⟩ := G.hw_in_gS hh' hW ⟨S, hS⟩ hh'W (Submodule.mem_inf.mp hvI).2 hvHW hv0'
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      apply hv0'
      rw [hc', zero_smul]
    have hmem : h' ∈ G.gS {h} := by
      have hq : h' = c'⁻¹ • v := by rw [hc', smul_smul, inv_mul_cancel₀ hc'0, one_smul]
      rw [hq]
      exact Submodule.smul_mem _ _ (Submodule.mem_inf.mp hvI).1
    have hle : G.gS {h'} ≤ G.gS {h} := G.gS_le (Set.singleton_subset_iff.mpr hmem) (G.gS_stable _)
    exact ⟨(G.gS {h}).subtype, fun a b x => rfl, fun m hm => ⟨⟨m, hle hm⟩, rfl⟩⟩

end iso

section padic

variable (p : ℕ) [Fact p.Prime] {U V : Type} [AddCommGroup U] [Module ℚ_[p] U] [AddCommGroup V] [Module ℚ_[p] V]
  {n : ℕ}

theorem QQ_int (G₁ : GlW ℚ_[p] U n) (G₂ : GlW ℚ_[p] V n) (S : Finset (Fin n → ℤ)) (l : ℕ) {k : ℕ}
    (b : Module.Basis (Fin k) ℚ_[p] U) {L : AddSubgroup U} {M : AddSubgroup V} (hZ : ZpClosed p M)
    (hLd : DivStable G₁.E L) (hMd : DivStable G₂.E M) (hLg : ∀ μ, ∀ x ∈ L, G₁.comp μ x ∈ L)
    (hMg : ∀ μ, ∀ x ∈ M, G₂.comp μ x ∈ M) (hbL : ∀ i, b i ∈ L) (hbi : ∀ x ∈ L, ∀ i, ‖b.repr x i‖ ≤ 1)
    {m : V} (hm : m ∈ M) :
    ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) • QQ G₁ G₂ S l b m ∈ M := by
  obtain ⟨hZH, hDH⟩ := hom_divided_holds p U V (Fin n) G₁.E G₂.E L M hZ hLd hMd
  have hrel : GlRel (homAct G₁.E G₂.E) :=
    hom_relation_holds ℚ_[p] U V (Fin n) G₁.E G₂.E (glRel_ofT G₁) (glRel_ofT G₂)
  have hterm : ∀ i, ((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) •
      Psi G₁ G₂ S l ((b.coord i).smulRight m) (b i) ∈ M := by
    intro i
    have hφ : (b.coord i).smulRight m ∈ HomLat (K := ℚ_[p]) L M := by
      show ∀ x ∈ L, (b.coord i).smulRight m x ∈ M
      intro x hx
      rw [LinearMap.smulRight_apply]
      exact hZ _ (by rw [Module.Basis.coord_apply]; exact hbi x hx i) m hm
    have hp := weightZeroProj_mem_homLat G₁ G₂ S hLg hMg hφ
    have hI := invariant_integral_holds p (U →ₗ[ℚ_[p]] V) (Fin n) (homAct G₁.E G₂.E) hrel _ hZH hDH l (List.finRange n)
      (List.nodup_finRange n) _ hp
    rw [List.length_finRange] at hI
    have hI' : ∀ x ∈ L, (((p : ℚ_[p]) ^ (n.choose 2 * Nat.log p (l + n - 1))) •
        InvOp (homAct G₁.E G₂.E) l (List.finRange n) (pr0 G₁ G₂ S ((b.coord i).smulRight m))) x ∈ M := hI
    exact hI' (b i) (hbL i)
  rw [QQ_apply, smul_comm, Finset.smul_sum, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ (AddSubgroup.sum_mem _ fun i _ => hterm i) _

end padic

theorem typeInt_of (hNat : InvNat) (hHom : HomInv) (hSchur : SchurTrace) : TypeInt := by
  intro p _ V _ _ n G W M l hD la
  by_cases hex : ∃ h, G.IsHW la h ∧ h ∈ W ∧ h ≠ 0
  · obtain ⟨h, hhw, hhW, h0⟩ := hex
    have hhw' : G.comp la h = h ∧ ∀ a b, a < b → G.E a b h = 0 := hhw
    have hUW : G.gS {h} ≤ W := G.gS_le (Set.singleton_subset_iff.mpr hhW) hD.stable
    obtain ⟨S, hS⟩ := hD.finW
    obtain ⟨k, b, hbM, hbi⟩ := hD.basis (G.gS {h}) hUW
    have hk : k ≠ 0 := by
      rintro rfl
      apply h0
      have h1 : (⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ : G.gS {h}) = 0 := b.ext_elem (fun i => i.elim0)
      exact congrArg Subtype.val h1
    have hfr : (Module.finrank ℚ_[p] (G.gS {h}) : ℚ_[p]) = (k : ℚ_[p]) := by
      rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
    have hSch : ∀ φ : (G.gS {h}) →ₗ[ℚ_[p]] (G.gS {h}),
        (∀ c, homAct (res G (G.gS {h}) (G.gS_stable {h})).E (res G (G.gS {h}) (G.gS_stable {h})).E c c φ = 0) →
        InvOp (homAct (res G (G.gS {h}) (G.gS_stable {h})).E (res G (G.gS {h}) (G.gS_stable {h})).E) l (List.finRange n) φ =
          (LinearMap.trace ℚ_[p] _ φ / (k : ℚ_[p])) • LinearMap.id := fun φ hφ => by
      rw [hSchur ℚ_[p] V n G W l hD.stable hD.fd hD.finW hD.bound la h hhw hhW h0 φ hφ, hfr]
    have hS' : ∀ (x : G.gS {h}) (μ : Fin n → ℤ), μ ∉ S → (res G (G.gS {h}) (G.gS_stable {h})).comp μ x = 0 :=
      fun x μ hμ => Subtype.ext (by rw [res_comp_coe]; exact hS _ (hUW x.2) μ hμ)
    refine ⟨QQ (res G (G.gS {h}) (G.gS_stable {h})) G S l b, ?_, ?_, ?_⟩
    · intro x hx
      have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤
          LinearMap.eqLocus (QQ (res G (G.gS {h}) (G.gS_stable {h})) G S l b) LinearMap.id := by
        refine iSup_le fun v => ?_
        obtain ⟨θ, hθ, hsurj⟩ := exists_transport G hD.stable hD.finW hhw v.2.1 hhW v.2.2 h0
        intro m hm
        obtain ⟨y, rfl⟩ := hsurj m hm
        exact LinearMap.mem_eqLocus.mpr (QQ_id hNat (res G (G.gS {h}) (G.gS_stable {h})) G S l b hS' hSch hk θ hθ y)
      exact LinearMap.mem_eqLocus.mp (hle (IsoW_le_iSup G W la hx))
    · intro mu hmu x hx
      refine QQ_zero hHom (res G (G.gS {h}) (G.gS_stable {h})) G S l b (W := IsoW G W mu) (G.gS_stable _) ?_ ?_ hx
      · intro μ ν x' y hx0 hy0 hyI hxw hyw c
        have hxw' := congrArg Subtype.val hxw
        rw [res_comp_coe] at hxw'
        exact hD.bound μ ν (x' : V) y (fun h' => hx0 (Subtype.ext h')) hy0 (hUW x'.2) (IsoW_le G hD.stable mu hyI)
          hxw' hyw c
      · intro ψ hψ hψW
        refine equiv_zero G h ψ hψ ?_
        have hc : (res G (G.gS {h}) (G.gS_stable {h})).comp la ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ =
            ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ :=
          Subtype.ext (by rw [res_comp_coe]; exact hhw'.1)
        have hE : ∀ a b, a < b → (res G (G.gS {h}) (G.gS_stable {h})).E a b ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = 0 :=
          fun a b hab => Subtype.ext (by rw [res_E_coe]; exact hhw'.2 a b hab)
        have hHW : G.comp la (ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩) = ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ ∧
            ∀ a b, a < b → G.E a b (ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩) = 0 :=
          ⟨by rw [← comp_comm2 (res G (G.gS {h}) (G.gS_stable {h})) G ψ (fun c x => hψ c c x) la, hc],
            fun a b hab => by rw [← hψ, hE a b hab, map_zero]⟩
        exact hw_IsoW_zero G hD.stable hD.finW hmu hHW (hψW _)
    · intro m hm _
      refine QQ_int p (res G (G.gS {h}) (G.gS_stable {h})) G S l b (L := M.comap (G.gS {h}).subtype.toAddMonoidHom) hD.closed ?_ hD.div ?_
        hD.graded hbM hbi hm
      · intro a c hac j x hx
        show ((((j.factorial : ℚ_[p]))⁻¹ • (((res G (G.gS {h}) (G.gS_stable {h})).E a c ^ j) x) : G.gS {h}) : V) ∈ M
        rw [Submodule.coe_smul, res_pow_coe]
        exact hD.div a c hac j _ hx
      · intro μ x hx
        show (((res G (G.gS {h}) (G.gS_stable {h})).comp μ x : G.gS {h}) : V) ∈ M
        rw [res_comp_coe]
        exact hD.graded μ _ hx
  · push_neg at hex
    refine ⟨0, ?_, fun _ _ _ _ => rfl, fun m _ _ => by simp⟩
    intro x hx
    have hle : (⨆ v : {v : V // G.IsHW la v ∧ v ∈ W}, G.gS {(v : V)}) ≤ ⊥ := by
      refine iSup_le fun v => G.gS_le ?_ ?_
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy, hex _ v.2.1 v.2.2]
        exact Submodule.zero_mem _
      · intro a b y hy
        rw [Submodule.mem_bot] at hy ⊢
        rw [hy, map_zero]
    have hx0 := hle (IsoW_le_iSup G W la hx)
    rw [Submodule.mem_bot] at hx0
    rw [hx0, map_zero]

end Formalism.InvariantFactorPaths.PW
end

section -- merged from Formalism.ThetaLogCoordinates.TraceIsometryWeights.FinalP
namespace Formalism.InvariantFactorPaths.PW.Top

theorem invInv : InvInv := invariant_inverse_holds
theorem invNat : InvNat := invariant_natural_holds
theorem homInv : HomInv := homInv_of invInv
theorem schurTrace : SchurTrace := schurTrace_of invInv
theorem typeInt : TypeInt := typeInt_of invNat homInv schurTrace
theorem divInt : DivInt := divided_integral_holds
theorem latBasisPol : LatBasisPol := lattice_basis_polynomial
theorem projP : ProjP := projection_lattice_holds
theorem commP : CommP := comm_projection_holds
theorem intP : IntP := intP_of typeInt latBasisPol
theorem dischargeP : DischargeP := dischargeP_of projP commP intP

end Formalism.InvariantFactorPaths.PW.Top
end

namespace Formalism.InvariantFactorPaths.PW.Top

theorem weylInt : WeylInt := weyl_integral_holds
theorem weylP : WeylP := weylP_of weylInt lattice_basis_polynomial

private theorem intP_statement : IntP := by
  have hInv : InvInv := invariant_inverse_holds
  exact intP_of (typeInt_of invariant_natural_holds (homInv_of hInv) (schurTrace_of hInv)) lattice_basis_polynomial

theorem extP : ExtP := extP_of intP_statement
theorem dischargeW : DischargeW := dischargeW_of weylP
theorem dischargeE : DischargeE := dischargeE_of extP

end Formalism.InvariantFactorPaths.PW.Top
