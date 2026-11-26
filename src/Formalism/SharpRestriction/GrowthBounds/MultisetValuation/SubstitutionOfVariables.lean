module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AtPiEqRescale

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntegralExpRename
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF expSum eq_of_low Gser)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

section ExpFormal

variable {K : Type} [Field K]

theorem th_expK_zero {ι : Type} : expK (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_expK, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h

theorem th_subst_expSum {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries σ K) (M : ℕ) : MvPowerSeries.subst a (expSum f M) = expSum (MvPowerSeries.subst a f) M := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [expSum, expSum, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]

theorem th_subst_expK {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (expK f) = expK (MvPowerSeries.subst a f) := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hsf : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 hf
  refine eq_of_low fun M => ?_
  have h1 := Formalism.DworkPowerSeriesWeights.low_subst_of_low ha0 (low_expK_sub hf M)
  have h2 := low_expK_sub hsf M
  have e : MvPowerSeries.subst a (expK f) - expK (MvPowerSeries.subst a f) =
      MvPowerSeries.subst a (expK f - expSum f M) -
        (expK (MvPowerSeries.subst a f) - expSum (MvPowerSeries.subst a f) M) := by
    rw [← th_subst_expSum ha, ← MvPowerSeries.coe_substAlgHom ha, map_sub]
    ring
  rw [e]
  exact low_sub h1 h2

theorem th_map_expK {ι K2 : Type} [Field K2] (φ : K →+* K2) (f : MvPowerSeries ι K) :
    MvPowerSeries.map φ (expK f) = expK (MvPowerSeries.map φ f) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPowerSeries.coeff_map, coeff_expK, coeff_expK, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_inv₀, map_natCast, ← map_pow, MvPowerSeries.coeff_map]

end ExpFormal

section Param

variable (p : ℕ) [hp : Fact p.Prime]

def E0 {ι : Type} (f : MvPowerSeries ι (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ ∃ h : MvPowerSeries ι (WW p), MvPowerSeries.constantCoeff h = 0 ∧
    expK f = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) h

theorem integralExp_zero {ι : Type} : E0 p (0 : MvPowerSeries ι (K0 p)) := by
  refine ⟨map_zero _, 0, map_zero _, ?_⟩
  rw [th_expK_zero, map_zero, add_zero]

theorem integralExp_add {ι : Type} {f g : MvPowerSeries ι (K0 p)} (hf : E0 p f) (hg : E0 p g) : E0 p (f + g) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  obtain ⟨hg0, h', hh0', hge⟩ := hg
  refine ⟨by rw [map_add (f := _), hf0, hg0, add_zero], h + h' + h * h', by simp [hh0, hh0'], ?_⟩
  rw [expK_add hf0 hg0, hfe, hge, map_add (f := _), map_add (f := _), map_mul]
  ring

theorem integralExp_sum {ι α : Type} (s : Finset α) (f : α → MvPowerSeries ι (K0 p)) (h : ∀ a ∈ s, E0 p (f a)) :
    E0 p (∑ a ∈ s, f a) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact integralExp_zero p
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact integralExp_add p (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

def ren {κ σ R : Type} [CommRing R] (φ : κ → σ) (f : MvPowerSeries κ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ R)) f

theorem integralExp_rename {κ σ : Type} [Finite κ] (φ : κ → σ) {f : MvPowerSeries κ (K0 p)} (hf : E0 p f) :
    E0 p (ren φ f) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  have hXK : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have hXW : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have haW : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXW
  have haK : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXK
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero haK hXK hf0, ren φ h,
    MvPowerSeries.constantCoeff_subst_eq_zero haW hXW hh0, ?_⟩
  unfold ren
  rw [← th_subst_expK _ hXK hf0, hfe, ← MvPowerSeries.coe_substAlgHom haK, map_add (f := _), map_one,
    MvPowerSeries.coe_substAlgHom haK, MvPowerSeries.map_subst haW]
  simp only [MvPowerSeries.map_X]

theorem exp_neg_integral {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : E0 p f) :
    ∃ w : MvPowerSeries ι (WW p), expK (-f) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  refine ⟨MvPowerSeries.invOfUnit (1 + h) 1, ?_⟩
  have hinv : (1 + h) * MvPowerSeries.invOfUnit (1 + h) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by simp [hh0])
  have hneg : expK (-f) * expK f = 1 := by
    rw [← expK_add (by simp [hf0]) hf0, neg_add_cancel, th_expK_zero]
  calc expK (-f) = expK (-f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        ((1 + h) * MvPowerSeries.invOfUnit (1 + h) 1) := by rw [hinv, map_one, mul_one]
    _ = (expK (-f) * expK f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        (MvPowerSeries.invOfUnit (1 + h) 1) := by
      rw [hfe, map_mul, map_add (f := _), map_one]
      ring
    _ = _ := by rw [hneg, one_mul]

end Param

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser')

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Param

variable (p : ℕ) [hp : Fact p.Prime]

def tOf {K' σ τ : Type} [Field K'] (vp : K') (μ : PowerSeries K') (L : σ → MvPowerSeries τ K') :
    σ → MvPowerSeries τ K' :=
  fun i => PowerSeries.subst (L i) (PowerSeries.C vp * μ)

private theorem constantCoeff_logF_eq_zero : PowerSeries.constantCoeff (logF p) = 0 := by
  first
  | (rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; unfold logF; simp)
  | (unfold logF; simp)
  | (simp [logF, ← PowerSeries.coeff_zero_eq_constantCoeff_apply])

private theorem cc_subst_lemma_2 {τ S : Type} [CommRing S] {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff a = 0) {f : PowerSeries S} (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  have hs : PowerSeries.HasSubst a := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact PowerSeries.HasSubst.of_constantCoeff_nilpotent (by rw [ha]; exact IsNilpotent.zero)
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  first
  | rw [PowerSeries.subst_mul hs, PowerSeries.subst_X hs, map_mul, ha, zero_mul]
  | rw [← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom hs, PowerSeries.subst_X hs,
      map_mul, ha, zero_mul]

theorem th_lX_const (K1 : Type) [Field K1] [Algebra (K0 p) K1] {σ : Type} (i : σ) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) = 0 := by
  refine cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) ?_
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_logF_eq_zero, map_zero]

theorem th_inParam_eq {σ : Type} (f : MvPowerSeries σ (K0 p)) : inParam p f = inParamK p (K0 p) f := by
  unfold inParam inParamK
  congr 1

theorem th_inParamK_map {σ : Type} [Finite σ] (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K']
    [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (U : MvPowerSeries σ K1) :
    inParamK p K' (MvPowerSeries.map (algebraMap K1 K') U) =
      MvPowerSeries.map (algebraMap K1 K') (inParamK p K1 U) := by
  unfold inParamK
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (th_lX_const p K1))]
  congr 1
  funext i
  have hX : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ K1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  rw [PowerSeries.map_subst hX, MvPowerSeries.map_X, map_logF, map_logF]
  congr 1
  ext n
  unfold lgF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [apply_ite (algebraMap K1 K'), map_zero, map_inv₀, map_pow, map_natCast]

theorem th_tOf_const {K' σ τ : Type} [Field K'] (vp : K') (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (i : σ) :
    MvPowerSeries.constantCoeff (tOf vp μ L i) = 0 := by
  unfold tOf
  refine cc_subst_lemma_2 (hL0 i) ?_
  rw [map_mul, h0, mul_zero]

theorem th_subst_log (K' : Type) [Field K'] [Algebra (K0 p) K'] {σ τ : Type} [Finite σ] (vp : K')
    (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X)
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (U : MvPowerSeries σ K') :
    MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U =
      MvPowerSeries.subst (tOf vp μ L) (inParamK p K' U) := by
  have hsh : MvPowerSeries.HasSubst (tOf vp μ L) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (th_tOf_const vp μ h0 L hL0)
  unfold inParamK
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero (th_lX_const p K')) hsh]
  congr 1
  funext i
  have hX : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ K') :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have e3 : MvPowerSeries.subst (tOf vp μ L) (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K')
      (PowerSeries.map (algebraMap (K0 p) K') (logF p))) =
      PowerSeries.subst (MvPowerSeries.subst (tOf vp μ L) (MvPowerSeries.X i : MvPowerSeries σ K'))
        (PowerSeries.map (algebraMap (K0 p) K') (logF p)) :=
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.hasSubst_iff.1 hX) hsh _
  rw [e3, MvPowerSeries.subst_X hsh, map_logF]
  exact (log_at p K' vp μ h0 h1 (L i) (hL0 i)).symm

private theorem hasSubst_of_constantCoeff_eq_zero' {κ τ S : Type} [CommRing S] [Finite κ] {a : κ → MvPowerSeries τ S}
    (h : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' h
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero h
  | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [h s]; exact IsNilpotent.zero)
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [h s]; exact IsNilpotent.zero)
  | exact ⟨fun s => by rw [h s]; exact IsNilpotent.zero, fun d => Set.toFinite _⟩

theorem th_hasSubst_lX {σ : Type} [Finite σ] : MvPowerSeries.HasSubst
    (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) := by
  refine hasSubst_of_constantCoeff_eq_zero' fun i => ?_
  exact cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) (constantCoeff_logF_eq_zero p)

private theorem constantCoeff_subst_eq_zero' {κ τ S : Type} [CommRing S] [Finite κ] {a : κ → MvPowerSeries τ S}
    (h : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) {f : MvPowerSeries κ S}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 := by
  have key : ∀ d : κ →₀ ℕ,
      MvPowerSeries.coeff d f • MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
    intro d
    by_cases hd : d = 0
    · subst hd
      rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at hf
      rw [hf, zero_smul]
    · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hd (Finsupp.ext hcon)
      have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
        rw [Finsupp.prod, map_prod]
        exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by rw [map_pow, h s, zero_pow hs])
      rw [h0, smul_zero]
  rw [MvPowerSeries.constantCoeff_subst (hasSubst_of_constantCoeff_eq_zero' h)]
  simp only [key, finsum_zero]

theorem th_inParam_const {σ : Type} [Finite σ] {f : MvPowerSeries σ (K0 p)}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (inParam p f) = 0 := by
  unfold inParam
  exact constantCoeff_subst_eq_zero' (fun i => cc_subst_lemma_2 (MvPowerSeries.constantCoeff_X i) (constantCoeff_logF_eq_zero p)) hf

theorem th_inParam_sub {σ : Type} [Finite σ] (f g : MvPowerSeries σ (K0 p)) :
    inParam p (f - g) = inParam p f - inParam p g := by
  have ha := th_hasSubst_lX p (σ := σ)
  unfold inParam
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sub]

theorem th_inParam_neg {σ : Type} [Finite σ] (f : MvPowerSeries σ (K0 p)) :
    inParam p (-f) = -inParam p f := by
  have ha := th_hasSubst_lX p (σ := σ)
  unfold inParam
  rw [← MvPowerSeries.coe_substAlgHom ha, map_neg]

theorem th_inParam_sum {σ α : Type} [Finite σ] (s : Finset α) (f : α → MvPowerSeries σ (K0 p)) :
    inParam p (∑ a ∈ s, f a) = ∑ a ∈ s, inParam p (f a) := by
  have ha := th_hasSubst_lX p (σ := σ)
  unfold inParam
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]

theorem th_ren_hasSubst {κ σ R : Type} [Finite κ] [CommRing R] (φ : κ → σ) :
    MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ R)) :=
  hasSubst_of_constantCoeff_eq_zero' fun k => MvPowerSeries.constantCoeff_X (φ k)

theorem th_ren_sub {κ σ R : Type} [Finite κ] [CommRing R] (φ : κ → σ) (f g : MvPowerSeries κ R) :
    ren φ (f - g) = ren φ f - ren φ g := by
  have ha := th_ren_hasSubst (R := R) φ
  unfold ren
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sub]

theorem th_ren_const {κ σ R : Type} [Finite κ] [CommRing R] (φ : κ → σ) {f : MvPowerSeries κ R}
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (ren φ f) = 0 := by
  unfold ren
  exact constantCoeff_subst_eq_zero' (fun k => MvPowerSeries.constantCoeff_X (φ k)) hf

theorem th_inParam_ren {κ σ : Type} [Finite κ] [Finite σ] (φ : κ → σ) (f : MvPowerSeries κ (K0 p)) :
    inParam p (ren φ f) = ren φ (inParam p f) := by
  unfold inParam ren
  rw [MvPowerSeries.subst_comp_subst_apply (th_ren_hasSubst φ) (th_hasSubst_lX p),
    MvPowerSeries.subst_comp_subst_apply (th_hasSubst_lX p) (th_ren_hasSubst φ)]
  congr 1
  funext k
  rw [MvPowerSeries.subst_X (th_hasSubst_lX p)]
  have hX : PowerSeries.HasSubst (MvPowerSeries.X k : MvPowerSeries κ (K0 p)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X k)
  have e3 : MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)))
      (PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries κ (K0 p)) (logF p)) =
      PowerSeries.subst (MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)))
        (MvPowerSeries.X k : MvPowerSeries κ (K0 p))) (logF p) :=
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.hasSubst_iff.1 hX) (th_ren_hasSubst φ) _
  rw [e3, MvPowerSeries.subst_X (th_ren_hasSubst φ)]

theorem substitution_of_variables {σ : Type} (be : MvPowerSeries (Fin 2) (K0 p)) (a b : σ) :
    sub2 p be (MvPowerSeries.X a) (MvPowerSeries.X b) = ren ![a, b] be := by
  unfold sub2 ren
  congr 1
  funext k
  fin_cases k <;> rfl

def Gt (E : Type) [Fintype E] (c c' : K0 p) : MvPowerSeries (E ⊕ E) (K0 p) :=
  ∑ e : E, ren ![Sum.inl e, Sum.inr e] (Gser p c c')

theorem th_reduce {E τ : Type} [Fintype E] (be : MvPowerSeries (Fin 2) (K0 p))
    (hbe0 : MvPowerSeries.constantCoeff be = 0) (c c' : K0 p)
    (hG0 : MvPowerSeries.constantCoeff (Gser p c c') = 0) (hβ : E → E0 p (inParam p be - Gser p c c'))
    (Ph : MvPowerSeries (E ⊕ E) (K0 p))
    (hPh : Simeq p Ph (∑ e : E, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))))
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (μ : PowerSeries K')
    (h0 : PowerSeries.constantCoeff μ = 0) (hμ : ∀ n, PowerSeries.coeff n μ ∈ Rp p K' vp)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X)
    (L : E ⊕ E → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0)
    (hL : ∀ i, IntR (Rp p K' vp) (L i)) :
    ∃ V' : MvPowerSeries τ K', IntR (Rp p K' vp) V' ∧
      MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i)
          (MvPowerSeries.map (algebraMap (K0 p) K') (expS p (-Ph))) =
        MvPowerSeries.subst (tOf vp μ L) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K') (Gt p E c c')))) * V' := by
  have hcz := charZero_K' p (K0 p)
  obtain ⟨hc0, h, hh0, hE⟩ := hPh
  have hPsi0 : MvPowerSeries.constantCoeff
      (∑ e : E, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) :
        MvPowerSeries (E ⊕ E) (K0 p)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun e _ => by rw [substitution_of_variables]; exact th_ren_const _ hbe0
  have hPh0 : MvPowerSeries.constantCoeff Ph = 0 := by
    rw [map_sub, hPsi0, sub_zero] at hc0
    exact hc0
  have hGt0 : MvPowerSeries.constantCoeff (Gt p E c c') = 0 := by
    unfold Gt
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun e _ => th_ren_const _ hG0
  have hδ : E0 p (inParam p Ph - Gt p E c c') := by
    have e : inParam p Ph - Gt p E c c' =
        inParam p (Ph - ∑ e : E, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) +
          ∑ e : E, ren ![Sum.inl e, Sum.inr e] (inParam p be - Gser p c c') := by
      rw [th_inParam_sub, th_inParam_sum]
      simp only [substitution_of_variables, th_inParam_ren, th_ren_sub, Finset.sum_sub_distrib, Gt]
      ring
    rw [e]
    exact integralExp_add p ⟨th_inParam_const p hc0, h, hh0, hE⟩ (integralExp_sum p _ _ fun e _ => integralExp_rename p _ (hβ e))
  obtain ⟨w, hw⟩ := exp_neg_integral p hδ
  have ht0 := th_tOf_const vp μ h0 L hL0
  have htI : ∀ i, IntR (Rp p K' vp) (tOf vp μ L i) := fun i => IntR_psubst (hL0 i) (hL i) fun n => by
    rw [PowerSeries.coeff_C_mul]
    exact (Rp p K' vp).mul_mem (vp_mem_Rp p K' vp) (hμ n)
  refine ⟨MvPowerSeries.subst (tOf vp μ L) (MvPowerSeries.map (algebraMap (K0 p) K')
    (MvPowerSeries.map (algebraMap (WW p) (K0 p)) w)), IntR_subst _ ht0 htI fun n => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map]
    exact W_mem_Rp p K' vp _
  · have e1 : inParam p (expS p (-Ph)) = expK (-(Gt p E c c')) * expK (-(inParam p Ph - Gt p E c c')) := by
      have : inParam p (expS p (-Ph)) = expK (inParam p (-Ph)) := by
        unfold inParam
        exact th_subst_expK _ (fun i => by
          have := th_lX_const p (K0 p) i
          rwa [Algebra.algebraMap_self, PowerSeries.map_id] at this) (by rw [map_neg, hPh0, neg_zero])
      rw [this, ← expK_add (by rw [map_neg, hGt0, neg_zero]) (by rw [map_neg, hδ.1, neg_zero]), th_inParam_neg]
      congr 1
      ring
    rw [th_subst_log p K' vp μ h0 h1 L hL0, th_inParamK_map p (K0 p) K', ← th_inParam_eq, e1, hw, map_mul,
      th_map_expK, map_neg, MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero ht0)]

end Param

end Formalism.MainNotions.FormalGroupSystem.Pf
