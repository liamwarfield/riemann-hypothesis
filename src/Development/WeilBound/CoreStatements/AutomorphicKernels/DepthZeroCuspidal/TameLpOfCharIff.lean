module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.TameLpOfCharIff
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem tame_lpOfChar_iff (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) :
    IsTameWD (WD.lpOfChar h ξ hξ) ↔ ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → ξ σ = 1 := by
  constructor
  · rintro ⟨n, a, ha, H⟩ σ hσ
    unfold WD.lpOfChar at ha
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.mp ha
    have h1 : ∀ u : Fin 1 → ℂ,
        (WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) fun _ => hξ).ρ σ u = u := by
      intro u
      obtain ⟨v, rfl⟩ := e.surjective u
      rw [← he, H σ hσ]
      rfl
    have h2 := congrFun (h1 fun _ => 1) 0
    rw [WDRep.ofChars_ρ, diagEnd_apply, mul_one] at h2
    exact Units.ext h2
  · intro H
    refine ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ), rfl, fun σ hσ => ?_⟩
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [WDRep.ofChars_ρ, diagEnd_apply, H σ hσ]
    simp

end PositivityTheory.LocalParametersCuspidal.DZC

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.LeviInductionForms
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

theorem val_sub_one_lt_of_pow {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {p : ℕ} (hp : p.Prime) (hpv : v (p : K) < 1) {x : K} {k : ℕ} (hx : v (x ^ p ^ k - 1) < 1) :
    v (x - 1) < 1 := by
  have hN : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 : v (x ^ p ^ k) = 1 := by
    have := Valuation.map_one_add_of_lt v hx
    rwa [add_sub_cancel] at this
  have hx1 : v x ≤ 1 := by
    refine le_of_not_gt fun hc => ?_
    have : 1 < v x ^ p ^ k := one_lt_pow₀ hc hN
    rw [← map_pow, h1] at this
    exact lt_irrefl _ this
  have hy : v (x - 1) ≤ 1 :=
    (Valuation.map_sub v x 1).trans (max_le hx1 (by rw [map_one]))
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨x - 1, hy⟩ : v.integer) (1 : v.integer) k
  have hr' : x ^ p ^ k = (x - 1) ^ p ^ k + 1 + (p : K) * (x - 1) * (r : K) := by
    have := congrArg (fun z : v.integer => (z : K)) hr
    simp only [Subring.coe_add, Subring.coe_pow, Subring.coe_mul, Subring.coe_natCast, OneMemClass.coe_one,
      one_pow, mul_one, sub_add_cancel] at this
    exact this
  have hr1 : v (r : K) ≤ 1 := r.2
  have e : (x - 1) ^ p ^ k = (x ^ p ^ k - 1) + -((p : K) * (x - 1) * (r : K)) := by
    rw [hr']; ring
  have hlt : v ((x - 1) ^ p ^ k) < 1 := by
    rw [e]
    refine Valuation.map_add_lt v hx ?_
    rw [Valuation.map_neg, map_mul, map_mul]
    calc v (p : K) * v (x - 1) * v (r : K) ≤ v (p : K) * 1 * 1 := by gcongr
      _ < 1 := by rw [mul_one, mul_one]; exact hpv
  refine lt_of_not_ge fun hc => ?_
  have : 1 ≤ v (x - 1) ^ p ^ k := one_le_pow₀ hc
  rw [← map_pow] at this
  exact absurd hlt (not_lt.2 this)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}


omit [IsAlgClosure E Ω] in
theorem wildPf_of_isWild {σ : G E Ω} (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A σ) : Formalism.MainNotions.N.KillingConditions.WildPf.IsWild A σ := by
  intro y hy
  have hv : A.valuation y ≠ 0 := by simpa using hy
  have e : σ y / y - 1 = (σ y - y) / y := by field_simp
  rw [e, map_div₀]
  exact (div_lt_one₀ (zero_lt_iff.2 hv)).2 (hσ.2 y hy)

theorem wild_to_unitsOne (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (σ : Weil h)
    (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω)) : Valued.v ((a σ : w.adicCompletion E) - 1) < 1 := by
  obtain ⟨p, hp, hpw⟩ : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 E) ∈ w.asIdeal :=
    ⟨_, GlobalTheory.LocalData.resChar_prime w, GlobalTheory.LocalData.resChar_mem w⟩
  have hpA : A.valuation ((p : ℕ) : Ω) < 1 := by
    have := (h ((p : ℕ) : 𝓞 E)).2 hpw
    simpa using this
  have hpv : Valued.v ((p : ℕ) : w.adicCompletion E) < 1 := by
    have h1 := (w.valuation_lt_one_iff_mem (K := E) ((p : ℕ) : 𝓞 E)).2 hpw
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w ((p : ℕ) : E)
    simp only [map_natCast] at h1
    have h3 : ((p : ℕ) : w.adicCompletion E) = (((p : ℕ) : E) : w.adicCompletion E) :=
      (map_natCast (algebraMap E (w.adicCompletion E)) p).symm
    rw [h3, h2]; exact h1
  set U : Set (w.adicCompletion E)ˣ := {u | Valued.v ((u : w.adicCompletion E) - 1) < 1} with hUdef
  have hU : U ∈ nhds (1 : (w.adicCompletion E)ˣ) := by
    have h0 : {x : w.adicCompletion E | Valued.v (x - 1) < 1} ∈
        nhds ((1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [Valued.mem_nhds]
      exact ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
    exact Units.continuous_val.continuousAt.preimage_mem_nhds h0
  have hV : (fun τ : Ine (F := E) A => a (ineIncl h τ)) ⁻¹' U ∈ nhds (1 : Ine (F := E) A) := by
    refine ha.cont.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨O, hO, hOs⟩ := (mem_nhds_induced Subtype.val (1 : Ine (F := E) A) _).1 hV
  rw [OneMemClass.coe_one] at hO
  obtain ⟨L, hL, hLO⟩ := (krullTopology_mem_nhds_one_iff E Ω O).1 hO
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hp hpA (σ : G E Ω) (wildPf_of_isWild hσ)
    L.fixingSubgroup (IntermediateField.fixingSubgroup_isOpen L)
  have hτ : (σ : G E Ω) ^ (p ^ k) ∈ Ine (F := E) A := (Ine (F := E) A).pow_mem hσ.1 _
  have hmem := hOs (show ((⟨_, hτ⟩ : Ine (F := E) A) : G E Ω) ∈ O from hLO hk)
  have e : ineIncl h (⟨_, hτ⟩ : Ine (F := E) A) = σ ^ (p ^ k) := Subtype.ext (by simp)
  simp only [Set.mem_preimage, e, map_pow, hUdef, Set.mem_ofPred_eq, Units.val_pow_eq_pow_val] at hmem
  exact val_sub_one_lt_of_pow Valued.v hp hpv hmem

end PositivityTheory.LocalParametersCuspidal.DZC

end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.WhittakerSupportTildeOf
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.SuperDiagUSingle
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Basics
variable {m : ℕ}






end Basics

section Mask
variable {N : ℕ} (P : Fin N → Fin N → Prop) [DecidableRel P]

def maskM (X : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k := fun a b => if P a b then X a b else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maskM_mul (hP : ∀ a b c, P a b → P b c → False) (X Y : Matrix (Fin N) (Fin N) k) :
    maskM P X * maskM P Y = 0 := by
  ext a c
  simp only [Matrix.mul_apply, maskM, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h1 : P a b
  · by_cases h2 : P b c
    · exact (hP a b c h1 h2).elim
    · simp [h2]
  · simp [h1]


def U (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) : GL (Fin N) k :=
  ⟨1 + maskM P X, 1 - maskM P X, by simp [add_mul, mul_sub, maskM_mul P hP],
    by simp [sub_mul, mul_add, maskM_mul P hP]⟩






end Mask

section Rep
variable {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]


end Rep

section Parab
variable {M : ℕ}




end Parab

section Main

end Main

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
end

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option linter.unusedSectionVars false

namespace WhittakerInverseTranspose

section Tilde

theorem invT_invT' {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    GlobalTheory.CuspRep.invT n R (GlobalTheory.CuspRep.invT n R g) = g := Units.ext rfl

theorem val_invT' {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) :
    ((GlobalTheory.CuspRep.invT n R g : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) =
      ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ := rfl

theorem continuous_invT' (N : ℕ) : Continuous (GlobalTheory.CuspRep.invT N k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSmooth_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : IsSmooth ρ) :
    IsSmooth (ρ.comp (GlobalTheory.CuspRep.invT N k)) :=
  fun v => (h v).preimage (continuous_invT' N)

theorem isIrreducible_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp (GlobalTheory.CuspRep.invT N k)) := by
  let Φ : Subrepresentation (ρ.comp (GlobalTheory.CuspRep.invT N k)) ≃o Subrepresentation ρ :=
    { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
        rw [← invT_invT' N g]
        exact U.apply_mem_toSubmodule (GlobalTheory.CuspRep.invT N k g) hv⟩
      invFun := fun U => ⟨U.toSubmodule, fun g v hv => U.apply_mem_toSubmodule _ hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have : IsSimpleOrder (Subrepresentation ρ) := h
  exact Φ.isSimpleOrder

theorem mem_unipRad_iff' {s N : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N) (g : GL (Fin N) k) :
    g ∈ unipRad k e ↔ ∀ x y, ((e.symm y).1 < (e.symm x).1 → (g : Matrix (Fin N) (Fin N) k) x y = 0) ∧
      ((e.symm x).1 = (e.symm y).1 →
        (g : Matrix (Fin N) (Fin N) k) x y = (1 : Matrix (Fin N) (Fin N) k) x y) := by
  rw [mem_unipRad, mem_parab_iff]
  constructor
  · rintro ⟨h1, h2⟩ x y
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
    simp only [Equiv.symm_apply_apply]
    refine ⟨fun hab => h1 a b i j hab, fun hab => ?_⟩
    subst hab
    rw [h2 a i j]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h; exact hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h)).2)
  · intro h
    refine ⟨fun a b i j hab => (h _ _).1 (by simpa using hab), fun a i j => ?_⟩
    rw [(h _ _).2 (by simp)]
    by_cases hij : i = j
    · subst hij; simp
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne]
      intro h'; exact hij (eq_of_heq (Sigma.mk.inj_iff.1 (e.injective h')).2)

theorem invT_mem_unipRad {s N : ℕ} {d d' : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    (e' : (Σ a, Fin (d' a)) ≃ Fin N) (he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1) {g : GL (Fin N) k}
    (hg : g ∈ unipRad k e) : GlobalTheory.CuspRep.invT N k g ∈ unipRad k e' := by
  have hi := (mem_unipRad_iff' e _).1 (inv_mem hg)
  refine (mem_unipRad_iff' e' _).2 fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩
  · rw [val_invT', Matrix.transpose_apply]
    refine (hi y x).1 ?_
    rw [he, he] at hxy
    exact Fin.rev_lt_rev.1 hxy
  · rw [val_invT', Matrix.transpose_apply, (hi y x).2 ?_]
    · by_cases hxy' : x = y
      · subst hxy'; rfl
      · rw [Matrix.one_apply_ne hxy', Matrix.one_apply_ne (Ne.symm hxy')]
    · rw [he, he] at hxy; exact (Fin.rev_injective hxy).symm

theorem isCuspidal_comp_invT {N : ℕ} {ρ : Representation ℂ (GL (Fin N) k) V} (h : IsCuspidal ρ) :
    IsCuspidal (ρ.comp (GlobalTheory.CuspRep.invT N k)) := by
  refine ⟨isSmooth_comp_invT h.1, fun s d e hne => ?_⟩
  let e' : (Σ a, Fin (d (Fin.revPerm a))) ≃ Fin N :=
    (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).trans e
  have he : ∀ x, (e'.symm x).1 = Fin.rev (e.symm x).1 := fun x => by
    have h1 : e'.symm x = (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) := rfl
    obtain ⟨⟨a, i⟩, hq⟩ : ∃ q, (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm).symm (e.symm x) = q :=
      ⟨_, rfl⟩
    have h2 := congrArg (Equiv.sigmaCongrLeft (β := fun a => Fin (d a)) Fin.revPerm) hq
    rw [Equiv.apply_symm_apply, Equiv.sigmaCongrLeft_apply] at h2
    rw [h1, hq, h2]
    simp
  have he' : ∀ x, (e.symm x).1 = Fin.rev (e'.symm x).1 := fun x => by rw [he, Fin.rev_rev]
  have hne' : unipRad k e' ≠ ⊥ := by
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    refine Subgroup.ne_bot_iff_exists_ne_one.2 ⟨⟨_, invT_mem_unipRad e e' he hg⟩, fun h1 => hg1 ?_⟩
    have h2 : GlobalTheory.CuspRep.invT N k g = 1 := congrArg Subtype.val h1
    refine Subtype.ext ?_
    show g = 1
    rw [← invT_invT' N g, h2, map_one]
  have hs := h.2 s (fun a => d (Fin.revPerm a)) e' hne'
  have htop : twKer ρ (unipRad k e') 1 = ⊤ := Submodule.Quotient.subsingleton_iff.1 hs
  show Subsingleton (V ⧸ twKer _ _ 1)
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff, ← htop]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  refine Submodule.subset_span ⟨⟨GlobalTheory.CuspRep.invT N k n, invT_mem_unipRad e' e he' n.2⟩, v, ?_⟩
  simp [invT_invT']

end Tilde

end WhittakerInverseTranspose

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
end
