module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightsCloseOfHeightGammaConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GmultEqZeroOfInj
noncomputable section
namespace GlobalTheory.PhiGam.Compare
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries

theorem inj_iff_surj {k U : Type} [Field k] [AddCommGroup U] [Module k U] (S : Module.End k U)
    (P Q : Submodule k U) (hP : ∀ p ∈ P, S p ∈ P) (hQ : ∀ p ∈ Q, S p ∈ Q)
    [hfin : FiniteDimensional k (P.map Q.mkQ)] :
    (∀ p ∈ P, S p ∈ Q → p ∈ Q) ↔ ∀ y ∈ P, ∃ p ∈ P, y - S p ∈ Q := by
  have hSQ : Q ≤ Q.comap S := fun p hp => hQ p hp
  let Sq := Q.mapQ Q S hSQ
  have hSq : ∀ z ∈ P.map Q.mkQ, Sq z ∈ P.map Q.mkQ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨S p, hP p hp, rfl⟩
  constructor
  · intro hinj
    have hi : Function.Injective (Sq.restrict hSq) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨_, p, hp, rfl⟩ hz
      have h1 : Q.mkQ (S p) = 0 := congrArg Subtype.val hz
      have h2 : p ∈ Q := hinj p hp ((Submodule.Quotient.mk_eq_zero _).mp h1)
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h2)
    have hs := LinearMap.injective_iff_surjective.mp hi
    intro y hy
    obtain ⟨⟨_, p, hp, rfl⟩, hz⟩ := hs ⟨Q.mkQ y, y, hy, rfl⟩
    have h1 : Q.mkQ (S p) = Q.mkQ y := congrArg Subtype.val hz
    exact ⟨p, hp, (Submodule.Quotient.eq _).mp h1.symm⟩
  · intro hsur
    have hs : Function.Surjective (Sq.restrict hSq) := by
      rintro ⟨_, y, hy, rfl⟩
      obtain ⟨p, hp, h⟩ := hsur y hy
      refine ⟨⟨Q.mkQ p, p, hp, rfl⟩, Subtype.ext ?_⟩
      exact ((Submodule.Quotient.eq _).mpr h).symm
    have hi := LinearMap.injective_iff_surjective.mpr hs
    intro p hp h
    have h0 : Sq.restrict hSq ⟨Q.mkQ p, p, hp, rfl⟩ = 0 :=
      Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)
    have h1 := (injective_iff_map_eq_zero _).mp hi _ h0
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h1)

theorem gmult_eq_zero_of_inj {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (P Q : Submodule k U) (x : k)
    (hP : ∀ p ∈ P, (T - algebraMap k (Module.End k U) x) p ∈ P)
    (hQ : ∀ p ∈ Q, (T - algebraMap k (Module.End k U) x) p ∈ Q)
    (h : ∀ p ∈ P, (T - algebraMap k (Module.End k U) x) p ∈ Q → p ∈ Q) : gmult T P Q x = 0 := by
  unfold gmult
  set S := T - algebraMap k (Module.End k U) x with hS
  have h1 : ∀ m : ℕ, ∀ p ∈ P, (S ^ m) p ∈ Q → p ∈ Q := by
    intro m
    induction m with
    | zero => intro p _ hp; simpa using hp
    | succ m ih =>
      intro p hp hq
      rw [pow_succ, Module.End.mul_apply] at hq
      exact h p hp (ih _ (hP p hp) hq)
  have hmono : Monotone fun m : ℕ => Q.comap (S ^ m) := by
    refine monotone_nat_of_le_succ fun m p hp => ?_
    rw [Submodule.mem_comap] at hp ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hQ _ hp
  have htop : Q.submoduleOf (P ⊓ ⨆ m : ℕ, Q.comap (S ^ m)) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨p, hp, hp'⟩ _
    obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hp'
    exact h1 m p hp hm
  rw [htop]
  exact Module.finrank_zero_of_subsingleton

variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]

theorem graded_inj {l : ℕ} (R : RingPG k l) {g : V →ₗ[k] V} (hg : Semi R.γ g) {N : Submodule k⟦X⟧ V}
    (hN : N.FG) (hC : CondC g N) (b : ℤ) (y : k) (h : sen g N (y + b) = 0) :
    ∀ x ∈ sh b N, nab g x - y • x ∈ sh (b + 1) N → x ∈ sh (b + 1) N := by
  haveI := Window.finite_quot hN
  obtain ⟨h1, -⟩ := Window.bij_of_gmult_zero (nab g) (N.restrictScalars k) ((sh 1 N).restrictScalars k)
    (fun p hp => Window.nab_mem hC hp) (fun p hp => Window.nab_mem_sh R hg hC 1 hp) (y + b) h
  have hv : vv k ≠ 0 := vv_ne_zero k
  intro x hx hx'
  obtain ⟨n, hn, rfl⟩ := mem_sh_iff_exists.mp hx
  obtain ⟨n', hn', e⟩ := Window.nab_shift R hg hC b hn
  obtain ⟨t, ht, e'⟩ := mem_sh_iff_exists.mp hx'
  have hc : y • vv k ^ b • n = vv k ^ b • y • n := by
    rw [← smul_assoc, const_smul_eq, mul_comm, mul_smul, ← mul_one (algebraMap k k⸨X⸩ y), ← const_smul_eq,
      smul_assoc, one_smul]
  rw [e, hc, ← smul_sub, zpow_add_one₀ hv, mul_smul] at e'
  have e2 := smul_right_injective V (zpow_ne_zero b hv) e'
  have : n ∈ sh 1 N := h1 n hn (mem_sh_iff_exists.mpr ⟨t - n', N.sub_mem ht hn', by
    rw [zpow_one, smul_sub, e2, add_smul]; abel⟩)
  obtain ⟨r, hr, rfl⟩ := mem_sh_iff_exists.mp this
  exact mem_sh_iff_exists.mpr ⟨r, hr, by rw [zpow_add₀ hv, mul_smul]⟩

theorem sen_compare : ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l) {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V] [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V] [FiniteDimensional k⸨X⸩ V] (g : V →ₗ[k] V), Semi R.γ g → ∀ N₁ N₂ : Submodule k⟦X⟧ V, IsLat N₁ → IsLat N₂ → CondC g N₁ → CondC g N₂ → ∀ s : ℕ, sh s N₁ ≤ N₂ → N₂ ≤ sh (-s) N₁ → ∀ y : k, sen g N₂ y ≠ 0 → ∃ j : ℤ, |j| ≤ s ∧ sen g N₁ (y + j) ≠ 0 := by
  intro k _ l _ _ R V _ _ _ _ _ _ _ _ g hg N₁ N₂ h₁ h₂ c₁ c₂ s lo hi y hy
  by_contra hcon
  push_neg at hcon
  apply hy
  set S : Module.End k V := nab g - algebraMap k (Module.End k V) y with hSdef
  have hS : ∀ p, S p = nab g p - y • p := fun p => rfl
  have st : ∀ N : Submodule k⟦X⟧ V, CondC g N → ∀ b : ℤ, ∀ p ∈ sh b N, S p ∈ sh b N := fun N c b p hp => by
    rw [hS]
    exact (sh b N).sub_mem (Window.nab_mem_sh R hg c b hp) (((sh b N).restrictScalars k).smul_mem y hp)
  have st2 : ∀ p ∈ N₂, S p ∈ N₂ := by
    have := st N₂ c₂ 0
    rwa [sh_zero_eq] at this
  have key : ∀ m : ℕ, m ≤ 2 * s + 1 → ∀ x ∈ N₂, ∃ p ∈ N₂, x - S p ∈ sh (-s + m) N₁ := by
    intro m
    induction m with
    | zero => intro _ x hx; exact ⟨0, N₂.zero_mem, by simpa using hi hx⟩
    | succ m ih =>
      intro hm x hx
      obtain ⟨p, hp, hp'⟩ := ih (by omega) x hx
      set b : ℤ := -s + m with hb
      have hsen := hcon b (by rw [abs_le]; omega)
      have hf := Window.finite_quot (h₁.shift b).1
      rw [sh_sh_eq, add_comm] at hf
      haveI : FiniteDimensional k (((N₂ ⊓ sh b N₁).restrictScalars k).map
          ((sh (b + 1) N₁).restrictScalars k).mkQ) :=
        Submodule.finiteDimensional_of_le (S₂ := ((sh b N₁).restrictScalars k).map
          ((sh (b + 1) N₁).restrictScalars k).mkQ) (Submodule.map_mono fun z hz => hz.2)
      obtain ⟨q, hq, hq'⟩ := (inj_iff_surj S ((N₂ ⊓ sh b N₁).restrictScalars k)
        ((sh (b + 1) N₁).restrictScalars k) (fun z hz => ⟨st2 z hz.1, st N₁ c₁ b z hz.2⟩)
        (fun z hz => st N₁ c₁ _ z hz)).mp
        (fun z hz hz' => graded_inj R hg h₁.1 c₁ b y hsen z hz.2 hz') (x - S p)
        ⟨N₂.sub_mem hx (st2 p hp), hp'⟩
      refine ⟨p + q, N₂.add_mem hp hq.1, ?_⟩
      rw [map_add (f := _), ← sub_sub, Nat.cast_succ, ← add_assoc]
      exact hq'
  haveI := Window.finite_quot h₂.1
  refine gmult_eq_zero_of_inj (nab g) _ _ y st2 (st N₂ c₂ 1) ?_
  refine (inj_iff_surj S (N₂.restrictScalars k) ((sh 1 N₂).restrictScalars k) st2 (st N₂ c₂ 1)).mpr ?_
  intro x hx
  obtain ⟨p, hp, hp'⟩ := key (2 * s + 1) le_rfl x hx
  refine ⟨p, hp, sh_le_sh 1 lo ?_⟩
  rw [sh_sh_eq]
  convert hp' using 2
  push_cast; ring

end GlobalTheory.PhiGam.Compare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightsCloseOfHeightGammaConditions
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem sen_near_of_abc : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (D : ModPG R n (Vc k m)) {r : ℕ} (Dt : TopData n r) (N₁ N₂ : Lats k n m),
    ABC D Dt.w Dt.wst N₁ → ABC D Dt.w Dt.wst N₂ → ∀ i y, sen (D.γ i) (N₂ i) y ≠ 0 →
      ∃ j : ℤ, |j| ≤ Dt.sg l i ∧ sen (D.γ i) (N₁ i) (y + j) ≠ 0 := by
  intro k _ l n m _ _ _ R D r Dt N₁ N₂ h₁ h₂ i y hy
  obtain ⟨hL₁, hAB₁, hC₁⟩ := h₁
  obtain ⟨hL₂, hAB₂, hC₂⟩ := h₂
  have e12 := CloseTw.main D Dt.h Dt.w N₁ N₂ hL₁ hL₂ hAB₁ hAB₂ i
  have e21 := CloseTw.main D Dt.h Dt.w N₂ N₁ hL₂ hL₁ hAB₂ hAB₁ i
  have hle : N₂ i ≤ sh (-(sg l Dt.h i : ℤ)) (N₁ i) := by
    have h' := sh_le_sh (-(sg l Dt.h i : ℤ)) e21
    rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h'
  exact Compare.sen_compare R (D.γ i) (D.γ_semi i) (N₁ i) (N₂ i) (hL₁ i) (hL₂ i) (hC₁ i) (hC₂ i) _ e12 hle y hy

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightsCloseOfHeightGammaConditionsStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.senWeights_close_of_height_gamma_conditions : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) {r : ℕ} (Dt : TopData n r) (N₁ N₂ : Lats k n m), ABC D Dt.w Dt.wst N₁ → ABC D Dt.w Dt.wst N₂ → ∀ i y, sen (D.γ i) (N₂ i) y ≠ 0 → ∃ j : ℤ, |j| ≤ Dt.sg l i ∧ sen (D.γ i) (N₁ i) (y + j) ≠ 0 := by
  first | exact @GlobalTheory.Models.sen_near_of_abc | exact GlobalTheory.Models.sen_near_of_abc | (intros; apply GlobalTheory.Models.sen_near_of_abc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumPart
section -- merged from Development.AbelianVarietyTheory.Counterexamples.NonGaloisSurvey.UnitsOfFieldDD
noncomputable section
namespace GlobalTheory.Survey.UnitsOfFieldRootsOfUnity
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

section Sum
variable {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L)

def sumEquiv (h : IsSumLat i i') : (T.V × T'.V) ≃ₗ[LL] T''.V :=
  LinearEquiv.ofBijective (i.f.coprod i'.f) h.1

theorem sumEquiv_apply (h : IsSumLat i i') (x : T.V) (y : T'.V) :
    sumEquiv i i' h (x, y) = i.f x + i'.f y := rfl

theorem _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.symm_act (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.IsSumLat i i') (g : G) (z : T''.V) :
    (_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm (T''.ρ g z) =
      (T.ρ g ((_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm z).1,
        T'.ρ g ((_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).symm z).2) := by
  apply (_root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv i i' h).injective
  rw [LinearEquiv.apply_symm_apply, _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv_apply, i.equiv, i'.equiv, ← map_add (f := _),
    ← _root_.GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumEquiv_apply i i' h, Prod.mk.eta, LinearEquiv.apply_symm_apply]

def pr₁ (h : IsSumLat i i') : LatHom T''.L T.L where
  f := LinearMap.fst LL _ _ ∘ₗ (sumEquiv i i' h).symm.toLinearMap
  equiv := fun g z => by simp [symm_act]
  cont := by
    have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
    exact IsModuleTopology.continuous_of_linearMap _
  T_le := fun z hz => by
    obtain ⟨x, hx, y, hy, rfl⟩ := h.2 z hz
    rw [← sumEquiv_apply i i' h]
    simpa using hx

def pr₂ (h : IsSumLat i i') : LatHom T''.L T'.L where
  f := LinearMap.snd LL _ _ ∘ₗ (sumEquiv i i' h).symm.toLinearMap
  equiv := fun g z => by simp [symm_act]
  cont := by
    have : ContinuousSMul LL T'.V := IsModuleTopology.toContinuousSMul LL T'.V
    exact IsModuleTopology.continuous_of_linearMap _
  T_le := fun z hz => by
    obtain ⟨x, hx, y, hy, rfl⟩ := h.2 z hz
    rw [← sumEquiv_apply i i' h]
    simpa using hy

end Sum

theorem latHom_ext {T T' : LocLat G Qp LL O} {f g : LatHom T.L T'.L} (h : ∀ x, f.f x = g.f x) :
    f = g := by
  cases f; cases g
  congr 1
  exact LinearMap.ext h

theorem map_of_zero {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (h : ∀ x, f.f x = 0)
    (x : W.DD T) : W.map f x = 0 := by
  have : f = latComp (latSmul T' (0 : O)) f := latHom_ext fun y => by
    simp [latComp, latSmul, h]
  rw [this, W.map_comp, W.map_latSmul, zero_smul]

theorem sum_N {T T' T'' : LocLat G Qp LL O} (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (hT'' : IsCrys PD T''.ρ)
    (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) (h : IsSumLat i i') (x : W.DD T) (y : W.DD T') :
    W.map i x + W.map i' y ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T') := by
  have e1 : ∀ a, (pr₁ i i' h).f (i.f a) = a := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (a, 0)
    rw [sumEquiv_apply, map_zero, add_zero] at this
    simp [pr₁, this]
  have e2 : ∀ a, (pr₁ i i' h).f (i'.f a) = 0 := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (0, a)
    rw [sumEquiv_apply, map_zero, zero_add] at this
    simp [pr₁, this]
  have e3 : ∀ a, (pr₂ i i' h).f (i.f a) = 0 := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (a, 0)
    rw [sumEquiv_apply, map_zero, add_zero] at this
    simp [pr₂, this]
  have e4 : ∀ a, (pr₂ i i' h).f (i'.f a) = a := fun a => by
    have := (sumEquiv i i' h).symm_apply_apply (0, a)
    rw [sumEquiv_apply, map_zero, zero_add] at this
    simp [pr₂, this]
  constructor
  · intro hz
    have h1 := W.map_N (pr₁ i i' h) hT'' hT _ hz
    have h2 := W.map_N (pr₂ i i' h) hT'' hT' _ hz
    rw [map_add (f := _), ← W.map_comp, ← W.map_comp] at h1 h2
    rw [show latComp (pr₁ i i' h) i = latId T from latHom_ext e1, W.map_id,
      map_of_zero (latComp (pr₁ i i' h) i') e2, add_zero] at h1
    rw [show latComp (pr₂ i i' h) i' = latId T' from latHom_ext e4, W.map_id,
      map_of_zero (latComp (pr₂ i i' h) i) e3, zero_add] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨hx, hy⟩
    exact (W.N T'').add_mem (W.map_N i hT hT'' x hx) (W.map_N i' hT' hT'' y hy)

theorem sumFor_of_crys
    (hc : ∀ (T T' T'' : LocLat G Qp LL O) (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L),
      IsSumLat i i' → IsCrys PD T.ρ → IsCrys PD T'.ρ → IsCrys PD T''.ρ) : SumFor W := by
  intro T T' T'' hT hT' i i' h
  have key : ∀ a b, (pr₁ i i' h).f (i.f a + i'.f b) = a ∧ (pr₂ i i' h).f (i.f a + i'.f b) = b :=
    fun a b => by
      have := (sumEquiv i i' h).symm_apply_apply (a, b)
      rw [sumEquiv_apply] at this
      simp only [pr₁, pr₂, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
      simp
  have hbij : Function.Bijective ((W.map i).coprod (W.map i')) := by
    constructor
    · rw [injective_iff_map_eq_zero]
      rintro ⟨x, y⟩ hxy
      simp only [LinearMap.coprod_apply] at hxy
      have h1 := congrArg (W.map (pr₁ i i' h)) hxy
      have h2 := congrArg (W.map (pr₂ i i' h)) hxy
      rw [map_add (f := _), ← W.map_comp, ← W.map_comp, map_zero] at h1 h2
      rw [show latComp (pr₁ i i' h) i = latId T from latHom_ext fun a => by
          simpa [latComp, latId] using (key a 0).1, W.map_id,
        map_of_zero (latComp (pr₁ i i' h) i') (fun a => by simpa [latComp] using (key 0 a).1),
        add_zero] at h1
      rw [show latComp (pr₂ i i' h) i' = latId T' from latHom_ext fun a => by
          simpa [latComp, latId] using (key 0 a).2, W.map_id,
        map_of_zero (latComp (pr₂ i i' h) i) (fun a => by simpa [latComp] using (key a 0).2),
        zero_add] at h2
      simp [h1, h2]
    · intro z
      refine ⟨(W.map (pr₁ i i' h) z, W.map (pr₂ i i' h) z), ?_⟩
      simp only [LinearMap.coprod_apply]
      rw [← W.map_comp, ← W.map_comp, ← W.map_latAdd,
        show latAdd (latComp i (pr₁ i i' h)) (latComp i' (pr₂ i i' h)) = latId T'' from
          latHom_ext fun a => by
            obtain ⟨⟨x, y⟩, rfl⟩ := (sumEquiv i i' h).surjective a
            rw [sumEquiv_apply]
            change i.f ((pr₁ i i' h).f _) + i'.f ((pr₂ i i' h).f _) = _
            rw [(key x y).1, (key x y).2]
            rfl, W.map_id]
  refine ⟨LinearEquiv.ofBijective _ hbij, fun x y => rfl, fun x y => ?_, fun g x y => ?_,
    fun x y => sum_N hT hT' (hc T T' T'' i i' h hT hT') i i' h x y⟩
  · change W.φD T'' (W.map i x + W.map i' y) = W.map i _ + W.map i' _
    rw [map_add (f := _), ← W.map_φ, ← W.map_φ]
    rfl
  · change W.γD T'' g (W.map i x + W.map i' y) = W.map i _ + W.map i' _
    rw [map_add (f := _), ← W.map_γ, ← W.map_γ]
    rfl

end GlobalTheory.Survey.UnitsOfFieldRootsOfUnity
end
end

namespace GlobalTheory.WachSum

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

theorem sumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts.SumPart l P H := by
  intro K s LL h
  exact GlobalTheory.Survey.UnitsOfFieldRootsOfUnity.sumFor_of_crys fun _ _ _ i i' hs hT hT' =>
    GlobalTheory.Cmp.WachMonoidal.isCrys_of_isSumLat i i' hT hT' hs

end GlobalTheory.WachSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCounts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCounts
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg.Shape

def kerProd {O : Type} [CommRing O] (c : O) {ι M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] :
    LinearMap.ker (c • LinearMap.id : (ι → M) × N →ₗ[O] (ι → M) × N) ≃
      (ι → LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) ×
        LinearMap.ker (c • LinearMap.id : N →ₗ[O] N) where
  toFun x := (fun i => ⟨x.1.1 i, by
      have h := LinearMap.mem_ker.1 x.2
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.smul_apply, Pi.zero_apply] at h
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact h.1 i⟩, ⟨x.1.2, by
      have h := LinearMap.mem_ker.1 x.2
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_zero, Prod.snd_zero] at h
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact h.2⟩)
  invFun y := ⟨(fun i => (y.1 i).1, y.2.1), by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff,
        Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.smul_apply,
        Pi.zero_apply]
      refine ⟨fun i => ?_, ?_⟩
      · have := (y.1 i).2
        simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using this
      · have := y.2.2
        simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using this⟩
  left_inv x := rfl
  right_inv y := rfl

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem card_ker_prod [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {H : Type} [AddCommGroup H] [Module O H] {a : ℕ} {F : Type} [AddCommGroup F] [Module O F]
    (φ : H ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) (n : ℕ) :
    Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : H →ₗ[O] H)) =
      (Nat.card (IsLocalRing.ResidueField O) ^ n) ^ a *
        Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) := by
  have hK : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Formalism.NG.KO O →ₗ[O] Formalism.NG.KO O)) =
      Nat.card (IsLocalRing.ResidueField O) ^ n :=
    (levKO_card hϖ (LinearEquiv.refl O (Formalism.NG.KO O)) n).2
  have h1 : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : H →ₗ[O] H)) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id :
        (Fin a → Formalism.NG.KO O) × F →ₗ[O] (Fin a → Formalism.NG.KO O) × F)) :=
    Nat.card_congr (levCongr φ (ϖ ^ n))
  rw [h1, Nat.card_congr (kerProd (ϖ ^ n)), Nat.card_prod, Nat.card_fun, hK, Nat.card_eq_fintype_card (α := Fin a), Fintype.card_fin]

theorem cyclic_of_card_ker_le [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F]
    (h : Nat.card (LinearMap.ker (ϖ • LinearMap.id : F →ₗ[O] F)) ≤
      Nat.card (IsLocalRing.ResidueField O)) :
    ∃ c0 : F, ∀ y : F, ∃ a : O, y = a • c0 := by
  set g : F →ₗ[O] F := ϖ • LinearMap.id with hg
  have hQ : Nat.card (F ⧸ LinearMap.range g) ≤ Nat.card (IsLocalRing.ResidueField O) := by
    have e1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range g)
    have e2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g)
    have e3 := Nat.card_congr (LinearMap.quotKerEquivRange g).toEquiv
    have hr : 0 < Nat.card (LinearMap.range g) := Nat.card_pos
    rw [e3, e1, mul_comm (Nat.card (LinearMap.ker g))] at e2
    rw [Nat.eq_of_mul_eq_mul_left hr e2]
    exact h
  have hx : ∃ x : F, ∀ y : F, y ∈ Submodule.span O {x} ⊔ LinearMap.range g := by
    by_cases hs : Subsingleton (F ⧸ LinearMap.range g)
    · refine ⟨0, fun y => ?_⟩
      have : (Submodule.Quotient.mk y : F ⧸ LinearMap.range g) = 0 := Subsingleton.elim _ _
      exact Submodule.mem_sup_right ((Submodule.Quotient.mk_eq_zero _).1 this)
    · rw [not_subsingleton_iff_nontrivial] at hs
      haveI : Finite (F ⧸ LinearMap.range g) :=
        Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
      obtain ⟨xb, hxb⟩ := exists_ne (0 : F ⧸ LinearMap.range g)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
      set t := LinearMap.toSpanSingleton O (F ⧸ LinearMap.range g)
        (Submodule.Quotient.mk x) with ht
      have hker : LinearMap.ker t = IsLocalRing.maximalIdeal O := by
        symm
        apply (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le
        · intro htop
          apply hxb
          have h1 : (1 : O) ∈ LinearMap.ker t := htop ▸ Submodule.mem_top
          simpa [ht] using h1
        · rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
            LinearMap.mem_ker, ht, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
            Submodule.Quotient.mk_eq_zero]
          exact ⟨x, rfl⟩
      have hrange : LinearMap.range t = ⊤ := by
        by_contra hne
        obtain ⟨z, hz⟩ : ∃ z, z ∉ LinearMap.range t := by
          by_contra hall
          push_neg at hall
          exact hne (eq_top_iff.2 fun z _ => hall z)
        have hlt : Nat.card (LinearMap.range t) < Nat.card (F ⧸ LinearMap.range g) :=
          Finite.card_subtype_lt (p := fun w => w ∈ LinearMap.range t) hz
        have hc : Nat.card (LinearMap.range t) = Nat.card (IsLocalRing.ResidueField O) := by
          rw [← Nat.card_congr (LinearMap.quotKerEquivRange t).toEquiv, hker]
          rfl
        omega
      refine ⟨x, fun y => ?_⟩
      obtain ⟨a, ha⟩ : ∃ a, t a = Submodule.Quotient.mk y := by
        have hy : (Submodule.Quotient.mk y : F ⧸ LinearMap.range g) ∈ LinearMap.range t :=
          hrange ▸ Submodule.mem_top
        exact hy
      rw [ht, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.eq] at ha
      have hy : y = a • x - (a • x - y) := by abel
      rw [hy]
      exact Submodule.sub_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
        (Submodule.mem_sup_right ha)
  obtain ⟨x, hx⟩ := hx
  have hfg : (⊤ : Submodule O F).FG :=
    ⟨(Set.finite_univ (α := F)).toFinset, by simp⟩
  have hle : (⊤ : Submodule O F) ≤ Submodule.span O {x} := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro y _
    have hsub : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • (⊤ : Submodule O F) := by
      rintro _ ⟨z, rfl⟩
      have hm : ϖ ∈ IsLocalRing.maximalIdeal O := by
        rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
      exact Submodule.smul_mem_smul hm Submodule.mem_top
    have hmono : Submodule.span O {x} ⊔ LinearMap.range g ≤
        Submodule.span O {x} ⊔ IsLocalRing.maximalIdeal O • (⊤ : Submodule O F) :=
      sup_le_sup_left hsub _
    exact hmono (hx y)
  refine ⟨x, fun y => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle Submodule.mem_top)
  exact ⟨a, ha.symm⟩

theorem quotShape_of_counts : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X) (d a : ℕ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F], (Hc ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) →
    (∃ C : ℕ, ∀ n : ℕ, 0 < n →
      Nat.card (IsLocalRing.ResidueField O) ^ (n * d) ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ∧
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ≤ C * Nat.card (IsLocalRing.ResidueField O) ^ (n * d)) →
    Nat.card (LinearMap.ker (ϖ ^ 1 • LinearMap.id : Hc →ₗ[O] Hc)) ≤ Nat.card (IsLocalRing.ResidueField O) ^ (d + 1) →
    Formalism.RepresentationBoundsCohomology.JT.QuotShape Hc ⊥ d := by
  intro O _ _ _ _ ϖ hϖ X _ _ Hc d a F _ _ _ φ hC h1
  have hq : 2 ≤ Nat.card (IsLocalRing.ResidueField O) := Finite.one_lt_card
  have hcard := card_ker_prod hϖ φ
  have hF1 : ∀ n : ℕ, 1 ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) :=
    fun n => Nat.card_pos
  have hFle : ∀ n : ℕ, Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) ≤ Nat.card F :=
    fun n => Nat.card_le_card_of_injective _ Subtype.val_injective
  obtain ⟨C, hC⟩ := hC
  have hlt : ∀ m : ℕ, m < Nat.card (IsLocalRing.ResidueField O) ^ m := fun m =>
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq m)
  have had : a = d := by
    rcases lt_trichotomy a d with h | h | h
    · exfalso
      have hn := (hC (Nat.card F + 1) (Nat.succ_pos _)).1
      rw [hcard] at hn
      set q := Nat.card (IsLocalRing.ResidueField O)
      set n := Nat.card F + 1
      have h2 : (q ^ n) ^ a * q ^ n ≤ q ^ (n * d) := by
        rw [← pow_succ, ← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left n h)
      have hpos : 0 < (q ^ n) ^ a := by positivity
      have h3 : (q ^ n) ^ a * q ^ n ≤ (q ^ n) ^ a * Nat.card F :=
        h2.trans (hn.trans (Nat.mul_le_mul_left _ (hFle n)))
      have h4 := Nat.le_of_mul_le_mul_left h3 hpos
      have h5 := hlt n
      omega
    · exact h
    · exfalso
      have hn := (hC (C + 1) (Nat.succ_pos _)).2
      rw [hcard] at hn
      set q := Nat.card (IsLocalRing.ResidueField O)
      set n := C + 1
      have h2 : q ^ (n * d) * q ^ n ≤ (q ^ n) ^ a := by
        rw [← pow_add, ← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (by nlinarith)
      have h3 : (q ^ n) ^ a ≤ (q ^ n) ^ a * Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) :=
        Nat.le_mul_of_pos_right _ (hF1 n)
      have hpos : 0 < q ^ (n * d) := by positivity
      have h4 : q ^ (n * d) * q ^ n ≤ q ^ (n * d) * C := by
        rw [mul_comm (q ^ (n * d)) C]; exact h2.trans (h3.trans hn)
      have h5 := Nat.le_of_mul_le_mul_left h4 hpos
      have h6 := hlt n
      omega
  subst had
  have hsoc : Nat.card (LinearMap.ker (ϖ • LinearMap.id : F →ₗ[O] F)) ≤
      Nat.card (IsLocalRing.ResidueField O) := by
    have h1' := h1
    rw [hcard 1] at h1'
    simp only [pow_one] at h1'
    rw [pow_succ] at h1'
    have hpos : 0 < Nat.card (IsLocalRing.ResidueField O) ^ a := by positivity
    have := Nat.le_of_mul_le_mul_left h1' hpos
    exact this
  obtain ⟨c0, hc0⟩ := cyclic_of_card_ker_le hϖ hsoc
  have hbot : (⊥ : Submodule O X).comap Hc.subtype = ⊥ := by
    rw [Submodule.comap_bot, Submodule.ker_subtype]
  let e0 : (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) ≃ₗ[O] Hc :=
    Submodule.quotEquivOfEqBot _ hbot
  let ι : (Fin a → Formalism.NG.KO O) →ₗ[O] (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) :=
    e0.symm.toLinearMap ∘ₗ φ.symm.toLinearMap ∘ₗ LinearMap.inl O _ F
  let π : (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) →ₗ[O] F :=
    LinearMap.snd O _ F ∘ₗ φ.toLinearMap ∘ₗ e0.toLinearMap
  refine ⟨F, inferInstance, inferInstance, ι, π, ?_, ?_, c0, hc0⟩
  · intro u v huv
    have := congrArg (fun z => (φ (e0 z)).1) huv
    simpa only [ι, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.inl_apply] using this
  · intro y
    constructor
    · intro hy
      refine ⟨(φ (e0 y)).1, ?_⟩
      apply e0.injective
      apply φ.injective
      simp only [π, LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
        LinearEquiv.coe_coe] at hy
      simp only [ι, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact Prod.ext rfl hy.symm
    · rintro ⟨u, rfl⟩
      simp only [ι, π, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.inl_apply, LinearMap.snd_apply]

end GlobalTheory.ShapeNeg.Shape
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionShapeOfTorsionCountsStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_shape_of_torsion_counts : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X) (d a : ℕ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F], (Hc ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) →
    (∃ C : ℕ, ∀ n : ℕ, 0 < n →
      Nat.card (IsLocalRing.ResidueField O) ^ (n * d) ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ∧
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ≤ C * Nat.card (IsLocalRing.ResidueField O) ^ (n * d)) →
    Nat.card (LinearMap.ker (ϖ ^ 1 • LinearMap.id : Hc →ₗ[O] Hc)) ≤ Nat.card (IsLocalRing.ResidueField O) ^ (d + 1) →
    Formalism.RepresentationBoundsCohomology.JT.QuotShape Hc ⊥ d := by
  first | exact @GlobalTheory.ShapeNeg.Shape.quotShape_of_counts | exact GlobalTheory.ShapeNeg.Shape.quotShape_of_counts | (intros; apply GlobalTheory.ShapeNeg.Shape.quotShape_of_counts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormula
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg.SeqCount

open Formalism.NG ReciprocityTheory.ChartRestriction.T2

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M]

theorem exists_pow_smul_eq {ϖ : O} (hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m) (n : ℕ) (m : M) :
    ∃ m' : M, ϖ ^ n • m' = m := by
  induction n generalizing m with
  | zero => exact ⟨m, by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih m
    obtain ⟨b, hb⟩ := hdiv a
    exact ⟨b, by rw [pow_succ, mul_smul, hb, ha]⟩

theorem lev_val_injective {c : O} : Function.Injective (Lev.val : Lev M c → M) :=
  fun _ _ h => Lev.ext h

def levelCocycleToModuleCocycle (ρ : Representation O G M) (c : O) : Z1 (levRep ρ c) →ₗ[O] coZ1s ρ where
  toFun f := ⟨fun g => (f.1 g).val, fun g h => by
    have := ((mem_Z1_iff_cocycle _ _).1 f.2).2 g h
    show (f.1 (g * h)).val = (f.1 g).val + ρ g (f.1 h).val
    rw [this, Lev.val_add, levRep_val]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def levelH1ToModuleH1 (ρ : Representation O G M) (c : O) : H1 (levRep ρ c) →ₗ[O] H1z ρ :=
  Submodule.mapQ _ _ (levelCocycleToModuleCocycle ρ c) (by
    intro f hf
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
    exact ⟨m.val, funext fun g => by
      have h2 : f.1 g = levRep ρ c g m - m := hm g
      show ρ g m.val - m.val = (f.1 g).val
      rw [h2]; rfl⟩)

theorem valuation_H1_mk (ρ : Representation O G M) (c : O) (f : Z1 (levRep ρ c)) :
    levelH1ToModuleH1 ρ c (Submodule.Quotient.mk f) = Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) := rfl

theorem valuation_H1_mem (ρ : Representation O G M) (c : O) (x : H1 (levRep ρ c)) : levelH1ToModuleH1 ρ c x ∈ HcLC ρ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨levelCocycleToModuleCocycle ρ c f, ?_, rfl⟩
  show IsLocallyConstant (fun g => (f.1 g).val)
  have h1 : IsLocallyConstant f.1 := (IsLocallyConstant.iff_continuous f.1).2 ((mem_Z1_iff_cocycle _ _).1 f.2).1
  exact h1.comp _

theorem smul_valuation_H1 (ρ : Representation O G M) (c : O) (x : H1 (levRep ρ c)) : c • levelH1ToModuleH1 ρ c x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [valuation_H1_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨0, funext fun g => ?_⟩
  show ρ g 0 - 0 = c • (f.1 g).val
  rw [Lev.smul_val, map_zero, sub_zero]

def phi (ρ : Representation O G M) (c : O) :
    H1 (levRep ρ c) →ₗ[O] LinearMap.ker (c • LinearMap.id : HcLC ρ →ₗ[O] HcLC ρ) :=
  LinearMap.codRestrict _ (LinearMap.codRestrict (HcLC ρ) (levelH1ToModuleH1 ρ c) (valuation_H1_mem ρ c)) (fun x => by
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact Subtype.ext (smul_valuation_H1 ρ c x))

theorem phi_surjective (ρ : Representation O G M) (c : O) (hdiv : ∀ m : M, ∃ m' : M, c • m' = m)
    (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) : Function.Surjective (phi ρ c) := by
  rintro ⟨⟨y, hy⟩, hk⟩
  obtain ⟨z, hz, rfl⟩ := hy
  have hk' : c • (Submodule.mkQ _ z : H1z ρ) = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.1 hk)
    simpa using this
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk'
  obtain ⟨m, hm⟩ := hk'
  obtain ⟨m', hm'⟩ := hdiv m
  have hz2 : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := z.2
  have hzlc : IsLocallyConstant (z.1 : G → M) := hz
  let w : G → M := fun g => z.1 g - (ρ g m' - m')
  have hw : ∀ g, c • w g = 0 := fun g => by
    have h1 : ρ g m - m = c • z.1 g := congrFun hm g
    show c • (z.1 g - (ρ g m' - m')) = 0
    rw [smul_sub, smul_sub, ← map_smul (ρ g) c m', hm', h1, sub_self]
  have hwlc : IsLocallyConstant w := hzlc.sub ((hlc m').sub (IsLocallyConstant.const m'))
  have hwc : ∀ g h, w (g * h) = w g + ρ g (w h) := fun g h => by
    show z.1 (g * h) - (ρ (g * h) m' - m') = (z.1 g - (ρ g m' - m')) + ρ g (z.1 h - (ρ h m' - m'))
    rw [hz2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel
  have hf : (fun g => Lev.mk (w g) (hw g) : G → Lev M c) ∈ Z1 (levRep ρ c) := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩
    · exact (IsLocallyConstant.desc _ Lev.val hwlc lev_val_injective).continuous
    · show w (g * h) = w g + ρ g (w h)
      exact hwc g h
  refine ⟨Submodule.Quotient.mk ⟨_, hf⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show levelH1ToModuleH1 ρ c (Submodule.Quotient.mk ⟨_, hf⟩) = Submodule.mkQ _ z
  rw [valuation_H1_mk, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-m', funext fun g => ?_⟩
  show ρ g (-m') - -m' = (z.1 g - (ρ g m' - m')) - z.1 g
  rw [map_neg]
  abel

def preInv (ρ : Representation O G M) (c : O) : Submodule O M :=
  ρ.invariants.comap (c • LinearMap.id : M →ₗ[O] M)

theorem mem_preInv {ρ : Representation O G M} {c : O} (m : M) :
    m ∈ preInv ρ c ↔ ∀ g, ρ g (c • m) = c • m := Iff.rfl

theorem smul_cob_eq_zero {ρ : Representation O G M} {c : O} (m : preInv ρ c) (g : G) :
    c • (ρ g m.1 - m.1) = 0 := by
  rw [smul_sub, ← map_smul (ρ g) c, (mem_preInv _).1 m.2 g, sub_self]

def cobLev (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    preInv ρ c →ₗ[O] Z1 (levRep ρ c) where
  toFun m := ⟨fun g => Lev.mk (ρ g m.1 - m.1) (smul_cob_eq_zero m g), by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩
    · exact (IsLocallyConstant.desc _ Lev.val ((hlc m.1).sub (IsLocallyConstant.const m.1))
        lev_val_injective).continuous
    · show ρ (g * h) m.1 - m.1 = (ρ g m.1 - m.1) + ρ g (ρ h m.1 - m.1)
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel⟩
  map_add' a b := Subtype.ext (funext fun g => Lev.ext (by
    show ρ g (a.1 + b.1) - (a.1 + b.1) = (ρ g a.1 - a.1) + (ρ g b.1 - b.1)
    rw [map_add (f := _)]; abel))
  map_smul' r a := Subtype.ext (funext fun g => Lev.ext (by
    show ρ g (r • a.1) - r • a.1 = r • (ρ g a.1 - a.1)
    rw [map_smul, smul_sub]))

def kappa (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    preInv ρ c →ₗ[O] H1 (levRep ρ c) :=
  (Submodule.mkQ _) ∘ₗ cobLev ρ c hlc

theorem ker_valuation_H1 (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    LinearMap.ker (levelH1ToModuleH1 ρ c) = LinearMap.range (kappa ρ c hlc) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) : H1z ρ) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨m, hm⟩ := h1
    have hm' : ∀ g, ρ g m - m = (f.1 g).val := fun g => congrFun hm g
    have hP : m ∈ preInv ρ c := (mem_preInv m).2 fun g => by
      have := congrArg (c • ·) (hm' g)
      simp only [Lev.smul_val, smul_sub] at this
      rw [map_smul, ← sub_eq_zero, ← this]
    refine ⟨⟨m, hP⟩, ?_⟩
    show Submodule.Quotient.mk (cobLev ρ c hlc ⟨m, hP⟩) = Submodule.Quotient.mk f
    congr 1
    exact Subtype.ext (funext fun g => Lev.ext (hm' g))
  · rintro x ⟨m, rfl⟩
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c (cobLev ρ c hlc m)) : H1z ρ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m.1, rfl⟩

def toQ (ρ : Representation O G M) (c : O) :
    preInv ρ c →ₗ[O] (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) :=
  (Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict ρ.invariants
    ((c • LinearMap.id : M →ₗ[O] M) ∘ₗ (preInv ρ c).subtype) (fun m =>
      (Representation.mem_invariants _ _).2 ((mem_preInv _).1 m.2)))

theorem toQ_surjective (ρ : Representation O G M) (c : O) (hdiv : ∀ m : M, ∃ m' : M, c • m' = m) :
    Function.Surjective (toQ ρ c) := by
  intro y
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m, hm⟩ := hdiv t.1
  have hP : m ∈ preInv ρ c := (mem_preInv m).2 fun g => by
    rw [hm]; exact (Representation.mem_invariants _ _).1 t.2 g
  refine ⟨⟨m, hP⟩, ?_⟩
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext hm

theorem ker_kappa (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    LinearMap.ker (kappa ρ c hlc) = LinearMap.ker (toQ ρ c) := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have h1 : (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0 := h
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨ℓ, hℓ⟩ := (mem_coboundaries1 _ _).1 h1
    have hℓ' : ∀ g, ρ g m.1 - m.1 = ρ g ℓ.val - ℓ.val := fun g => congrArg Lev.val (hℓ g)
    have hinv : m.1 - ℓ.val ∈ ρ.invariants := (Representation.mem_invariants _ _).2 fun g => by
      rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp (hℓ' g)
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨m.1 - ℓ.val, hinv⟩, Subtype.ext ?_⟩
    show c • (m.1 - ℓ.val) = c • m.1
    rw [smul_sub, Lev.smul_val, sub_zero]
  · intro h
    have h1 : (Submodule.Quotient.mk _ : ρ.invariants ⧸ LinearMap.range
        (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) = 0 := h
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨t, ht⟩ := h1
    have ht' : c • t.1 = c • m.1 := congrArg Subtype.val ht
    have hl : c • (m.1 - t.1) = 0 := by rw [smul_sub, ht', sub_self]
    show (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_coboundaries1 _ _).2 ⟨Lev.mk (m.1 - t.1) hl, fun g => Lev.ext ?_⟩
    show ρ g m.1 - m.1 = ρ g (m.1 - t.1) - (m.1 - t.1)
    rw [map_sub, (Representation.mem_invariants _ _).1 t.2 g]
    abel

theorem card_H1_level_rep_eq : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O) (n : ℕ),
    (∀ m : M, ∃ m' : M, ϖ • m' = m) → (∀ m : M, IsLocallyConstant (fun g => ρ g m)) →
    Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) →
    Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
    Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) *
      Nat.card (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  intro O _ G _ _ M _ _ ρ ϖ n hdiv hlc hfin
  have hdivc := exists_pow_smul_eq hdiv n
  have hs := phi_surjective ρ (ϖ ^ n) hdivc hlc
  refine ⟨Finite.of_surjective _ hs, ?_⟩
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (phi ρ (ϖ ^ n))),
    Nat.card_congr ((phi ρ (ϖ ^ n)).quotKerEquivOfSurjective hs).toEquiv, mul_comm]
  congr 1
  have hker : LinearMap.ker (phi ρ (ϖ ^ n)) = LinearMap.range (kappa ρ (ϖ ^ n) hlc) := by
    rw [phi, LinearMap.ker_codRestrict, LinearMap.ker_codRestrict, ker_valuation_H1]
  rw [hker]
  exact Nat.card_congr (((kappa ρ (ϖ ^ n) hlc).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_kappa ρ (ϖ ^ n) hlc)).trans
      ((toQ ρ (ϖ ^ n)).quotKerEquivOfSurjective (toQ_surjective ρ (ϖ ^ n) hdivc)))).toEquiv)

end GlobalTheory.ShapeNeg.SeqCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH1LevelRepFormulaStatement
open ReciprocityTheory.Gal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H1_level_rep_formula : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O) (n : ℕ),
    (∀ m : M, ∃ m' : M, ϖ • m' = m) → (∀ m : M, IsLocallyConstant (fun g => ρ g m)) →
    Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) →
    Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
    Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) *
      Nat.card (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  first | exact @GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq | exact GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq | (intros; apply GlobalTheory.ShapeNeg.SeqCount.card_H1_level_rep_eq <;> assumption)
end
end
