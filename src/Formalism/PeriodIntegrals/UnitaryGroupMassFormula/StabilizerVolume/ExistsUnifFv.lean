module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasureEqOfCos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProdSt

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.EventuallySmulSub
noncomputable section

namespace PI.VolStabS

open Topology Filter Set

section Abs

variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]

def smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) : AddSubgroup W :=
  P.map (DistribSMul.toAddMonoidHom W t)

omit [TopologicalSpace K] in
theorem mem_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) (z : W) :
    z ∈ smulSub t P ↔ ∃ p ∈ P, t • p = z := by
  simp [smulSub, AddSubgroup.mem_map]

theorem coe_smulSub {W : Type} [AddCommGroup W] [Module K W] (t : K) (P : AddSubgroup W) :
    (smulSub t P : Set W) = (fun p => t • p) '' (P : Set W) := by
  ext z
  simp [smulSub, AddSubgroup.coe_map]

theorem isOpen_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (ht : t ≠ 0) (P : AddSubgroup W) (hP : IsOpen (P : Set W)) :
    IsOpen (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact (Homeomorph.smulOfNeZero t ht).isOpenMap _ hP

theorem isCompact_smulSub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (t : K) (P : AddSubgroup W) (hP : IsCompact (P : Set W)) :
    IsCompact (smulSub t P : Set W) := by
  rw [coe_smulSub]
  exact hP.image (continuous_const_smul t)

theorem eventually_smul_sub {W : Type} [AddCommGroup W] [Module K W] [TopologicalSpace W]
    [ContinuousSMul K W] (S : Set W) (hS : IsCompact S) (s : ℕ → K)
    (hs : Tendsto s atTop (𝓝 0)) (N : Set W) (hN : N ∈ 𝓝 (0 : W)) :
    ∃ k, ∀ p ∈ S, s k • p ∈ N := by
  have hP : ∀ p ∈ S, ∀ᶠ q : K × W in 𝓝 ((0 : K), p), q.1 • q.2 ∈ N := by
    intro p _
    have h : Tendsto (fun q : K × W => q.1 • q.2) (𝓝 ((0 : K), p)) (𝓝 (0 : W)) := by
      simpa using (continuous_smul : Continuous fun q : K × W => q.1 • q.2).tendsto ((0 : K), p)
    exact h hN
  have hev := hS.eventually_forall_of_forall_eventually (P := fun (t : K) (p : W) => t • p ∈ N) hP
  exact (hs.eventually hev).exists

variable [T2Space X]

theorem reach_of_approx (π : K) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLc : IsCompact (L : Set V)) (hπL : ∀ w ∈ L, π • w ∈ L)
    (D : V →+ X) (hDc : Continuous D) (hDs : ∀ (t : K) w, D (t • w) = t • D w)
    (P : AddSubgroup X) (hPc : IsCompact (P : Set X))
    (hbase : ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub π P) :
    ∀ p ∈ P, ∃ l ∈ L, D l = p := by
  have hπkL : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ, mul_smul]
      exact ih _ (hπL w hw)
  have hstep : ∀ k : ℕ, ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub (π ^ k) P := by
    intro k
    induction k with
    | zero =>
      intro p hp
      exact ⟨0, L.zero_mem, (mem_smulSub _ _ _).2 ⟨p, hp, by simp⟩⟩
    | succ k ih =>
      intro p hp
      obtain ⟨l, hl, hpl⟩ := ih p hp
      obtain ⟨p', hp', e1⟩ := (mem_smulSub _ _ _).1 hpl
      obtain ⟨l', hl', hpl'⟩ := hbase p' hp'
      obtain ⟨p'', hp'', e2⟩ := (mem_smulSub _ _ _).1 hpl'
      refine ⟨l + π ^ k • l', L.add_mem hl (hπkL k l' hl'), (mem_smulSub _ _ _).2 ⟨p'', hp'', ?_⟩⟩
      rw [map_add (f := _), hDs, pow_succ, mul_smul, e2, smul_sub, e1]
      abel
  set S : Set X := D '' (L : Set V) with hS
  have hSc : IsClosed S := (hLc.image hDc).isClosed
  have hb : ∀ N ∈ 𝓝 (0 : X), ∃ k, (smulSub (π ^ k) P : Set X) ⊆ N := by
    intro N hN
    obtain ⟨k, hk⟩ := eventually_smul_sub (P : Set X) hPc (fun k => π ^ k) hπ N hN
    refine ⟨k, ?_⟩
    rw [coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp
  intro p hp
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  have hmem : p ∈ ⋂ k, thick S (smulSub (π ^ k) P) := by
    refine mem_iInter.2 fun k => ?_
    obtain ⟨l, hl, hpl⟩ := hstep k p hp
    exact ⟨D l, ⟨l, hl, rfl⟩, hpl⟩
  have hpS : p ∈ S :=
    (Set.ext_iff.mp (iInter_thick S hSc (fun k => smulSub (π ^ k) P) hb) p).mp hmem
  exact hpS

theorem filt_abstract [ContinuousMul K] (π : K) (hπ0 : π ≠ 0) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLo : IsOpen (L : Set V)) (hLc : IsCompact (L : Set V))
    (hπL : ∀ w ∈ L, π • w ∈ L)
    (β : V → V → X) (hβc : Continuous fun q : V × V => β q.1 q.2)
    (hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w)
    (hβ2 : ∀ u w w', β u (w + w') = β u w + β u w')
    (hβs : ∀ (t : K) u w, β u (t • w) = t • β u w)
    (G : V → X) (hG : ∀ u W, G (u + W) = G u + β u W + G W)
    (hGs : ∀ (t : K) w, G (t • w) = t • t • G w)
    (x : V) (hxo : IsOpen (β x '' (L : Set V)))
    (hsmall : ∀ U ∈ 𝓝 (0 : X), ∃ N2 ∈ 𝓝 (0 : V), ∀ c : K, (∀ w ∈ L, c • w ∈ N2) →
      ∀ w ∈ L, c • G w ∈ U) :
    ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ0 : AddSubgroup V,
      (∃ c : K, c ≠ 0 ∧ Λ0 = L.map (DistribSMul.toAddMonoidHom V c)) → (Λ0 : Set V) ⊆ N →
      ∃ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (D : V →+ X),
        Λ 0 = Λ0 ∧ (∀ n, IsOpen (Λ n : Set V)) ∧ (∀ n, IsCompact (Λ n : Set V)) ∧ Antitone Λ ∧
        (∀ n, IsOpen (H n : Set X)) ∧ (∀ n, IsCompact (H n : Set X)) ∧
        (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') ∧ (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1) := by
  have hβ0 : ∀ w, β 0 w = 0 := fun w => by
    have h := hβ1 0 0 w
    rw [add_zero] at h
    simpa using h
  have hβ0' : ∀ u, β u 0 = 0 := fun u => by
    have h := hβ2 u 0 0
    rw [add_zero] at h
    simpa using h
  let Dm : V → V →+ X := fun u =>
    { toFun := β u, map_zero' := hβ0' u, map_add' := hβ2 u }
  have hDm : ∀ u w, Dm u w = β u w := fun _ _ => rfl
  have hDmc : ∀ u, Continuous (Dm u) := fun u =>
    hβc.comp (Continuous.prodMk continuous_const continuous_id)
  set P : AddSubgroup X := L.map (Dm x) with hPdef
  have hPset : (P : Set X) = β x '' (L : Set V) := by
    rw [hPdef, AddSubgroup.coe_map]
    rfl
  have hPo : IsOpen (P : Set X) := by rw [hPset]; exact hxo
  have hPc : IsCompact (P : Set X) := by rw [hPset]; exact hLc.image (hDmc x)
  have hπP : ∀ p ∈ P, π • p ∈ P := by
    intro p hp
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hp
    exact AddSubgroup.mem_map.2 ⟨π • l, hπL l hl, by rw [hDm, hDm, hβs]⟩
  have hπkP : ∀ k : ℕ, ∀ p ∈ P, π ^ k • p ∈ P := by
    intro k
    induction k with
    | zero => intro p hp; simpa using hp
    | succ k ih =>
      intro p hp
      rw [pow_succ, mul_smul]
      exact ih _ (hπP p hp)
  set πP := smulSub π P with hπPdef
  have hπPo : IsOpen (πP : Set X) := isOpen_smulSub π hπ0 P hPo
  have hN1 : ∀ᶠ u in 𝓝 (0 : V), ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X) := by
    have hP : ∀ w ∈ (L : Set V), ∀ᶠ q : V × V in 𝓝 ((0 : V), w), β q.1 q.2 ∈ (πP : Set X) := by
      intro w _
      have h := hβc.tendsto ((0 : V), w)
      have hm : β ((0 : V), w).1 ((0 : V), w).2 ∈ (πP : Set X) := by
        show β 0 w ∈ (πP : Set X)
        rw [hβ0]
        exact πP.zero_mem
      exact h (hπPo.mem_nhds hm)
    exact hLc.eventually_forall_of_forall_eventually
      (P := fun (u : V) (w : V) => β u w ∈ (πP : Set X)) hP
  obtain ⟨N2, hN2, hsm⟩ := hsmall πP (hπPo.mem_nhds πP.zero_mem)
  refine ⟨{u | ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)} ∩ N2, inter_mem hN1 hN2, ?_⟩
  rintro y hy Λ0 ⟨c, hc0, rfl⟩ hsub
  have hcL : ∀ w ∈ L, c • w ∈ {u | ∀ w ∈ (L : Set V), β u w ∈ (πP : Set X)} ∩ N2 :=
    fun w hw => hsub (AddSubgroup.mem_map.2 ⟨w, hw, rfl⟩)
  have hcG : ∀ w ∈ L, c • G w ∈ πP := hsm c (fun w hw => (hcL w hw).2)
  have hreach : ∀ p ∈ P, ∃ l ∈ L, Dm y l = p := by
    refine reach_of_approx π hπ L hLc hπL (Dm y) (hDmc y) (fun t w => hβs t y w) P hPc ?_
    intro p hp
    obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hp
    refine ⟨l, hl, ?_⟩
    have e : Dm x l - Dm y l = -(β (y - x) l) := by
      rw [hDm, hDm]
      have := hβ1 x (y - x) l
      rw [add_sub_cancel] at this
      rw [this]
      abel
    rw [e]
    exact πP.neg_mem (hy.1 l hl)
  set Q := L.map (Dm y) with hQdef
  have hPQ : P ≤ Q := fun p hp => by
    obtain ⟨l, hl, e⟩ := hreach p hp
    exact AddSubgroup.mem_map.2 ⟨l, hl, e⟩
  have hQo : IsOpen (Q : Set X) := AddSubgroup.isOpen_mono hPQ hPo
  have hQc : IsCompact (Q : Set X) := by rw [hQdef, AddSubgroup.coe_map]; exact hLc.image (hDmc y)
  set s : ℕ → K := fun n => π ^ n * c with hsdef
  have hs0 : ∀ n, s n ≠ 0 := fun n => mul_ne_zero (pow_ne_zero n hπ0) hc0
  have hsc : s 0 = c := by simp [hsdef]
  set Λ : ℕ → AddSubgroup V := fun n => smulSub (s n) L with hΛdef
  have hH : ∀ n, (Λ n).map (Dm y) = smulSub (s n) Q := by
    intro n
    ext z
    rw [AddSubgroup.mem_map, mem_smulSub]
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hv
      exact ⟨Dm y l, AddSubgroup.mem_map_of_mem _ hl, by rw [hDm, hDm, hβs]⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨l, hl, rfl⟩ := AddSubgroup.mem_map.1 hq
      exact ⟨s n • l, (mem_smulSub _ _ _).2 ⟨l, hl, rfl⟩, by rw [hDm, hDm, hβs]⟩
  refine ⟨Λ, fun n => (Λ n).map (Dm y), Dm y, ?_, fun n => isOpen_smulSub _ (hs0 n) L hLo,
    fun n => isCompact_smulSub _ L hLc, ?_, ?_, ?_, ?_, fun n => rfl, ?_⟩
  · simp only [hΛdef, smulSub, hsc]
  · refine antitone_nat_of_succ_le fun n z hz => ?_
    obtain ⟨l, hl, rfl⟩ := (mem_smulSub _ _ _).1 hz
    refine (mem_smulSub _ _ _).2 ⟨π • l, hπL l hl, ?_⟩
    rw [smul_smul]
    congr 1
    simp only [hsdef]
    ring
  · intro n
    show IsOpen (((Λ n).map (Dm y) : AddSubgroup X) : Set X)
    rw [hH]
    exact isOpen_smulSub _ (hs0 n) Q hQo
  · intro n
    show IsCompact (((Λ n).map (Dm y) : AddSubgroup X) : Set X)
    rw [hH]
    exact isCompact_smulSub _ Q hQc
  · intro N' hN'
    have hst : Tendsto s atTop (𝓝 0) := by
      have := hπ.mul_const c
      simpa [hsdef] using this
    obtain ⟨k, hk⟩ := eventually_smul_sub (Q : Set X) hQc s hst N' hN'
    refine ⟨k, ?_⟩
    show (((Λ k).map (Dm y) : AddSubgroup X) : Set X) ⊆ N'
    rw [hH, coe_smulSub]
    rintro _ ⟨q, hq, rfl⟩
    exact hk q hq
  · intro n Z hZ W hW
    obtain ⟨z, hz, rfl⟩ := (mem_smulSub _ _ _).1 hZ
    obtain ⟨w, hw, rfl⟩ := (mem_smulSub _ _ _).1 hW
    rw [hsc]
    show G (y + c • z + s n • w) - G (y + c • z) - β y (s n • w) ∈ (Λ (n + 1)).map (Dm y)
    have e1 : G (y + c • z + s n • w) - G (y + c • z) - β y (s n • w) =
        β (c • z) (s n • w) + G (s n • w) := by
      rw [hG (y + c • z) (s n • w), hβ1 y (c • z)]
      abel
    obtain ⟨p1, hp1, e2⟩ := (mem_smulSub _ _ _).1 ((hcL z hz).1 w hw)
    obtain ⟨p2, hp2, e3⟩ := (mem_smulSub _ _ _).1 (hcG w hw)
    have e4 : β (c • z) (s n • w) + G (s n • w) = s (n + 1) • (p1 + π ^ n • p2) := by
      rw [hβs, hGs, ← e2]
      have e5 : s n • s n • G w = s n • π ^ n • (c • G w) := by
        simp only [hsdef]
        module
      rw [e5, ← e3]
      simp only [hsdef]
      module
    rw [e1, e4, hH]
    exact (mem_smulSub _ _ _).2 ⟨_, hPQ (P.add_mem hp1 (hπkP n p2 hp2)), rfl⟩

end Abs

end PI.VolStabS
end
end

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

section HermMod

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

theorem sigR_algebraMap (σ : E →ₐ[F] E) (t : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) t) = algebraMap R (R ⊗[F] E) t := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem hR_smul_left (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J (t • x) y = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hR_smul_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : R)
    (x y : Fin M → R ⊗[F] E) : hR R σ J x (t • y) = t • hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

instance hermSMul (σ : E →ₐ[F] E) (n : ℕ) : SMul R (HermR R σ n) :=
  ⟨fun t S => ⟨t • (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)), by
    intro a b
    have h := S.2 a b
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, sigR_algebraMap]
    rw [h]⟩⟩

theorem coe_hermSMul (σ : E →ₐ[F] E) (n : ℕ) (t : R) (S : HermR R σ n) :
    ((t • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = t • (S : Matrix _ _ _) := rfl

instance hermModule (σ : E →ₐ[F] E) (n : ℕ) : Module R (HermR R σ n) :=
  Function.Injective.module R (HermR R σ n).subtype Subtype.coe_injective (fun _ _ => rfl)

end HermMod

theorem exists_unif_Fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : Fv F v, π ≠ 0 ∧ Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0) ∧
      π ∈ v.adicCompletionIntegers F := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    rw [v.valuedAdicCompletion_eq_valuation' π, hπ]
  have h1 : Valued.v (π : v.adicCompletion F) < 1 := by
    rw [hv]
    decide
  refine ⟨π, fun h => ?_, ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · have hlt : ‖(π : v.adicCompletion F)‖ < 1 := Valued.toNormedField.norm_lt_one_iff.2 h1
    exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact h1.le

theorem gramFilt_of (hDx : DxOpen) : GramFilt := by
  intro F E _ _ _ _ σ hσ M J hJ hdet a ha1 ha2 v d b x hx
  have : FiniteDimensional F E := Module.Finite.of_basis b
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have hNE : NumberField E :=
    { to_charZero := inferInstance
      to_finiteDimensional := Module.Finite.trans F E }
  have := locallyCompact_Fv F v
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  have : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have : ContinuousSMul (Fv F v) (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (ContinuousSMul (Fv F v) (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : ContinuousSMul (Fv F v) (HermR (Fv F v) σ a) := by
    refine ⟨continuous_induced_rng.2 ?_⟩
    show Continuous fun p : Fv F v × HermR (Fv F v) σ a =>
      p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)
  obtain ⟨π, hπ0, hπ, hπO⟩ := exists_unif_Fv v
  set L := latSub b v a M with hLdef
  have hLo : IsOpen (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    (PositiveNearLattice.isClopen_latV b v a M).isOpen
  have hLc : IsCompact (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)) :=
    PositiveNearLattice.isCompact_latV b v a M
  have hπL : ∀ w ∈ L, π • w ∈ L := by
    intro w hw i j k
    have h := hw i j k
    show (Algebra.TensorProduct.basis (Fv F v) b).repr (π • w i j) k ∈ v.adicCompletionIntegers F
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hπO h
  let β : (Fin a → Fin M → Fv F v ⊗[F] E) → (Fin a → Fin M → Fv F v ⊗[F] E) →
      HermR (Fv F v) σ a := fun u w => ⟨gramB (Fv F v) σ J u w, gramB_mem (Fv F v) σ hσ J hJ u w⟩
  have hβc : Continuous fun q : (Fin a → Fin M → Fv F v ⊗[F] E) × (Fin a → Fin M → Fv F v ⊗[F] E) =>
      β q.1 q.2 := (continuous_gramB (Fv F v) σ J).subtype_mk _
  have hβ1 : ∀ u u' w, β (u + u') w = β u w + β u' w := by
    intro u u' w
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J (u + u') w i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u' w i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hβ2 : ∀ u w w', β u (w + w') = β u w + β u w' := by
    intro u w w'
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J u (w + w') i j = gramB (Fv F v) σ J u w i j + gramB (Fv F v) σ J u w' i j
    simp only [gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hβs : ∀ (t : Fv F v) u w, β u (t • w) = t • β u w := by
    intro t u w
    apply Subtype.ext
    funext i j
    show gramB (Fv F v) σ J u (t • w) i j = t • gramB (Fv F v) σ J u w i j
    simp only [gramB, Pi.smul_apply, hR_smul_left, hR_smul_right, smul_add]
  set G := gramH (Fv F v) σ hσ J hJ (n := a) with hGdef
  have hG : ∀ u W, G (u + W) = G u + β u W + G W := by
    intro u W
    apply Subtype.ext
    funext i j
    show gramR (Fv F v) σ J (u + W) i j =
      gramR (Fv F v) σ J u i j + gramB (Fv F v) σ J u W i j + gramR (Fv F v) σ J W i j
    simp only [gramR, gramB, Pi.add_apply, hR_add_left, hR_add_right]
    ring
  have hGs : ∀ (t : Fv F v) w, G (t • w) = t • t • G w := by
    intro t w
    apply Subtype.ext
    funext i j
    show gramR (Fv F v) σ J (t • w) i j = t • t • gramR (Fv F v) σ J w i j
    simp only [gramR, Pi.smul_apply, hR_smul_left, hR_smul_right]
  have hGc : Continuous G := continuous_gramH (Fv F v) σ hσ J hJ
  have hxo : IsOpen (β x '' (L : Set (Fin a → Fin M → Fv F v ⊗[F] E))) := by
    have h := hDx F E σ hσ M J hJ hdet a ha1 ha2 v d b x hx
    have e : (fun W => gramH (Fv F v) σ hσ J hJ (x + W) - gramH (Fv F v) σ hσ J hJ x -
        gramH (Fv F v) σ hσ J hJ W) = β x := by
      funext W
      rw [← hGdef, hG]
      abel
    rwa [e] at h

  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · subst h0
      exfalso
      have : (1 : E) = 0 := by
        rw [← b.sum_repr (1 : E)]
        simp
      exact one_ne_zero this
    · exact h0
  have hM : 0 < M := by omega
  let i0 : Fin a := ⟨0, ha1⟩
  let j0 : Fin M := ⟨0, hM⟩
  let k0 : Fin d := ⟨0, hd⟩
  let φ : (Fin a → Fin M → Fv F v ⊗[F] E) → Fv F v := fun Y => PositiveNearLattice.crd b (Fv F v) (Y i0 j0) k0
  have hφc : Continuous φ :=
    (PositiveNearLattice.continuous_crd b (Fv F v) k0).comp ((continuous_apply j0).comp (continuous_apply i0))
  have hφs : ∀ (t : Fv F v) Y, φ (t • Y) = t * φ Y := by
    intro t Y
    show (Algebra.TensorProduct.basis (Fv F v) b).repr (t • Y i0 j0) k0 =
      t * (Algebra.TensorProduct.basis (Fv F v) b).repr (Y i0 j0) k0
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e0 : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    if i = i0 ∧ j = j0 then inclR (Fv F v) (b k0) else 0
  have he0L : e0 ∈ L := by
    intro i j k
    show PositiveNearLattice.crd b (Fv F v) (e0 i j) k ∈ v.adicCompletionIntegers F
    by_cases hij : i = i0 ∧ j = j0
    · simp only [e0, if_pos hij, PositiveNearLattice.crd_incl, b.repr_self, Finsupp.single_apply]
      split_ifs
      · simp
      · simp
    · simp only [e0, if_neg hij, PositiveNearLattice.crd, map_zero, Finsupp.zero_apply]
      exact zero_mem _
  have hφe : φ e0 = 1 := by
    show PositiveNearLattice.crd b (Fv F v) (e0 i0 j0) k0 = 1
    simp [e0, PositiveNearLattice.crd_incl, b.repr_self]
  have hsmall : ∀ U ∈ 𝓝 (0 : HermR (Fv F v) σ a), ∃ N2 ∈ 𝓝 (0 : Fin a → Fin M → Fv F v ⊗[F] E),
      ∀ c : Fv F v, (∀ w ∈ L, c • w ∈ N2) → ∀ w ∈ L, c • G w ∈ U := by
    intro U hU
    have hT : ∀ᶠ t in 𝓝 (0 : Fv F v), ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)),
        t • G w ∈ U := by
      have hP : ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)),
          ∀ᶠ q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) in 𝓝 ((0 : Fv F v), w), q.1 • G q.2 ∈ U := by
        intro w _
        have h : Tendsto (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2)
            (𝓝 ((0 : Fv F v), w)) (𝓝 (0 : HermR (Fv F v) σ a)) := by
          have hc : Continuous (fun q : Fv F v × (Fin a → Fin M → Fv F v ⊗[F] E) => q.1 • G q.2) :=
            continuous_fst.smul (hGc.comp continuous_snd)
          have := hc.tendsto ((0 : Fv F v), w)
          simpa using this
        exact h hU
      exact hLc.eventually_forall_of_forall_eventually
        (P := fun (t : Fv F v) (w : Fin a → Fin M → Fv F v ⊗[F] E) => t • G w ∈ U) hP
    refine ⟨φ ⁻¹' {t | ∀ w ∈ (L : Set (Fin a → Fin M → Fv F v ⊗[F] E)), t • G w ∈ U}, ?_, ?_⟩
    · have h0 : φ 0 = 0 := by
        have := hφs 0 0
        simpa using this
      exact hφc.continuousAt.preimage_mem_nhds (by rw [h0]; exact hT)
    · intro c hc w hw
      have h := hc e0 he0L
      simp only [Set.mem_preimage, Set.mem_setOf_eq, hφs, hφe, mul_one] at h
      exact h w hw
  exact filt_abstract π hπ0 hπ L hLo hLc hπL β hβc hβ1 hβ2 hβs G hG hGs x hxo hsmall

end PI.VolStabS
