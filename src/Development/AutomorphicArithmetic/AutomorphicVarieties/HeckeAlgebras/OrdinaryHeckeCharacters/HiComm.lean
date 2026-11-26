module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.OrdFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IsSubquotientOfHasSupport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtinLit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.ExtDense
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem hiC_sum {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H) (x : H) (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite) (v : M) :
    dc ρ K K x v = ∑ q ∈ hfin.toFinset, ρ q.out v := by
  rw [dc, finsum_set_coe_eq_finsum_mem (f := fun q : H ⧸ K => ρ q.out), finsum_mem_eq_finite_toFinset_sum _ hfin,
    LinearMap.sum_apply]

private theorem hiC_comm {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (K : Subgroup H) (x : H) (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite)
    (T : Module.End A M) (hT : ∀ g v, T (ρ g v) = ρ g (T v)) (v : M) : T (dc ρ K K x v) = dc ρ K K x (T v) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hiC_sum ρ K x hfin, hiC_sum ρ K x hfin, map_sum]
  exact Finset.sum_congr rfl fun q _ => hT _ _

private theorem hiC_orb {H : Type} [Group H] (K : Subgroup H) (x y : H) :
    (y : H ⧸ K) ∈ MulAction.orbit K (x : H ⧸ K) ↔ ∃ k ∈ K, (k * x)⁻¹ * y ∈ K := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, k.2, QuotientGroup.eq.mp hk⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨⟨k, hk⟩, QuotientGroup.eq.mpr h⟩

private theorem hiC_equiv {A H H' M : Type} [CommRing A] [Group H] [Group H'] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (ρ' : Representation A H' M) (K : Subgroup H) (K' : Subgroup H') (e : H' ≃* H)
    (he : ∀ g, e g ∈ K ↔ g ∈ K') (hρ : ∀ g, ρ' g = ρ (e g)) (x : H')
    (hfin' : (MulAction.orbit K' (x : H' ⧸ K')).Finite) (hfin : (MulAction.orbit K (e x : H ⧸ K)).Finite)
    (v : M) (hv : v ∈ fixd ρ K) : dc ρ' K' K' x v = dc ρ K K (e x) v := by
  classical
  have hq : ∀ a b : H', ((e a : H) : H ⧸ K) = (e b : H) ↔ (a : H' ⧸ K') = b := fun a b => by
    rw [QuotientGroup.eq, QuotientGroup.eq, ← map_inv, ← map_mul, he]
  have ho : ∀ y : H', ((e y : H) : H ⧸ K) ∈ MulAction.orbit K (e x : H ⧸ K) ↔
      (y : H' ⧸ K') ∈ MulAction.orbit K' (x : H' ⧸ K') := fun y => by
    rw [hiC_orb, hiC_orb]
    constructor
    · rintro ⟨k, hk, h⟩
      obtain ⟨k, rfl⟩ := e.surjective k
      exact ⟨k, (he k).1 hk, (he _).1 (by simpa using h)⟩
    · rintro ⟨k, hk, h⟩
      exact ⟨e k, (he k).2 hk, by simpa using (he _).2 h⟩
  rw [hiC_sum ρ' K' x hfin', (dcSum A H M ρ K K (e x) hfin).1 (hfin'.toFinset.image fun q => e q.out) ?_ ?_ v hv,
    Finset.sum_image]
  · exact Finset.sum_congr rfl fun q _ => by rw [hρ]
  · intro p _ q _ h
    exact Quotient.out_injective (e.injective h)
  · intro y hy
    obtain ⟨q, hq', rfl⟩ := Finset.mem_image.1 hy
    rw [ho, QuotientGroup.out_eq']
    exact hfin'.mem_toFinset.1 hq'
  · intro q hq'
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := e.surjective y
    refine ⟨e (y : H' ⧸ K').out, ⟨Finset.mem_image.2 ⟨_, hfin'.mem_toFinset.2 ((ho y).1 hq'), rfl⟩, ?_⟩, ?_⟩
    · rw [hq, QuotientGroup.out_eq']
    · rintro z ⟨hz, h⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
      rw [hq, QuotientGroup.out_eq'] at h
      rw [h]

private def hiC_stab {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (v : M) : Subgroup H where
  carrier := {u | ρ u v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    have ha' : ρ a v = v := ha
    have hb' : ρ b v = v := hb
    change ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' {a} ha := by
    have ha' : ρ a v = v := ha
    change ρ a⁻¹ v = v
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private theorem hiC_ord {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A]
    [IsCNL A] {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (hθ : X.I.ContChar θ) (U : Subgroup X.Ub)
    {ι : Type} (s : Finset ι) (u : ι → X.Ub) (f : X.Fn A m) (hf : f ∈ X.Ord τ θ U)
    (hfix : ∑ i ∈ s, X.ra τ (u i) f ∈ fixd (X.ra τ) U) : ∑ i ∈ s, X.ra τ (u i) f ∈ X.Ord τ θ U := by
  obtain ⟨-, h2, h3, -⟩ := spStab Γ Ga Gp X A m τ θ hθ
  have hval : ∀ (k : ℕ) (f : X.Fn A m), f ∈ X.valIn A m k ↔ ∀ g i, f g i ∈ maximalIdeal A ^ k := fun k f => by
    simp [Frame.valIn, Submodule.mem_pi]
  rw [mem_ord_iff] at hf ⊢
  refine ⟨⟨Submodule.sum_mem _ fun q _ => h2 _ f hf.1.1, hfix⟩, fun k => ?_⟩
  obtain ⟨n, hn⟩ := hf.2 k
  have key : ∀ (u : X.Ub) (j : ℕ), X.ra τ u ((X.U A m X.I.z ^ j) f) = (X.U A m X.I.z ^ j) (X.ra τ u f) := by
    intro u j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, h3 _ X.I.z_mem]
  refine ⟨n, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [← key, ← map_sub]
  rw [hval] at hn ⊢
  intro g i
  rw [Frame.ra_apply]
  simp only [Matrix.mulVec, dotProduct]
  exact Submodule.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hn _ j)

section

variable {A U M : Type} [CommRing A] [Group U] [AddCommGroup M] [Module A M] (ρ : Representation A U M)

private theorem hiC_ra {u u' : U} (h : Commute u u') (f : M) : ρ u (ρ u' f) = ρ u' (ρ u f) := by
  rw [← Module.End.mul_apply, ← map_mul, h.eq, map_mul, Module.End.mul_apply]

private theorem hiC_fix {H ι : Type} [Group H] (s : H →* U) (K : Subgroup H) (x : H)
    (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite) (V : Subgroup U) (W : ι → Subgroup U) (h1 : K.map s ≤ V)
    (h2 : ∀ u ∈ V, ∃ k ∈ K, ∃ u' ∈ V, u = s k * u' ∧ ∀ g, Commute u' (s g))
    (h3 : ∀ i, ∀ u ∈ W i, ∀ g, Commute u (s g)) (f : M) (hf : f ∈ fixd ρ (V ⊔ ⨆ i, W i)) :
    dc (ρ.comp s) K K x f ∈ fixd ρ (V ⊔ ⨆ i, W i) := by
  have hc : ∀ u ∈ V ⊔ ⨆ i, W i, (∀ g, Commute u (s g)) → ρ u (dc (ρ.comp s) K K x f) = dc (ρ.comp s) K K x f :=
    fun u hu h => by rw [hiC_comm _ _ _ hfin _ (fun g v => hiC_ra ρ (h g) v), hf u hu]
  have h4 : V ⊔ ⨆ i, W i ≤ hiC_stab ρ (dc (ρ.comp s) K K x f) := by
    refine sup_le (fun u hu => ?_) (iSup_le fun q u hu => ?_)
    · obtain ⟨k, hk, u', hu', rfl, h⟩ := h2 u hu
      refine mul_mem ?_ (hc u' (Subgroup.mem_sup_left hu') h)
      exact (dcSum A _ _ (ρ.comp s) K K x hfin).2.1 f (fun a ha => hf _ (Subgroup.mem_sup_left (h1 ⟨a, ha, rfl⟩))) k hk
    · exact hc _ (Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem q hu)) (h3 q u hu)
  exact h4

private theorem hiC_two {H H' : Type} [Group H] [Group H'] (s : H →* U) (K : Subgroup H) (x : H)
    (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite) (s' : H' →* U) (K' : Subgroup H') (x' : H')
    (hfin' : (MulAction.orbit K' (x' : H' ⧸ K')).Finite) (h : ∀ g g', Commute (s g) (s' g')) (f : M) :
    dc (ρ.comp s) K K x (dc (ρ.comp s') K' K' x' f) = dc (ρ.comp s') K' K' x' (dc (ρ.comp s) K K x f) :=
  hiC_comm _ _ _ hfin' _ (fun g v => (hiC_comm (ρ.comp s) _ _ hfin (ρ (s' g))
    (fun g' v => hiC_ra ρ (h g' g).symm v) v).symm) f

end

private theorem hiC_dcOrd {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A]
    [IsCNL A] {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (hθ : X.I.ContChar θ) (U : Subgroup X.Ub)
    {H : Type} [Group H] (s : H →* X.Ub) (K : Subgroup H) (x : H) (hfin : (MulAction.orbit K (x : H ⧸ K)).Finite)
    (f : X.Fn A m) (hf : f ∈ X.Ord τ θ U) (hfix : dc ((X.ra τ).comp s) K K x f ∈ fixd (X.ra τ) U) :
    dc ((X.ra τ).comp s) K K x f ∈ X.Ord τ θ U := by
  rw [hiC_sum _ _ _ hfin] at hfix ⊢
  exact hiC_ord X τ θ hθ U _ (fun q : H ⧸ K => s q.out) f hf hfix

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A]

private theorem hiC_P (v : H.V) (j : ℕ) : alV n H.Sl v j ∈ H.X.I.P := by
  classical
  intro v' _
  unfold alV
  by_cases h : v' = v
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact al_mem _ n j
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (glIwa ((H.Sl v').adicCompletion L) n).P.one_mem

private theorem hiC_fin (w : W.Plc L) (x : GLw n w) :
    (MulAction.orbit (KO (w.adicCompletion L) (Fin n)) (x : GLw n w ⧸ KO (w.adicCompletion L) (Fin n))).Finite :=
  (sphComm (w.adicCompletion L) n ℤ ℤ (Representation.trivial _ _ _)).1 x

private theorem hiC_KO (hA : H.Ax) (K : H.Lev) (w : W.Plc L) (hw : w ∈ H.Wp) (f : H.X.Fn A H.m)
    (hf : f ∈ fixd (H.X.ra (H.τA A)) (H.lev K)) :
    f ∈ fixd ((H.X.ra (H.τA A)).comp (H.sec w)) (KO (w.adicCompletion L) (Fin n)) := fun u hu =>
  hf _ (Subgroup.mem_sup_left (hA.W_le w hw ⟨u, hu, rfl⟩))

private theorem hiC_Tfix (hA : H.Ax) (K : H.Lev) (w : W.Plc L) (hw : w ∈ H.Wp) (j : ℕ) (f : H.X.Fn A H.m)
    (hf : f ∈ fixd (H.X.ra (H.τA A)) (H.lev K)) :
    sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j f ∈ fixd (H.X.ra (H.τA A)) (H.lev K) := by
  refine hiC_fix (H.X.ra (H.τA A)) (H.sec w) _ _ (hiC_fin w _) H.UQ _ (hA.W_le w hw) (hA.W_dec w hw) ?_ f hf
  rintro q _ ⟨g, -, rfl⟩
  exact hA.sectionsCommuteAtSplit q w hw g

private theorem hiC_TT (hA : H.Ax) (K : H.Lev) (w : W.Plc L) (hw : w ∈ H.Wp) (j : ℕ) (w' : W.Plc L) (hw' : w' ∈ H.Wp) (j' : ℕ)
    (f : H.X.Fn A H.m) (hf : f ∈ fixd (H.X.ra (H.τA A)) (H.lev K)) :
    sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j (sphOp ((H.X.ra (H.τA A)).comp (H.sec w')) j' f) =
      sphOp ((H.X.ra (H.τA A)).comp (H.sec w')) j' (sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j f) := by
  rcases hA.Wm_mul_Wm_comm w hw w' hw' with h | ⟨e, he, h⟩
  · exact hiC_two (H.X.ra (H.τA A)) (H.sec w) _ _ (hiC_fin w _) (H.sec w') _ _ (hiC_fin w' _) h f
  · have he' : ∀ v ∈ fixd (H.X.ra (H.τA A)) (H.lev K), sphOp ((H.X.ra (H.τA A)).comp (H.sec w')) j' v =
        dc ((H.X.ra (H.τA A)).comp (H.sec w)) (KO _ (Fin n)) (KO _ (Fin n)) (e (al _ n j')) v :=
      fun v hv => hiC_equiv _ _ _ _ e he (fun g => congrArg (H.X.ra (H.τA A)) (h g)) _ (hiC_fin w' _) (hiC_fin w _) v
        (hiC_KO H hA K w hw v hv)
    rw [he' f hf, he' _ (hiC_Tfix H hA K w hw j f hf)]
    exact (sphComm _ n A _ _).2.1 _ _ f (hiC_KO H hA K w hw f hf)

private theorem hiC_main [IsCNL A] (hA : H.Ax) (θ : H.X.I.T →* Aˣ) (hθ : H.X.I.ContChar θ) (K : H.Lev) :
    CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) := by
  obtain ⟨-, -, h3, h4, -⟩ := spStab _ _ _ H.X A H.m (H.τA A) θ hθ
  have hUT : ∀ (w : W.Plc L) j a, a ∈ H.X.I.P → ∀ f, H.X.U A H.m a (sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j f) =
      sphOp ((H.X.ra (H.τA A)).comp (H.sec w)) j (H.X.U A H.m a f) := fun w j a ha f =>
    hiC_comm _ _ _ (hiC_fin w _) _ (fun g v => (h3 a ha (H.sec w g) v).symm) f
  refine ⟨?_, ?_⟩
  · rintro (x | x) f hf
    · exact hiC_dcOrd H.X _ θ hθ _ (H.sec x.1.1) _ _ (hiC_fin _ _) f hf (hiC_Tfix H hA K _ x.1.2 _ f hf.1.2)
    · exact (h4 _ _ (hiC_P H _ _)).2 f hf
  · rintro (x | x) (y | y) f hf
    · exact hiC_TT H hA K _ x.1.2 _ _ y.1.2 _ f hf.1.2
    · exact (hUT _ _ _ (hiC_P H _ _) f).symm
    · exact hUT _ _ _ (hiC_P H _ _) f
    · have hN : f ∈ fixd (H.X.rp A H.m) H.X.I.N := hf.1.1.2.1
      have p1 := hiC_P H x.1 (x.2 + 1)
      have p2 := hiC_P H y.1 (y.2 + 1)
      have b1 := (uOpMul _ H.X.I A _ (H.X.rp A H.m) _ _ p1 p2 f hN).2.1
      have b2 := (uOpMul _ H.X.I A _ (H.X.rp A H.m) _ _ p2 p1 f hN).2.1
      rw [H.X.I.comm _ (H.X.I.P_le _ p1) _ (H.X.I.P_le _ p2)] at b1
      exact b1.trans b2.symm

end

theorem UpperTheory.V.Hi.hiComm :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ K, CommOn (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) ∧ Module.Finite A (H.X.Ord (H.τA A) θ (H.lev K)) ∧ Module.Free A (H.X.Ord (H.τA A) θ (H.lev K)) ∧ ∀ a, CommOn (H.MK θ a K) (H.op A) ∧ Module.Finite A (H.MK θ a K) ∧ Module.Free A (H.MK θ a K) := by
  intro L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ K
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hfi, hfr, -⟩ := ordFree _ _ _ H.X A H.m (H.τA A) θ hθ.cont (H.lev K) (hA.fin K) (hθ.free K)
  have hC := hiC_main H hA θ hθ.cont K
  refine ⟨hC, hfi, hfr, fun a => ?_⟩
  obtain ⟨b1, -, b2, -, b3⟩ := AlgebraTools.AnnihilatorQuotientFinite.locFree A _ _ (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A)
    (fun i => algebraMap c.O A (a i)) hC
  exact ⟨b1, b2, b3 inferInstance⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreEig
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem eig_cont {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedField K] (I : Ideal R) (y : R →+* K) (a : ℝ)
    (h1 : a < 1) (h0 : 0 ≤ a) (hy : ∀ N, ∀ x ∈ I ^ N, ‖y x‖ ≤ a ^ N) {f : Γ → R} (hf : Alg.AdicCont I f) :
    Continuous fun g => y (f g) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).eventually (gt_mem_nhds hε)).exists
  filter_upwards [(hf N).eventually_eq g] with g' hg'
  rw [dist_eq_norm, ← map_sub]
  exact (hy N _ (Ideal.Quotient.eq.1 hg')).trans_lt hN

private theorem eig_chi_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial B :=
    { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
  have h := D.nat (Polynomial A) (Polynomial B) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
  refine Eq.trans ?_ h
  change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]

private theorem eig_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) (b : ℕ → B)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp

private theorem eig_tele {n : ℕ} {K : Type} [Field K] (f g : Fin n → K) (hg : ∀ i, g i ≠ 0)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) (j : Fin n) : f j = g j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have e : Finset.univ.filter (fun i => i ≤ j) = insert j (Finset.univ.filter fun i => i < j) := by
      ext i; simp [le_iff_eq_or_lt]
    have h1 := h j
    rw [e, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_congr rfl fun i hi => ih i (by simpa using hi)] at h1
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => hg i) h1

private theorem eig_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {S K : Type} [Group S] [Field K] (a : S →* kˣ) (ha : Function.Surjective a) (P Q : S →* K)
    (h1 : ∀ s, a s ∈ Uo k → P s = Q s) (h2 : ∀ s, a s = unif k → P s = Q s) (s : S) : P s = Q s := by
  obtain ⟨t, ht⟩ := ha (unif k)
  have e : s = s * (t ^ ord k (a s))⁻¹ * t ^ ord k (a s) := by group
  have h3 : a (s * (t ^ ord k (a s))⁻¹) ∈ Uo k := by
    rw [map_mul, map_inv, map_zpow, ht, ← div_eq_mul_inv]
    exact GlAx.val_div_ord _
  rw [e, map_mul, map_mul Q, h1 _ h3, map_zpow, map_zpow, h2 t ht]

section Pow

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 F))

private theorem eig_ne (hh : (F →+* Qbar l) → ℤ) (x : (w.adicCompletion F)ˣ) : algPow w hh (x : w.adicCompletion F) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 x.ne_zero)

private theorem eig_mul (hh : (F →+* Qbar l) → ℤ) (x y : w.adicCompletion F) :
    algPow w hh (x * y) = algPow w hh x * algPow w hh y := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [map_mul, mul_zpow]

private theorem eig_ht {n : ℕ} (lam : Wt F l n) (i : Fin n) (x : (w.adicCompletion F)ˣ) :
    algPow w (-htW lam i) (x : w.adicCompletion F) * algPow w (lowW lam i) (x : w.adicCompletion F) *
      algPow w (fun _ => 1) (x : w.adicCompletion F) ^ (i : ℕ) = 1 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  unfold algPow
  simp only [finprod_eq_prod_of_fintype]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  have h0 : j.1 (x : w.adicCompletion F) ≠ 0 := (map_ne_zero j.1).2 x.ne_zero
  rw [zpow_one, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0]
  simp [htW]

end Pow

private theorem eig_loc (hG : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver B w)
    (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (ι : Qbar l ≃+* ℂ)
    (lam : Wt F l n) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → Weil h →* Qbar l)
    (h1 : ∀ i s, a s ∈ Uo _ → ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ) *
      algPow w (lowW lam i) (a s : w.adicCompletion F) = ι.symm (ω i (a s)))
    (h2 : ∀ (j : Fin n) s, a s = Hi.unif _ → ι (∏ i with i ≤ j, ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ)) =
      (ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1,
        algPow w (lowW lam i) ((Hi.unif (w.adicCompletion F) : (w.adicCompletion F)ˣ) : w.adicCompletion F)))⁻¹ * psEig ω (j + 1))
    (i : Fin n) (s : Weil h) : ψ i s = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F) := by
  let Q : Weil h →* Qbar l :=
    { toFun := fun s => ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
      map_one' := by simp [algPow]
      map_mul' := fun s t => by
        simp only [map_mul, Units.val_mul, eig_mul]
        ring }
  have he := Loc.epsArt hG h hl a ha
  have hq : ((normV w : ℕ) : Qbar l) ≠ 0 := by
    rw [← resCard_eq_normV]
    exact Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[w.adicCompletion F])).ne'
  refine eig_gen a ha.surj (ψ i) Q (fun s hs => ?_) (fun s hs => ?_) s
  · have hd : deg s = 0 := by
      have := ha.ord_eq s
      rw [ord_eq_zero hs] at this
      omega
    have e1 := h1 i s hs
    rw [he, hd, zpow_zero, one_mul] at e1
    have e2 := eig_ht w lam i (a s)
    change _ = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
    rw [← e1]
    linear_combination (-ψ i s) * e2
  · have hd : deg s = -1 := by
      have := ha.ord_eq s
      rw [hs, ord_eq_one GlAx.unif_spec] at this
      omega
    have e1 := eig_tele (fun i => ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ))
      (fun i => (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ * (ι.symm (ω i (a s)) * (((normV w : ℕ) : Qbar l) ^ (i : ℕ))⁻¹))
      (fun i => mul_ne_zero (inv_ne_zero (eig_ne w _ _)) (mul_ne_zero ((map_ne_zero ι.symm).2 (Units.ne_zero _))
        (inv_ne_zero (pow_ne_zero _ hq)))) (fun j => ι.injective ?_) i
    · have e2 := eig_ht w lam i (a s)
      have e3 := eig_ne w (lowW lam i) (a s)
      have e4 := pow_ne_zero (i : ℕ) hq
      rw [he, hd, mul_pow, zpow_neg_one, inv_pow] at e1
      change _ = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
      field_simp at e1
      linear_combination (-ψ i s) * e2 + algPow w (-htW lam i) (a s : w.adicCompletion F) * e1
    · have e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1) = Finset.univ.filter fun i => i ≤ j := by
        ext i; simp [Nat.lt_succ_iff]
      rw [h2 j s hs, psEig, e, hs, map_prod ι, map_prod ι, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, ι.apply_symm_apply, map_inv₀, map_inv₀, map_pow, map_natCast, ← resCard_eq_normV]
      rfl

private theorem eig_det {n : ℕ} {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] (y : R →+* Qbar l)
    (D : W.GDet n R Γ) (r : Γ →* GL (Fin n) (Qbar l)) (hr : Continuous r) (S : Set Γ) (hS : Dense S)
    (hD : ∀ i, Continuous fun g => y (D.lam i (MonoidAlgebra.single g 1)))
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map y = (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) :
    D.map y = W.GDet.ofRep (W.mat r) := by
  refine AlgebraTools.Det.extDense _ _ S hS (fun i _ => (hD i).congr fun g => ?_)
    (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hr) i) fun g hg => ?_
  · simp [W.GDet.lam, eig_chi_map]
  · rw [eig_chi_map, (AlgebraTools.Det.repApi (W.mat r)).2.1]
    exact h g hg

private theorem eig_ord (hG : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver B w)
    (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (ι : Qbar l ≃+* ℂ)
    (lam : Wt F l n) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)) {R : Type} [CommRing R]
    (y : R →+* Qbar l) (ψ : Fin n → Dec (F := F) B →* Rˣ) (hψ : ∀ i, Continuous fun g => y (ψ i g : R))
    (ε : Dec (F := F) B →* Rˣ) (he : ∀ g, y (ε g : R) = (cycBar F Ω l (g : G F Ω) : Qbar l))
    (t : Fin n → Uo (w.adicCompletion F) → R) (u : Fin n → R)
    (u1 : ∀ i (s : Weil h) (g : Dec (F := F) B) (x : Uo (w.adicCompletion F)), (g : G F Ω) = (s : G F Ω) → a s = x →
      (ψ i g * ε g ^ (i : ℕ) : Rˣ) * t i x = 1)
    (u2 : ∀ (j : Fin n) (s : Weil h) (g : Dec (F := F) B), (g : G F Ω) = (s : G F Ω) → a s = Hi.unif _ →
      ((∏ i with i ≤ j, ψ i g * ε g ^ (i : ℕ) : Rˣ) : R) = u j)
    (h1 : ∀ i (x : Uo (w.adicCompletion F)), (ω i x : ℂ) *
      ι (y (t i x) / algPow w (lowW lam i) ((x : (w.adicCompletion F)ˣ) : w.adicCompletion F)) = 1)
    (h2 : ∀ j : Fin n, ι (y (u j)) = (ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1,
        algPow w (lowW lam i) ((Hi.unif (w.adicCompletion F) : (w.adicCompletion F)ˣ) : w.adicCompletion F)))⁻¹ * psEig ω (j + 1))
    (i : Fin n) : OrdChar ι a (ω i) (htW lam i) (W.pushCh y (ψ i)) := by
  refine ⟨hω i, Units.continuous_iff.2 ⟨hψ i, ((hψ i).comp continuous_inv).congr fun g => by simp⟩, fun s g hg _ => ?_⟩
  obtain rfl : g = Subgroup.inclusion (Weil_le_Dec h) s := Subtype.ext hg
  refine eig_loc hG h hl a ha ι lam ω
    (fun i => ((Units.coeHom _).comp (W.pushCh y (ψ i))).comp (Subgroup.inclusion (Weil_le_Dec h)))
    (fun i s hs => ?_) (fun j s hs => ?_) i s
  · have e1 := congrArg y (u1 i s (Subgroup.inclusion (Weil_le_Dec h) s) ⟨_, hs⟩ rfl rfl)
    have e2 := congrArg ι.symm (h1 i ⟨_, hs⟩)
    rw [map_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, he, map_one, Subgroup.coe_inclusion] at e1
    rw [map_mul, ι.symm_apply_apply, map_one, mul_div_assoc', div_eq_one_iff_eq (eig_ne _ _ _)] at e2
    change y (ψ i (Subgroup.inclusion (Weil_le_Dec h) s) : R) * _ * _ = _
    rw [← e2]
    linear_combination (ι.symm (ω i (a s) : ℂ)) * e1
  · refine Eq.trans (congrArg ι (Eq.trans ?_ (congrArg y (u2 j s (Subgroup.inclusion (Weil_le_Dec h) s) rfl hs)))) (h2 j)
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, he]
    rfl

private theorem eig_pt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] :
    Fact (∀ y : R →ₐ[c.O] Qbar l, (∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → R), Alg.AdicCont (maximalIdeal R) f → Continuous fun g => y.toRingHom (f g)) ∧
      ∀ (v : H.V) (g : Dec (F := L) (H.pl v)), y.toRingHom (H.epsV R v g : R) = (cycBar L Ω l (g : G L Ω) : Qbar l)) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨-, b, b1, b0, hb⟩ := (GradeZeroInterpolatingElement.coPt c R).1 y
  exact ⟨fun Γ _ f hf => eig_cont _ y.toRingHom b b1 b0 hb hf,
    fun v g => (y.commutes (algebraMap ℤ_[l] c.O (cycZ L Ω l (g : G L Ω) : ℤ_[l]))).trans rfl⟩


theorem UpperTheory.V.Hi.coreEig :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    ∀ (y : H.TK θ a K →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.Part ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d), F ∈ Y.Y → F ≠ 0 → (∀ w j, H.opC ι lam d (.inl (w, j)) F = ι (y (H.gen θ a K (.inl (w, j)))) • F) → D.map y.toRingHom = W.GDet.ofRep (W.mat Y.r) ∧ ∀ v (ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (∀ i (u : Uo ((H.Sl v).adicCompletion L)), (ω i u : ℂ) * ι (H.finPart θ (y.toRingHom.comp (algebraMap A _)) lam v i u) = 1) → (∀ j : Fin n, ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) → ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh y.toRingHom (ψ v i)) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι a K _ _ D ψ hU y lam d ξ Y F hF hF0 hev
  obtain ⟨hc, he⟩ := (eig_pt H (H.TK θ a K)).out y
  refine ⟨eig_det _ D Y.r Y.cont _ hH.dense (fun i => hc _ _ (hU.cont i)) ?_,
    fun v ω hω h1 h2 i => ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [hU.frob ⟨w, hw⟩ B σ hB hσ]
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [Polynomial.map_map]
    refine (eig_pol _ n _ _ (Y.a ⟨w, hw⟩) fun j hj => ?_).trans (Y.frob ⟨w, hw⟩ B σ hB hσ).symm
    unfold HSet.genW
    split_ifs with h
    · have e := hev ⟨w, hw⟩ ⟨j - 1, h.2⟩
      have e' := Y.sph ⟨w, hw⟩ (j - 1 + 1) F hF
      have e2 := smul_left_injective ℂ hF0 (e.symm.trans e')
      rw [show j - 1 + 1 = j by omega] at e2
      exact e2
    · rw [show j = 0 by omega, Y.a_zero, map_one]
  · have h3 := eig_ord hN.aut.art (H.ovr v) (hH.Sl_over v) (H.art v) (hH.art_spec v) ι lam ω hω _ (ψ v)
      (fun i => hc _ _ (hU.ψ_cont v i)) _ (he v)
    have h4 := h3 (fun i x => algebraMap A (H.TK θ a K) (θ (eV n H.Sl v i x))) (fun j => H.gen θ a K (.inr (v, j)))
      (hU.ψ_unit v) (hU.ψ_unif v) h1 h2
    exact h4 i
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreUniq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cu_ext {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) [IsHausdorff I R] {S : Set Γ}
    (hS : Dense S) {f g : Γ → R} (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (h : ∀ x ∈ S, f x = g x) : f = g := by
  funext x
  refine IsHausdorff.eq_iff_smodEq (I := I).2 fun N => ?_
  rw [smul_eq_mul, Ideal.mul_top]
  letI : TopologicalSpace (R ⧸ I ^ N) := ⊥
  haveI : DiscreteTopology (R ⧸ I ^ N) := ⟨rfl⟩
  exact congrFun (Continuous.ext_on hS (hf N).continuous (hg N).continuous fun y hy => by simp only [h y hy]) x

private theorem cu_prod {n : ℕ} {M : Type} [CommGroup M] (f g : Fin n → M)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) : ∀ j, f j = g j := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hj : j ∈ Finset.univ.filter fun i => i ≤ j := by simp
    have e := h j
    rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ g hj,
      Finset.prod_congr rfl (g := g) fun i hi => ih i (by
        rw [Finset.mem_erase, Finset.mem_filter] at hi
        exact lt_of_le_of_ne hi.2.2 hi.1)] at e
    exact mul_right_cancel e

private theorem cu_gen {W M k : Type} [Group W] [Group M] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : W →* kˣ) (ha : Function.Surjective a) (f g : W →* M)
    (h1 : ∀ s (y : Uo k), a s = y → f s = g s) (h2 : ∀ s, a s = unif k → f s = g s) (s : W) : f s = g s := by
  obtain ⟨p, hp⟩ := ha (unif k)
  have e := h1 (s * (p ^ ord k (a s))⁻¹) ⟨_, GlAx.val_div_ord (a s)⟩ (by
    rw [map_mul, map_inv, map_zpow, hp]
    exact (div_eq_mul_inv _ _).symm)
  rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, h2 p hp] at e
  exact mul_right_cancel e

theorem UpperTheory.V.Hi.coreUniq :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    ∀ (D' : W.GDet n (H.TK θ a K) H.Gq) (ψ' : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D' ψ' → D' = D ∧ ψ' = ψ := by
  intro _ L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ _ a K _ _ D ψ hU D' ψ' hU'
  refine ⟨UpperTheory.V.CA.d_gext D' D fun g i _ _ => congrFun (cu_ext _ hA.dense (hU'.cont i) (hU.cont i) ?_) g, ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    simp only [W.GDet.lam, hU.frob ⟨w, hw⟩ B σ hB hσ, hU'.frob ⟨w, hw⟩ B σ hB hσ]
  · funext v i
    have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec (H.ovr v))) := UpperTheory.weil_group_dense_in_galois_group L Ω _ _ (H.ovr v)
    refine MonoidHom.ext fun g => Units.ext (congrFun (cu_ext _ hd (hU'.ψ_cont v i) (hU.ψ_cont v i) ?_) g)
    rintro _ ⟨s, rfl⟩
    refine congrArg Units.val (cu_gen (H.art v) (hA.art_spec v).surj ((ψ' v i).comp _) ((ψ v i).comp _)
      (fun s y hy => ?_) (fun s hs => ?_) s)
    · have e := (hU'.ψ_unit v i s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) y rfl hy)
      have e' := (hU.ψ_unit v i s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) y rfl hy)
      exact mul_right_cancel (inv_injective (Units.ext
        ((Units.eq_inv_of_mul_eq_one_left e).symm.trans (Units.eq_inv_of_mul_eq_one_left e'))))
    · exact mul_right_cancel (cu_prod _ _ (fun j => Units.ext
        ((hU'.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs).trans
          (hU.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs).symm)) i)
end
