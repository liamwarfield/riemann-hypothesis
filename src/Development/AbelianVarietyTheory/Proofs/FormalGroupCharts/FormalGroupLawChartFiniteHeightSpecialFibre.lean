module

public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFormalGroupLawOfChartOfJetChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FiniteTorsionSpecialFibreOfUnif
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_torsion_of_pullback {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) (t : Z ⟶ S')
    (r : Z ⟶ S) (hr : t ≫ f = r) (N : ℕ)
    (h : Finite {x : Over.mk t ⟶ (Over.pullback f).obj G // x ^ N = 1}) :
    Finite {x : Over.mk r ⟶ G // x ^ N = 1} := by
  subst hr
  let e := ObjPull.pushEquiv (isGrpPullback_pullback G f) (Over.mk t)
  refine Finite.of_injective (β := {x : Over.mk t ⟶ (Over.pullback f).obj G // x ^ N = 1})
    (fun x => ⟨e.symm x.1, ?_⟩) ?_
  · have hx : (show Over.mk ((Over.mk t).hom ≫ f) ⟶ G from x.1) ^ N = 1 := x.2
    rw [← map_pow, hx, map_one]
  · intro x y hxy
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val hxy))

theorem finite_torsion_special_fibre_of_unif : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (β : T →+* Ω), (∀ a ∈ maximalIdeal T, β a = 0) → ∀ N : ℕ, 1 ≤ N → Finite {x : Over.mk (spMap β) ⟶ G // x ^ N = 1} := by
  intro T _ _ _ G _ _ D A U Ω _ _ β hβ N hN
  let β' : T ⧸ (maximalIdeal T) ^ (0 + 1) →+* Ω :=
    Ideal.Quotient.lift _ β (fun a ha => hβ a (by simpa using ha))
  have g := U.gt 0
  have : IsCommMonObj (Out.thickObj T (maximalIdeal T) 0 G) := Functor.isCommMonObj_obj
  have h := GlobalTheory.TorusExtTorsion.finite_torsion_geomPoint _ (Out.thickObj T (maximalIdeal T) 0 G) (Out.thickObj T (maximalIdeal T) 0 D.toPre.P.A)
    D.toPre.X g.q g.i g.q_hom g.i_hom g.isKernel (Out.TLinPf.isAb_pullback _ _ D.toPre.P.isAb) Ω
    (Geo.Tor.spMap β') N hN
  refine finite_torsion_of_pullback G (Out.thick T (maximalIdeal T) 0) (Geo.Tor.spMap β') _ ?_ N h
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.LocallyOfFiniteTypePullbackUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniversalThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniversalThickening
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.IsolPt

theorem isArtinianRing_of_finite_points (k B : Type) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [Finite (B →ₐ[k] AlgebraicClosure k)] : IsArtinianRing B := by
  have hN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hJ : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have hsur : ∀ m : Ideal B, m.IsMaximal → ∃ f : B →ₐ[k] AlgebraicClosure k, RingHom.ker f = m := by
    intro m hm
    letI := Ideal.Quotient.field m
    have : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
    let g : (B ⧸ m) →ₐ[k] AlgebraicClosure k := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨g.comp (Ideal.Quotient.mkₐ k m), ?_⟩
    ext b
    simp only [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [map_eq_zero_iff g g.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]
  have hfin : {m : Ideal B | m.IsMaximal}.Finite :=
    (Set.finite_range fun f : B →ₐ[k] AlgebraicClosure k => RingHom.ker f).subset hsur
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h1 : p.jacobson = p := IsJacobsonRing.out hJ hp.isRadical
  have hf : {J : Ideal B | p ≤ J ∧ J.IsMaximal}.Finite := hfin.subset fun _ h => h.2
  have h2 : hf.toFinset.inf id ≤ p := by
    rw [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset]
    exact h1.le
  obtain ⟨m, hm, hle⟩ := hp.inf_le'.1 h2
  rw [Set.Finite.mem_toFinset] at hm
  have : m = p := le_antisymm hle hm.1
  exact this ▸ hm.2

theorem exists_pow_stable {B : Type} [CommRing B] [IsArtinianRing B] (I : Ideal B) :
    ∃ M : ℕ, ∀ j : ℕ, I ^ (M + 1) ≤ I ^ (j + 1) := by
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := B) (M := B)
    ⟨fun n => OrderDual.toDual (I ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  refine ⟨n, fun j => ?_⟩
  have h1 : I ^ n = I ^ (n + (j + 1)) := hn (n + (j + 1)) (by omega)
  calc I ^ (n + 1) ≤ I ^ n := Ideal.pow_le_pow_right (by omega)
    _ = I ^ (n + (j + 1)) := h1
    _ ≤ I ^ (j + 1) := Ideal.pow_le_pow_right (by omega)

theorem exists_thickening {k B : Type} [Field k] [CommRing B] [Algebra k B] [IsArtinianRing B]
    (e : B →ₐ[k] k) : ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ)
      (π : B →ₐ[k] A), RingHom.ker aug ^ (M + 1) = ⊥ ∧ aug.comp π = e ∧
      ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ),
        RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : B →ₐ[k] Q, augQ.comp z = e →
        ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = a.comp π := by
  obtain ⟨M, hM⟩ := exists_pow_stable (RingHom.ker e)
  set I : Ideal B := RingHom.ker e ^ (M + 1) with hI
  have hIe : ∀ b ∈ I, e b = 0 := fun b hb => Ideal.pow_le_self (Nat.succ_ne_zero M) hb
  refine ⟨B ⧸ I, inferInstance, inferInstance, Ideal.Quotient.liftₐ I e hIe, M, Ideal.Quotient.mkₐ k I,
    ?_, ?_, ?_⟩
  · have h : RingHom.ker (Ideal.Quotient.liftₐ I e hIe) ≤ (RingHom.ker e).map (Ideal.Quotient.mk I) := by
      intro x hx
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_map_of_mem _ hx
    refine le_bot_iff.1 ((Ideal.pow_right_mono h _).trans ?_)
    rw [← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  · ext b
    rfl
  · intro Q _ _ augQ j hj z hz
    have hzI : ∀ b ∈ I, z b = 0 := by
      intro b hb
      have h : (RingHom.ker e).map z ≤ RingHom.ker augQ := by
        rw [Ideal.map_le_iff_le_comap]
        intro c hc
        change augQ (z c) = 0
        rw [← AlgHom.comp_apply, hz]
        exact hc
      have h2 := Ideal.mem_map_of_mem z (hM j hb)
      rw [Ideal.map_pow] at h2
      have h3 := Ideal.pow_right_mono h _ h2
      rwa [hj] at h3
    refine ⟨Ideal.Quotient.liftₐ I z hzI, ?_, ?_⟩
    · apply Ideal.Quotient.algHom_ext
      ext b
      exact DFunLike.congr_fun hz b
    · ext b
      rfl

theorem exists_factor {k A B : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    {X : Over (Spec (CommRingCat.of k))} (x : Chart.sp (R₀ := k) A ⟶ X) (v : Chart.sp (R₀ := k) B ⟶ X)
    [IsOpenImmersion v.left] (hsub : Set.range x.left ⊆ Set.range v.left) :
    ∃ ψ : B →ₐ[k] A, x = Chart.spMap ψ ≫ v := by
  have hl := IsOpenImmersion.lift_fac v.left _ hsub
  obtain ⟨ψ, hψ⟩ := NatFun.spMap_surjective (k := k) (A := B) (B := A)
    (Over.homMk (IsOpenImmersion.lift v.left _ hsub) (by
      rw [← Over.w v, ← Category.assoc, hl, Over.w]))
  refine ⟨ψ, Over.OverMorphism.ext ?_⟩
  rw [hψ]
  exact hl.symm

theorem surjective_spMap_aug {k Q : Type} [Field k] [CommRing Q] [Algebra k Q] (q : Q →ₐ[k] k) (j : ℕ)
    (hj : RingHom.ker q ^ (j + 1) = ⊥) : Function.Surjective (Chart.spMap q).left := by
  intro p
  have hq : Function.Surjective q.toRingHom := fun c => ⟨algebraMap k Q c, q.commutes c⟩
  let p' : PrimeSpectrum Q := p
  haveI := p'.isPrime
  have hker : RingHom.ker q.toRingHom ≤ p'.asIdeal :=
    p'.isPrime.le_of_pow_le (n := j + 1) (le_of_eq_of_le hj bot_le)
  have hprime : (p'.asIdeal.map q.toRingHom).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  refine ⟨(⟨p'.asIdeal.map q.toRingHom, hprime⟩ : PrimeSpectrum k), ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap q.toRingHom (Ideal.map q.toRingHom p'.asIdeal) = p'.asIdeal
  rw [Ideal.comap_map_of_surjective' q.toRingHom hq, sup_eq_left.mpr hker]


open NatFun in
theorem exists_universal_thickening : ∀ (k : Type) [Field k] (K : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType K.hom], (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite (Over.mk t ⟶ K)) → ∀ e : Chart.sp (R₀ := k) k ⟶ K, ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ) (io : Chart.sp (R₀ := k) A ⟶ K), RingHom.ker aug ^ (M + 1) = ⊥ ∧ Chart.spMap aug ≫ io = e ∧ ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ), RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : Chart.sp (R₀ := k) Q ⟶ K, Chart.spMap augQ ≫ z = e → ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = Chart.spMap a ≫ io := by
  intro k _ K _ hfin e
  let o : (Chart.sp (R₀ := k) k).left := (⊥ : PrimeSpectrum k)
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := K.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e.left o)) isOpen_univ
  change IsAffineOpen U at hU
  let v : Chart.sp (R₀ := k) Γ(K.left, U) ⟶ K := affinePoint hU
  haveI : IsOpenImmersion v.left := hU.isOpenImmersion_fromSpec
  haveI : Mono v := Over.mono_of_mono_left v
  have hinj : ∀ (Q : Type) [CommRing Q] [Algebra k Q],
      Function.Injective fun f : Γ(K.left, U) →ₐ[k] Q => Chart.spMap f ≫ v := by
    intro Q _ _ f g h
    exact spMap_injective ((cancel_mono v).1 h)
  have hft : Algebra.FiniteType k Γ(K.left, U) := by
    have h : LocallyOfFiniteType (v.left ≫ K.hom) := inferInstance
    rw [Over.w v] at h
    have h2 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 h
    exact RingHom.finiteType_algebraMap.1 h2
  haveI : Finite (Chart.sp (R₀ := k) (AlgebraicClosure k) ⟶ K) := hfin _ _
  haveI : Finite (Γ(K.left, U) →ₐ[k] AlgebraicClosure k) := Finite.of_injective _ (hinj _)
  haveI := isArtinianRing_of_finite_points k Γ(K.left, U)
  have he : Set.range e.left ⊆ Set.range v.left := by
    rintro _ ⟨y, rfl⟩
    have : y = o := Subsingleton.elim (α := PrimeSpectrum k) _ _
    rw [this]
    exact hU.range_fromSpec.superset hxU
  obtain ⟨e₀, he₀⟩ := exists_factor e v he
  obtain ⟨A, _, _, aug, M, π, h1, h2, h3⟩ := exists_thickening e₀
  refine ⟨A, _, _, aug, M, Chart.spMap π ≫ v, h1, ?_, ?_⟩
  · rw [← Category.assoc, Chart.spMap_comp, h2, he₀]
  · intro Q _ _ augQ j hj z hz
    have hzr : Set.range z.left ⊆ Set.range v.left := by
      rintro _ ⟨y, rfl⟩
      obtain ⟨y', rfl⟩ := surjective_spMap_aug augQ j hj y
      apply he
      exact ⟨y', by rw [← hz]; rfl⟩
    obtain ⟨z₀, rfl⟩ := exists_factor z v hzr
    rw [← Category.assoc, Chart.spMap_comp, he₀] at hz
    obtain ⟨a, ha, rfl⟩ := h3 Q augQ j hj z₀ (hinj _ hz)
    exact ⟨a, ha, by rw [← Category.assoc, Chart.spMap_comp]⟩

end GlobalTheory.IsolPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsUniversalThickeningStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_thickening_of_finite_points : ∀ (k : Type) [Field k] (K : Over (Spec (CommRingCat.of k))) [LocallyOfFiniteType K.hom], (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite (Over.mk t ⟶ K)) → ∀ e : Chart.sp (R₀ := k) k ⟶ K, ∃ (A : Type) (_ : CommRing A) (_ : Algebra k A) (aug : A →ₐ[k] k) (M : ℕ) (io : Chart.sp (R₀ := k) A ⟶ K), RingHom.ker aug ^ (M + 1) = ⊥ ∧ Chart.spMap aug ≫ io = e ∧ ∀ (Q : Type) [CommRing Q] [Algebra k Q] (augQ : Q →ₐ[k] k) (j : ℕ), RingHom.ker augQ ^ (j + 1) = ⊥ → ∀ z : Chart.sp (R₀ := k) Q ⟶ K, Chart.spMap augQ ≫ z = e → ∃ a : A →ₐ[k] Q, augQ.comp a = aug ∧ z = Chart.spMap a ≫ io := by
  first | exact @GlobalTheory.IsolPt.exists_universal_thickening | exact GlobalTheory.IsolPt.exists_universal_thickening | (intros; apply GlobalTheory.IsolPt.exists_universal_thickening <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

theorem mem_sup_pow_of_toJet_mem_map {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ)
    (I : Ideal (MvPowerSeries κ R)) (g : MvPowerSeries κ R) (hg : toJet m g ∈ I.map (toJetHom R κ m)) :
    g ∈ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by
  have hs : Function.Surjective (toJetHom R κ m) := fun q => by
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨P, toJet_coe m P⟩
  obtain ⟨h, hh, e⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 hg
  have h2 : g - h ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ R)) ^ (m + 1) := by
    rw [← germIdeal_eq_span, mem_germIdeal_pow_iff]
    intro d hd
    rw [map_sub, (toJet_eq_iff m h g).1 e d hd, sub_self]
  have : g = h + (g - h) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left hh) (Ideal.mem_sup_right h2)

theorem locallyOfFiniteType_pullback_unit {S : Scheme.{0}} (G : Over S) [GrpObj G] [LocallyOfFiniteType G.hom]
    (f : G ⟶ G) : LocallyOfFiniteType (pullback f η[G]).hom := by
  have h1 : LocallyOfFiniteType (f.left ≫ G.hom) := by rw [Over.w f]; infer_instance
  have h2 : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left G.hom
  have h3 := (IsPullback.of_hasPullback f η[G]).map (Over.forget S)
  have h4 : LocallyOfFiniteType (pullback.snd f η[G]).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h3 h2
  have h5 : (pullback f η[G]).hom = (pullback.snd f η[G]).left := by
    rw [← Over.w (pullback.snd f η[G])]
    exact Category.comp_id _
  rw [h5]
  exact h4

theorem exists_pow_le_span_sup_pow_succ : ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] [LocallyOfFiniteType G.hom] (f : G ⟶ G), η[G] ≫ f = η[G] → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)), Finite {x : Over.mk t ⟶ G // x ≫ f = 1}) → ∀ (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ φ : Pt k 1 d, GlobalTheory.JetSer.IsMapOf x x f φ → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ M ≤ Ideal.span (Set.range φ) ⊔ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ^ (M + 1) := by
  intro k _ G _ _ f hf hfin d x hx φ hφ
  haveI := locallyOfFiniteType_pullback_unit G f
  have hext : ∀ {T : Over (Spec (CommRingCat.of k))} (u v : T ⟶ pullback f η[G]),
      u ≫ pullback.fst f η[G] = v ≫ pullback.fst f η[G] → u = v := fun u v h =>
    pullback.hom_ext h (toUnit_unique _ _)
  have hfinK : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Spec (CommRingCat.of k)),
      Finite (Over.mk t ⟶ pullback f η[G]) := by
    intro Ω _ _ t
    haveI := hfin Ω t
    refine Finite.of_injective (β := {x : Over.mk t ⟶ G // x ≫ f = 1})
      (fun u => ⟨u ≫ pullback.fst f η[G], ?_⟩) (fun u v h => hext u v (congrArg Subtype.val h))
    rw [Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  have h1f : (1 : Chart.sp (R₀ := k) k ⟶ G) ≫ f = toUnit _ ≫ η[G] := by
    rw [Hom.one_def, Category.assoc, hf]
  obtain ⟨A, _, _, aug, M, io, hM, hio, hU⟩ :=
    GlobalTheory.T.exists_universal_thickening_of_finite_points k (pullback f η[G]) hfinK (pullback.lift 1 (toUnit _) h1f)
  refine ⟨M + 1, ?_⟩
  obtain ⟨hex, -, hfp, -, -⟩ := repSt_of_jetAlgSt jetAlg k G d x hx (Fin 1 × Fin d)
  obtain ⟨y, hy, -⟩ := hex (pt k (n := 1) d 0) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gp_pt 0)
  have hy' := hφ.2 1 _ y hy
  rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.gt_comp1_pt_right] at hy'
  obtain ⟨ψ₀, hψ₀, hy₀⟩ := hy.2 (M + 1)
  obtain ⟨ψ₁, hψ₁, hy₁⟩ := hy'.2 (M + 1)
  have hya := (hfp _ y hy).2 (M + 1)
  have hxa := (isFPt_of_isUnivChart hx).2 (M + 1)
  set I : Ideal (Chart.JetR k (Fin 1 × Fin d) (M + 1)) :=
    (Ideal.span (Set.range φ)).map (toJetHom k (Fin 1 × Fin d) (M + 1)) with hI
  have hIle : I ≤ RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) := by
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact (jetAug_toJet (M + 1) (φ j)).trans (hφ.1 j)
  let π := Ideal.Quotient.mkₐ k I
  let augQ : (Chart.JetR k (Fin 1 × Fin d) (M + 1) ⧸ I) →ₐ[k] k :=
    Ideal.Quotient.liftₐ I (Chart.jetAug k (Fin 1 × Fin d) (M + 1)) (fun a ha => hIle ha)
  have haπ : augQ.comp π = Chart.jetAug k (Fin 1 × Fin d) (M + 1) := AlgHom.ext fun _ => rfl
  have hkQ : RingHom.ker augQ ^ (M + 1 + 1) = ⊥ := by
    have hle : RingHom.ker augQ ≤ (RingHom.ker (Chart.jetAug k (Fin 1 × Fin d) (M + 1))).map π := by
      intro q hq
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact Ideal.mem_map_of_mem π hq
    rw [← le_bot_iff]
    refine (Ideal.pow_right_mono hle _).trans ?_
    rw [← Ideal.map_pow, Chart.ker_jetAug_pow, Ideal.map_bot]
  have hz : (Chart.spMap π ≫ y (M + 1)) ≫ f = toUnit _ ≫ η[G] := by
    have e : π.comp ψ₁ = (Algebra.ofId k _).comp (Chart.jetAug k (Fin d) (M + 1)) := by
      refine Chart.jet_ext fun j => ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, Chart.jetAug_zR, map_zero, hψ₁]
      exact Ideal.Quotient.eq_zero_iff_mem.2
        (Ideal.mem_map_of_mem (toJetHom k (Fin 1 × Fin d) (M + 1)) (Ideal.subset_span ⟨j, rfl⟩))
    have hy₁' : y (M + 1) ≫ f = Chart.spMap ψ₁ ≫ x (M + 1) := hy₁
    rw [Category.assoc, hy₁', ← Category.assoc, Chart.spMap_comp, e, ← Chart.spMap_comp, Category.assoc, hxa,
      ← Hom.one_def]
    exact MonObj.comp_one _
  have hzone : Chart.spMap augQ ≫ Chart.spMap π ≫ y (M + 1) = 1 := by
    rw [← Category.assoc, Chart.spMap_comp, haπ, hya]
  obtain ⟨a, ha, hza⟩ := hU _ augQ (M + 1) hkQ (pullback.lift _ (toUnit _) hz) (hext _ _ (by
    rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hzone]))
  have hM' : RingHom.ker aug ^ (M + 1 + 1) = ⊥ := by
    rw [pow_succ (RingHom.ker aug) (M + 1), hM, Ideal.bot_mul]
  obtain ⟨ψ, ⟨hψa, hψ⟩, -⟩ := hx.2.2 A aug (M + 1) hM' (io ≫ pullback.fst f η[G]) (by
    rw [← Category.assoc, hio, pullback.lift_fst])
  have hz0 : ∀ j, ψ₀ (Chart.zR (M + 1) j) = Chart.zR (M + 1) (0, j) := fun j =>
    (hψ₀ j).trans (toJet_X (M + 1) _)
  have heq : a.comp ψ = π.comp ψ₀ := by
    refine (hx.2.2 _ augQ (M + 1) hkQ (Chart.spMap π ≫ y (M + 1)) hzone).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, ha, hψa]
    · rw [← Chart.spMap_comp, Category.assoc, ← hψ, ← Category.assoc, ← hza, pullback.lift_fst]
    · rw [← AlgHom.comp_assoc, haπ]
      refine Chart.jet_ext fun j => ?_
      rw [AlgHom.comp_apply, hz0, Chart.jetAug_zR, Chart.jetAug_zR]
    · rw [hy₀, ← Category.assoc, Chart.spMap_comp]
  let Θ := π.comp (toJetHom k (Fin 1 × Fin d) (M + 1))
  have hΘ : Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS k 1 d)) ≤
      ((RingHom.ker aug).map a).comap Θ := by
    rw [Ideal.span_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have e1 : Θ (MvPowerSeries.X (0, j)) = a (ψ (Chart.zR (M + 1) j)) := by
      have := AlgHom.congr_fun heq (Chart.zR (M + 1) j)
      rw [AlgHom.comp_apply, AlgHom.comp_apply, hψ₀] at this
      exact this.symm
    show Θ (MvPowerSeries.X (0, j)) ∈ (RingHom.ker aug).map a
    rw [e1]
    exact Ideal.mem_map_of_mem a ((AlgHom.congr_fun hψa _).trans (Chart.jetAug_zR (M + 1) j))
  intro g hg
  have h2 := Ideal.le_comap_pow _ (M + 1) (Ideal.pow_right_mono hΘ (M + 1) hg)
  rw [← Ideal.map_pow, hM, Ideal.map_bot] at h2
  exact mem_sup_pow_of_toJet_mem_map (M + 1) _ g (Ideal.Quotient.eq_zero_iff_mem.1 h2)

end GlobalTheory.JetSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsSeriesOfMorphismInChartsPowMulFormalGroupLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsSeriesOfMorphismInChartsPowMulFormalGroupLaw
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetSer

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem isMapOf_pow_mulF : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ F : Fin d → PS R 2 d, GlobalTheory.JetSer.IsLawOf x F → ∀ N : ℕ, GlobalTheory.JetSer.IsMapOf x x ((𝟙 G) ^ N : G ⟶ G) (mulF F N) := by
  intro R _ G _ d x hx F hF N
  induction N with
  | zero =>
    refine ⟨gp_zero₂, fun n a y h => ?_⟩
    have h0 := (repSt_of_jetAlgSt jetAlg R G d x hx (Fin n × Fin d)).2.2.2.1
    have e : comp1 (mulF F 0) a = 0 := evP_zero ![a] (single_point_zero_constant h.1)
    rw [e, pow_zero]
    simpa only [MonObj.comp_one] using h0
  | succ N ih =>
    refine ⟨gp_addOf F hF.1 _ _ ih.1 (gp_pt 0), fun n a y h => ?_⟩
    have e : comp1 (mulF F (N + 1)) a = addOf F (comp1 (mulF F N) a) a := by
      have e1 := evP_addOf ![a] (single_point_zero_constant h.1) F (mulF F N) (pt R d 0) ih.1 (gp_pt 0)
      rw [evP_pt _ (single_point_zero_constant h.1)] at e1
      exact e1
    rw [e, pow_succ]
    simpa only [MonObj.comp_mul, Category.comp_id] using hF.2 n _ _ _ _ (ih.2 n a y h) h

end GlobalTheory.JetSer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsSeriesOfMorphismInChartsPowMulFormalGroupLawStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : GlobalTheory.JetSer.Fam G (Fin d)), Chart.IsUnivChart G d x → ∀ F : Fin d → PS R 2 d, GlobalTheory.JetSer.IsLawOf x F → ∀ N : ℕ, GlobalTheory.JetSer.IsMapOf x x ((𝟙 G) ^ N : G ⟶ G) (mulF F N) := by
  first | exact @GlobalTheory.JetSer.isMapOf_pow_mulF | exact GlobalTheory.JetSer.isMapOf_pow_mulF | (intros; apply GlobalTheory.JetSer.isMapOf_pow_mulF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PowSpanXLeAndFiniteQuotientOfLeSupPowSucc
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ : ∀ (k : Type) [Field k] (σ : Type) [Finite σ] (I : Ideal (MvPowerSeries σ k)) (M : ℕ), Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ⊔ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ (M + 1) → Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ M ≤ I ∧ Module.Finite k (MvPowerSeries σ k ⧸ I) := by
  intro k _ σ _ I M h
  set m : Ideal (MvPowerSeries σ k) := Ideal.span (Set.range MvPowerSeries.X) with hm
  have hfg : m.FG := Submodule.fg_span (Set.finite_range _)
  have hjac : m ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, hm, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hle : m ^ M ≤ I := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (N' := m ^ M) (N := I) (I := m)
      (Ideal.FG.pow hfg) hjac ?_
    rw [pow_succ'] at h
    exact h
  exact ⟨hle, FormalIsogeny.finite_quotient_of_pow_le (N := M) hle⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLawChartFiniteHeightSpecialFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteHeight

theorem id_pow_left_proj {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (N : ℕ) :
    (𝟙 G' ^ N).left ≫ φ = φ ≫ (𝟙 G ^ N).left := by
  have h1 : (ObjPull.pushEquiv h G' (𝟙 G')).left = φ := Category.id_comp _
  have h2 : ObjPull.pushEquiv h G' (𝟙 G' ^ N) = ObjPull.pushEquiv h G' (𝟙 G') ≫ 𝟙 G ^ N := by
    rw [map_pow, MonObj.comp_pow, Category.comp_id]
  rw [← ObjPull.pushEquiv_left h, h2, Over.comp_left, h1]

theorem finite_torsion_pull {S S' Z : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (t : Z ⟶ S') (r : Z ⟶ S) (hr : t ≫ f = r) (N : ℕ)
    (hf : Finite {x : Over.mk r ⟶ G // x ^ N = 1}) :
    Finite {x : Over.mk t ⟶ G' // x ≫ (𝟙 G' ^ N) = 1} := by
  subst hr
  let e := ObjPull.pushEquiv h (Over.mk t)
  refine Finite.of_injective (β := {x : Over.mk (t ≫ f) ⟶ G // x ^ N = 1})
    (fun x => ⟨e x.1, ?_⟩) ?_
  · have hx : x.1 ^ N = 1 := by
      have := x.2
      rwa [MonObj.comp_pow, Category.comp_id] at this
    have : (e x.1) ^ N = 1 := by rw [← map_pow, hx, map_one]
    exact this
  · intro x y hxy
    exact Subtype.ext (e.injective (congrArg Subtype.val hxy))

theorem exists_pow_span_X_le_span_map_residue_mulF : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ N : ℕ, 1 ≤ N → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS (ResidueField T) 1 d)) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (mulF F.F N j)) := by
  intro T _ _ _ G _ _ D A U d F x hx N hN
  obtain ⟨x0, hu, hρ⟩ := GlobalTheory.T.isUniversalChart_of_formalGroupChart T G U.smooth d F x hx
  have hlaw := GlobalTheory.T.isFormalGroupLawOfChart_of_jetChart T G d F x hx x0 hu hρ
  have hmap := GlobalTheory.T.isSeriesOfMorphismInCharts_pow_mulFormalGroupLaw T G d x0 hu F.F hlaw N
  have hp := isGrpPullback_pullback G (Spec.map (CommRingCat.ofHom (residue T)))
  obtain ⟨x', hu', -, hm, -⟩ := GlobalTheory.ChartBaseChange.chartBaseChange GlobalTheory.JetSer.jetAlg
    (GlobalTheory.JetSer.serSt_of_jetAlgSt GlobalTheory.JetSer.jetAlg) T (ResidueField T) (residue T) G _ _ hp d x0 hu
  have hm' := hm _ _ _ (id_pow_left_proj hp N) hmap
  have hsm := U.smooth
  have : LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom (residue T)))).obj G).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp.1 inferInstance
  obtain ⟨M, hM⟩ := GlobalTheory.JetSer.exists_pow_le_span_sup_pow_succ (ResidueField T) _ _ (by
      rw [MonObj.comp_pow, Category.comp_id]
      have : η[(Over.pullback (Spec.map (CommRingCat.ofHom (residue T)))).obj G] = 1 := by
        rw [Hom.one_def, toUnit_unit, Category.id_comp]
      rw [this, one_pow]) (fun Ω _ _ t => by
      obtain ⟨b, rfl⟩ := Spec.map_surjective t
      refine finite_torsion_pull hp _ (Geo.Tor.spMap (b.hom.comp (residue T))) ?_ N
        (GlobalTheory.finite_torsion_special_fibre_of_unif T G D A U Ω _ (fun a ha => ?_) N hN)
      · rw [← Spec.map_comp]
        rfl
      · rw [RingHom.comp_apply, (residue_eq_zero_iff a).2 ha, map_zero]) d x' hu' _ hm'
  exact ⟨M, (GlobalTheory.pow_span_X_le_and_finite_quotient_of_le_sup_pow_succ _ _ _ M hM).1⟩

end GlobalTheory.FiniteHeight
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalGroupLawChartFiniteHeightSpecialFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupLaw_chart_finiteHeight_specialFibre : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (d : ℕ) (F : FGLaw T d) (x : ∀ m : ℕ, algOver T (JetR T (Fin 1 × Fin d) m) ⟶ G), IsChartJ G F x → ∀ N : ℕ, 1 ≤ N → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS (ResidueField T) 1 d)) ^ M ≤ Ideal.span (Set.range fun j => MvPowerSeries.map (residue T) (mulF F.F N j)) := by
  first | exact @GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF | exact GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF | (intros; apply GlobalTheory.FiniteHeight.exists_pow_span_X_le_span_map_residue_mulF <;> assumption)
end
