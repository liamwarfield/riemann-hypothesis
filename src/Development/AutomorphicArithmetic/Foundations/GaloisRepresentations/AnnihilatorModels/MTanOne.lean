module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTanOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma ofFn_prod_one {X : Type*} [Monoid X] {n : ℕ} (h : n = 1) (f : Fin n → X) :
    (List.ofFn f).prod = f ⟨0, by omega⟩ := by
  subst h; simp

private lemma alg_core {F κ V : Type} [CommRing F] [Field κ] [AddCommGroup V] [Module κ V] (p : ℕ) [CharP κ p]
    (T : F →+* Module.End κ V) (u : Ideal F) (α α' : F)
    (h1 : ∀ a ∈ u, a * α ∈ Ideal.span {(p : F)})
    (h2 : α + α' - 1 ∈ Ideal.span {(p : F)}) (h3 : α' ∈ u)
    (v : V) (e : ℕ) (hv : ∀ a ∈ u ^ e, T a v = 0) : ∀ a ∈ u, T a v = 0 := by
  have hp : ∀ x ∈ Ideal.span {(p : F)}, T x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, map_natCast]
    have hz : ((p : ℕ) : Module.End κ V) = 0 := by
      ext y
      rw [natCast_apply_eq_smul, ← Nat.cast_smul_eq_nsmul κ, CharP.cast_eq_zero, zero_smul]
      rfl
    rw [hz, mul_zero]
  have key : ∀ a ∈ u, T a = T (a * α') := by
    intro a ha
    have e1 : T (a * (α + α' - 1)) = 0 := hp _ (Ideal.mul_mem_left _ _ h2)
    have e2 : T (a * α) = 0 := hp _ (h1 a ha)
    have hs : a * α' = a + a * (α + α' - 1) - a * α := by ring
    rw [hs, map_sub, map_add (f := _), e1, e2]
    simp
  intro a ha
  have step : ∀ k : ℕ, T a = T (a * α' ^ k) ∧ a * α' ^ k ∈ u ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      obtain ⟨h, hm⟩ := ih
      refine ⟨?_, ?_⟩
      · rw [h, key _ (Ideal.pow_le_self (Nat.succ_ne_zero k) hm), pow_succ, _root_.mul_assoc]
      · rw [pow_succ α', ← _root_.mul_assoc, pow_succ u]
        exact Ideal.mul_mem_mul hm h3
  obtain ⟨h, hm⟩ := step e
  rw [h]
  exact hv _ (Ideal.pow_le_pow_right (Nat.le_succ e) hm)

private lemma comp_idpow {S : Scheme.{0}} {T G : Over S} [GrpObj G] (g : T ⟶ G) (n : ℕ) :
    g ≫ (𝟙 G) ^ n = g ^ n := by
  rw [MonObj.comp_pow, Category.comp_id]

private lemma tan_pow {κ : Type} [Field κ] (p : ℕ) [CharP κ p] {S : Scheme.{0}} (x : Sp κ ⟶ S) (G : Over S)
    [GrpObj G] [IsCommMonObj G] (g : epsPtR x ⟶ G) (hg : g ∈ GlobalTheory.TanPtMod.tanSub x G) (n : ℕ) (hn : p ∣ n) :
    g ^ n = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hv : (p * m) • (Additive.ofMul (⟨g, hg⟩ : GlobalTheory.TanPtMod.tanSub x G) : GlobalTheory.TanPtMod.Tan x G) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul κ, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, zero_smul]
  have h2 := congrArg (fun w => ((Additive.toMul w : GlobalTheory.TanPtMod.tanSub x G) : epsPtR x ⟶ G)) hv
  simpa using h2

private theorem left_one_eq_hom_comp_eta {S : Scheme.{0}} {T A : Over S} [GrpObj A] :
    Over.Hom.left (1 : T ⟶ A) = T.hom ≫ Over.Hom.left (η[A] : 𝟙_ (Over S) ⟶ A) := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

private theorem left_one_algPt_dualNumber_eq_epsPtR {κ : Type} [Field κ] {A : Over (Sp κ)} [GrpObj A] :
    Over.Hom.left (1 : algPt κ (DualNumber κ) ⟶ A) = Over.Hom.left (1 : epsPtR (𝟙 (Sp κ)) ⟶ A) := by
  rw [left_one_eq_hom_comp_eta, left_one_eq_hom_comp_eta]
  simp

theorem UpperTheory.Gal.crystallineComparison.Mod.tanOne_of :
    UElt → TanOne := by
  intro hU p _ D R _ b N hm ha r w hw κ _ _ _ β hβ o e
  have i0 : Fin D.a := ⟨0, by omega⟩
  have j0 : Fin D.m := ⟨0, by omega⟩
  have hi : ∀ i j : Fin D.a, i = j := fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have hj : ∀ i j : Fin D.m, i = j := fun i j => Fin.ext (by have := i.isLt; have := j.isLt; omega)
  have hwt : w ≠ ⊤ := by
    intro h
    have h0 := hβ i0 1 (h ▸ Submodule.mem_top)
    simp at h0
  obtain ⟨α, h1, h2, h3⟩ := hU p D r w hwt hw 1
  simp only [pow_one] at h1 h2 h3
  have hρ : β b.ρ = (r : κ) := by
    have h0 := hβ i0 _ (hw (sub_mem_uIdeal D r))
    rw [map_sub, map_sub, b.t_ω, map_intCast, map_intCast, sub_eq_zero] at h0
    exact h0
  let Tm : 𝓞 D.F →+* Module.End κ (GlobalTheory.TanPtMod.Tan (𝟙 (Sp κ)) o.A) :=
    (GlobalTheory.TanPtMod.actEnd o.act).comp (algebraMap (𝓞 D.F) D.O)
  let toE : (algPt κ (DualNumber κ) ⟶ o.A) → (epsPtR (𝟙 (Sp κ)) ⟶ o.A) :=
    fun v => Over.homMk v.left (by simp)
  let frE : (epsPtR (𝟙 (Sp κ)) ⟶ o.A) → (algPt κ (DualNumber κ) ⟶ o.A) :=
    fun v => Over.homMk v.left (by simp)
  have eig : ∀ v : algPt κ (DualNumber κ) ⟶ o.A, Inf (TrivSqZeroExt.fstHom κ κ κ) v →
      (∃ e', KilledBy o (uIdeal D r ^ e') v) →
      IsLieEigen (OActN.toF D o.act) (𝟙 (Sp κ)) (β.comp (b.t i0)) (toE v) := by
    intro v hinf ⟨e', hk⟩
    have hmem : toE v ∈ GlobalTheory.TanPtMod.tanSub (𝟙 (Sp κ)) o.A := by
      exact (GlobalTheory.TanPtMod.mem_tanSub_iff _ _ _).2 hinf
    have hkill : ∀ a ∈ uIdeal D r ^ e', Tm a (GlobalTheory.TanPtMod.Tan.mk (toE v) hmem) = 0 := by
      intro a ha'
      apply GlobalTheory.TanPtMod.Tan.ext
      show toE v ≫ o.act.act (algebraMap _ _ a) = 1
      ext1
      have h4 := congrArg Over.Hom.left (hk a ha')
      rw [Over.comp_left] at h4
      rw [Over.comp_left]
      exact h4.trans left_one_algPt_dualNumber_eq_epsPtR
    have hu := alg_core p Tm (uIdeal D r) α (D.bar α) h1 h2 h3 _ e' hkill
    have hsc : IsTanScal o.act (𝟙 (Sp κ)) (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) (toE v) := by
      refine ⟨?_, ?_⟩
      · rw [GlobalTheory.TanPtMod.mem_tanSub_iff] at hmem
        exact hmem
      · have hz := hu _ (sub_mem_uIdeal D r)
        rw [map_sub, LinearMap.sub_apply, sub_eq_zero, map_intCast] at hz
        have hz2 := congrArg GlobalTheory.TanPtMod.Tan.hom hz
        rw [intCast_apply_eq_smul, ← Int.cast_smul_eq_zsmul κ, GlobalTheory.TanPtMod.Tan.hom_smul] at hz2
        rw [hρ]
        exact congrArg Over.Hom.left hz2
    obtain ⟨w', hw', hprod⟩ := o.lie κ β (𝟙 (Sp κ)) (Category.id_comp _) (toE v) hsc
    rw [ofFn_prod_one ha, hi ⟨0, _⟩ i0] at hprod
    refine ⟨hsc.1, fun c => ?_⟩
    have h5 := (hw' i0 c).2
    rw [← hprod] at h5
    exact h5
  obtain ⟨vs, hvs, huniq⟩ := o.lieRank κ (𝟙 (Sp κ)) β (Category.id_comp _) i0
  refine ⟨frE (vs j0), ⟨?_, 1, ?_⟩, ?_, ?_⟩
  · ext1
    rw [Over.comp_left, left_one_algPt_dualNumber_eq_epsPtR]
    have hm0 : vs j0 ∈ GlobalTheory.TanPtMod.tanSub (𝟙 (Sp κ)) o.A := by
      rw [GlobalTheory.TanPtMod.mem_tanSub_iff]
      exact (hvs j0).1
    have h6 := tan_pow p (𝟙 (Sp κ)) o.A (vs j0) hm0 (p ^ (e + 1)) (dvd_pow_self p (Nat.succ_ne_zero e))
    rw [← comp_idpow] at h6
    exact congrArg Over.Hom.left h6
  · intro a ha'
    rw [pow_one] at ha'
    ext1
    rw [Over.comp_left, left_one_algPt_dualNumber_eq_epsPtR]
    have hz : β (b.t i0 a) = 0 := hβ i0 a (hw ha')
    have h7 := (hvs j0).2 a
    rw [RingHom.comp_apply, hz] at h7
    have h0 := congrArg Over.Hom.left (GlobalTheory.GrpTangentPt.epsScalePt_zero_comp (𝟙 (Sp κ)) (hvs j0).1)
    rw [← h0]
    exact h7
  · exact (hvs j0).1
  · intro v ⟨_, hk⟩ hinf
    obtain ⟨c, ⟨u', hu', hprod⟩, -⟩ := huniq (toE v) (eig v hinf hk)
    rw [ofFn_prod_one hm, hj ⟨0, _⟩ j0] at hprod
    refine ⟨c j0, ?_⟩
    have h8 := hu' j0
    rw [← hprod] at h8
    exact h8
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem kerAt_sub {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N}
    {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (x : X ⟶ M.X) (hz : z ≫ T.s = x) :
    ∃ K : Subgroup (Over.mk x ⟶ M.univ.A), (∀ g, g ∈ K ↔ KerAt T z g.left) ∧
      ∀ g ∈ K, ∀ a : D.O, g ≫ M.univ.act.act a ∈ K := by
  subst hz
  obtain ⟨-, hmon, hact, -⟩ := T.isog
  haveI := hmon
  let e := T.ms.ptEquiv (Over.mk z)
  have key : ∀ g : Over.mk (z ≫ T.s) ⟶ M.univ.A, KerAt T z g.left ↔ e.symm g ≫ T.ψ = 1 := by
    intro g
    constructor
    · intro h
      apply h
      rw [← ObjMap.ptEquiv_left, MulEquiv.apply_symm_apply]
    · intro h a' ha'
      have hq : a' = e.symm g := by
        apply e.injective
        rw [MulEquiv.apply_symm_apply]
        apply Over.OverMorphism.ext
        rw [ObjMap.ptEquiv_left]
        exact ha'
      rw [hq]
      exact h
  let f : (Over.mk z ⟶ T.o.A) →* (Over.mk z ⟶ T.o'.A) :=
    { toFun := fun a => a ≫ T.ψ
      map_one' := MonObj.one_comp _
      map_mul' := fun a b => MonObj.mul_comp a b _ }
  refine ⟨f.ker.comap e.symm.toMonoidHom, fun g => (key g).symm, ?_⟩
  intro g hg a
  have hs : e.symm (g ≫ M.univ.act.act a) = e.symm g ≫ T.o.act.act a := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, ObjMap.ptEquiv_act, MulEquiv.apply_symm_apply]
  haveI := T.o'.act.hom a
  change e.symm (g ≫ M.univ.act.act a) ≫ T.ψ = 1
  change e.symm g ≫ T.ψ = 1 at hg
  rw [hs, Category.assoc, hact a, ← Category.assoc, hg, MonObj.one_comp]

theorem UpperTheory.Gal.crystallineComparison.Mod.secEquiv_of :
    WVal → RankN → ValPtsX → SecCard → SecInj → SecSurj → SecEquiv := by
  intro hW hR hV hC hI hS p _ D O _ _ _ _ f b N r w _ hstd M j hj T V _ _ _ _ hp x W
  obtain ⟨ρ, hρl, hρc, hρk, hρT⟩ := hW p D O b N M w V x
  let q : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let u : Over.mk (q ≫ x) ⟶ Over.mk x := Over.homMk q rfl
  have hρu : ∀ g, ρ g = u ≫ g := by
    intro g
    apply Over.OverMorphism.ext
    rw [hρl, Over.comp_left]
    rfl
  haveI : IsProper M.univ.A.hom := M.univ.ab.proper
  haveI := T.fin
  obtain ⟨hAu, hAe⟩ := hV _ _ M.univ.A.hom inferInstance V x
  obtain ⟨hYu, hYe⟩ := hV _ _ T.s inferInstance V x
  have uinj : ∀ g g' : Over.mk x ⟶ M.univ.A, u ≫ g = u ≫ g' → g = g' := by
    intro g g' hg
    apply Over.OverMorphism.ext
    apply hAu _ _ (Over.w g) (Over.w g')
    have := congrArg CommaMorphism.left hg
    simpa [u] using this
  have usurj : ∀ g' : Over.mk (q ≫ x) ⟶ M.univ.A, ∃ g, u ≫ g = g' := by
    intro g'
    obtain ⟨gl, hgl, hgl'⟩ := hAe g'.left (Over.w g')
    refine ⟨Over.homMk gl hgl, ?_⟩
    apply Over.OverMorphism.ext
    simpa [u] using hgl'
  have pt0 : W.pt 0 = 1 := by
    have h := W.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hK := fun z : { z : Sp V ⟶ T.Y // z ≫ T.s = x } => kerAt_sub T z.1 x z.2
  choose Kz hKz hKa using hK
  let U : { z : Sp V ⟶ T.Y // z ≫ T.s = x } → Submodule (𝓞 D.F ⧸ w) W.H := fun z =>
    { carrier := {h | KerAt T z.1 (W.pt h).left}
      add_mem' := by
        intro a c ha hc
        change KerAt T z.1 (W.pt (a + c)).left
        rw [← hKz, W.add]
        exact mul_mem ((hKz z _).2 ha) ((hKz z _).2 hc)
      zero_mem' := by
        change KerAt T z.1 (W.pt 0).left
        rw [← hKz, pt0]
        exact one_mem _
      smul_mem' := by
        intro c h hh
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        change KerAt T z.1 (W.pt _).left
        rw [← hKz, W.smul]
        exact hKa z _ ((hKz z _).2 hh) _ }
  have hU : ∀ z h, h ∈ U z ↔ KerAt T z.1 (W.pt h).left := fun _ _ => Iff.rfl
  have hpK : ((p : ℕ) : FractionRing V) ≠ 0 := by
    intro h0
    apply hp
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_natCast, map_zero]
    exact h0
  let Φ : W.H → (Over.mk (q ≫ x) ⟶ M.univ.A) := fun h => u ≫ W.pt h
  have hΦinj : Function.Injective Φ := fun a c h => W.inj (uinj _ _ h)
  have hΦrange : ∀ g', (∃ h, Φ h = g') ↔ KilledBy M.univ w g' := by
    intro g'
    obtain ⟨g, rfl⟩ := usurj g'
    constructor
    · rintro ⟨h, hh⟩
      have := uinj _ _ hh
      rw [← this, ← hρu, ← hρk]
      exact (W.range _).1 ⟨h, rfl⟩
    · intro hk
      rw [← hρu, ← hρk] at hk
      obtain ⟨h, hh⟩ := (W.range g).2 hk
      exact ⟨h, by simp only [Φ, hh]⟩
  have hΦT : ∀ z h, h ∈ U z ↔ KerAt T (q ≫ z.1) (Φ h).left := by
    intro z h
    rw [hU, hρT r j _ T z.1 z.2, hρu]
  have hcardU : ∀ z, Nat.card (U z) = Ideal.absNorm w ^ j := by
    intro z
    have e1 : (U z) ≃ {g' : Over.mk (q ≫ x) ⟶ M.univ.A //
        KilledBy M.univ w g' ∧ KerAt T (q ≫ z.1) g'.left} :=
      Equiv.ofBijective (fun h => ⟨Φ h.1, (hΦrange _).1 ⟨_, rfl⟩, (hΦT z h.1).1 h.2⟩) (by
        constructor
        · intro a c h
          apply Subtype.ext
          apply hΦinj
          exact congrArg Subtype.val h
        · rintro ⟨g', hk, hT⟩
          obtain ⟨h, rfl⟩ := (hΦrange g').2 hk
          exact ⟨⟨h, (hΦT z h).2 hT⟩, rfl⟩)
    rw [Nat.card_congr e1]
    exact hC p D O b N M r w j _ T hstd.m1 (FractionRing V) hpK (q ≫ x) (q ≫ z.1)
      (by rw [Category.assoc, z.2])
  haveI : Module.Finite (𝓞 D.F ⧸ w) W.H := (hR p D O f b N r w hstd M V hp x W).1
  have hck : Nat.card (𝓞 D.F ⧸ w) = Ideal.absNorm w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) := by
    apply Nat.finite_of_card_ne_zero
    rw [hck, hstd.norm]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have h2 : 2 ≤ Ideal.absNorm w := by
    rw [← hck]
    exact Finite.one_lt_card
  have hrk : ∀ z, Module.finrank (𝓞 D.F ⧸ w) (U z) = j := by
    intro z
    apply Nat.pow_right_injective h2
    simp only
    rw [← hcardU z, ← hck, Module.natCard_eq_pow_finrank (K := 𝓞 D.F ⧸ w) (V := U z)]
  have ptneg : ∀ a, W.pt (-a) = (W.pt a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_right
    rw [← W.add, add_neg_cancel, pt0]
  refine ⟨Equiv.ofBijective (fun z => ⟨U z, hrk z⟩) ⟨?_, ?_⟩, fun z h => Iff.rfl⟩
  · intro z1 z2 hz
    have hUe : U z1 = U z2 := congrArg Subtype.val hz
    apply Subtype.ext
    apply hYu _ _ z1.2 z2.2
    apply hI p D O f b N r w hstd M j hj T (FractionRing V) hpK (q ≫ x) (q ≫ z1.1) (q ≫ z2.1)
      (by rw [Category.assoc, z1.2]) (by rw [Category.assoc, z2.2])
    intro g' hk
    obtain ⟨h, rfl⟩ := (hΦrange g').2 hk
    rw [← hΦT, ← hΦT, hUe]
  · rintro ⟨Us, hrank⟩
    let GK : Subgroup (Over.mk (q ≫ x) ⟶ M.univ.A) :=
      { carrier := {g' | ∃ h ∈ Us, Φ h = g'}
        one_mem' := ⟨0, Us.zero_mem, by simp only [Φ, pt0, MonObj.comp_one]⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
          exact ⟨a + c, Us.add_mem ha hc, by simp only [Φ, W.add, MonObj.comp_mul]⟩
        inv_mem' := by
          rintro _ ⟨a, ha, rfl⟩
          exact ⟨-a, Us.neg_mem ha, by simp only [Φ, ptneg, GrpObj.comp_inv]⟩ }
    have hmem : ∀ h, Φ h ∈ GK ↔ h ∈ Us := by
      intro h
      constructor
      · rintro ⟨h', hh', he⟩
        rw [← hΦinj he]
        exact hh'
      · intro hh
        exact ⟨h, hh, rfl⟩
    have hcardG : Nat.card GK = Ideal.absNorm w ^ j := by
      have e2 : Us ≃ GK := Equiv.ofBijective (fun h => ⟨Φ h.1, (hmem h.1).2 h.2⟩) (by
        constructor
        · intro a c h
          apply Subtype.ext
          apply hΦinj
          exact congrArg Subtype.val h
        · rintro ⟨g', h, hh, rfl⟩
          exact ⟨⟨h, hh⟩, rfl⟩)
      rw [← Nat.card_congr e2, Module.natCard_eq_pow_finrank (K := 𝓞 D.F ⧸ w) (V := Us), hck, hrank]
    obtain ⟨y, hys, hyG⟩ := hS p D O f b N r w hstd M j hj T (FractionRing V) hpK (q ≫ x) GK
      (by
        rintro _ ⟨h, -, rfl⟩
        exact (hΦrange _).1 ⟨h, rfl⟩)
      (by
        rintro _ ⟨h, hh, rfl⟩ a
        refine ⟨Ideal.Quotient.mk w a • h, Us.smul_mem _ hh, ?_⟩
        simp only [Φ, W.smul, Category.assoc])
      hcardG
    obtain ⟨z, hzs, hzq⟩ := hYe y hys
    refine ⟨⟨z, hzs⟩, ?_⟩
    apply Subtype.ext
    ext h
    change h ∈ U ⟨z, hzs⟩ ↔ h ∈ Us
    rw [hΦT, ← hmem]
    change KerAt T (q ≫ z) _ ↔ _
    rw [hzq]
    exact hyG _ ((hΦrange _).1 ⟨h, rfl⟩)
end
