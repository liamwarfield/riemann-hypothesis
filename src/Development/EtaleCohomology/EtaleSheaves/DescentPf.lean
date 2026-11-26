module

public import Development.EtaleCohomology.EtaleSheaves.PartDiagCut
public import Development.EtaleCohomology.EtaleSheaves.TwistTensorRestriction
public import Development.EtaleCohomology.EtaleSheaves.LPrimLocPf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.DescentPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.DescentPf

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

theorem val_smul {q : ℕ} [NeZero q] (i : ℤ) {U : Scheme.{0}} (c : ZMod q) (x : Sec (tw q i) U) :
    c.val • x = (ULift.up c : ULift.{1} (ZMod q)) • x := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  congr 1
  apply ULift.ext
  rw [ULift.down_natCast, ZMod.natCast_zmod_val]

theorem Descent_of (hAC : LateralTheory.E.LCBijPf.TwGenNZAC) : LateralTheory.E.LCSurjPf.Descent := by
  intro q _ i m hm B _ ζ y hloc
  obtain ⟨S, hS, hP⟩ := hloc
  have hform : ∀ {V W : Scheme.{0}} (g : V ⟶ Spec (CommRingCat.of B)) (h : W ⟶ V) (c : ZMod q),
      Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom) →
      Sec.res (h ≫ g) y = c.val • twGen i ((gam ζ).map (h ≫ g).appTop.hom) := by
    intro V W g h c hc
    have hs : ∀ x : Sec (tw q i) V, Sec.res h (c.val • x) = c.val • Sec.res h x := fun x => map_nsmul _ _ x
    rw [res_comp, hc, hs, LateralTheory.E.LCBijPf.twGen_res]
    rfl
  have huniq : ∀ {V1 V2 : Scheme.{0}} (g1 : V1 ⟶ Spec (CommRingCat.of B)) (g2 : V2 ⟶ Spec (CommRingCat.of B))
      (c1 c2 : ZMod q), Sec.res g1 y = c1.val • twGen i ((gam ζ).map g1.appTop.hom) →
      Sec.res g2 y = c2.val • twGen i ((gam ζ).map g2.appTop.hom) →
      ∀ v1 v2, g1 v1 = g2 v2 → c1 = c2 := by
    intro V1 V2 g1 g2 c1 c2 h1 h2 v1 v2 hv
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v1 v2 hv
    let A := (pullback g1 g2).affineOpenCover
    obtain ⟨w, -⟩ := A.covers z
    let a := A.f (A.idx z)
    have e1 := hform g1 (a ≫ pullback.fst g1 g2) c1 h1
    have e2 := hform g2 (a ≫ pullback.snd g1 g2) c2 h2
    have hcomp : (a ≫ pullback.snd g1 g2) ≫ g2 = (a ≫ pullback.fst g1 g2) ≫ g1 := by
      simp [pullback.condition]
    rw [hcomp] at e2
    have hne : Nontrivial (A.X (A.idx z)) := PrimeSpectrum.nontrivial w
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((a ≫ pullback.fst g1 g2) ≫ g1)
    have key := LateralTheory.E.LCBijPf.twGenNZ_of hAC q i (A.X (A.idx z)) (ζ.map φ.hom) (c1 - c2)
    refine sub_eq_zero.1 (key ?_)
    have e := e1.symm.trans e2
    rw [← hφ] at e
    rw [LateralTheory.E.LCBijPf.gam_map]
    rw [val_smul, val_smul] at e
    have hup : (ULift.up (c1 - c2) : ULift.{1} (ZMod q)) = ULift.up c1 - ULift.up c2 := rfl
    rw [val_smul, hup, sub_smul, sub_eq_zero]
    exact e
  obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
  have hpiece : ∀ x : PrimeSpectrum B, ∃ (R : CommRingCat.{0}) (g : Spec R ⟶ Spec (CommRingCat.of B)),
      Etale g ∧ S.arrows g ∧ x ∈ Set.range g := by
    intro x
    obtain ⟨j, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 x
    let A := (𝒰.X j).affineOpenCover
    obtain ⟨w, hw⟩ := A.covers v
    have : Etale (𝒰.f j) := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).2 j
    refine ⟨A.X (A.idx v), A.f (A.idx v) ≫ 𝒰.f j, inferInstance, S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk j)) _, ⟨w, ?_⟩⟩
    rw [Scheme.Hom.comp_apply, hw, hv]
  choose R g hg hSg hx using hpiece
  have hc : ∀ x, ∃ c : ZMod q, Sec.res (g x) y = c.val • twGen i ((gam ζ).map (g x).appTop.hom) :=
    fun x => hP _ _ (hSg x)
  choose c hc using hc
  have key : ∀ (x : PrimeSpectrum B) {V : Scheme.{0}} (g' : V ⟶ Spec (CommRingCat.of B)) (c' : ZMod q),
      Sec.res g' y = c'.val • twGen i ((gam ζ).map g'.appTop.hom) → ∀ v, g' v = x → c x = c' := by
    intro x V g' c' h' v hv
    obtain ⟨u, hu⟩ := hx x
    exact huniq (g x) g' _ _ (hc x) h' u v (hu.trans hv.symm)
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have := hg x
    refine ⟨Set.range (g x), (g x).isOpenMap.isOpen_range, hx x, fun x' hx' => ?_⟩
    obtain ⟨u, hu⟩ := hx'
    exact key x' (g x) (c x) (hc x) u hu
  let ψ : LocallyConstant (PrimeSpectrum B) (ZMod q) := ⟨c, hlc⟩
  refine ⟨ψ, Sieve.ofArrows (fun x => Spec (R x)) g, ?_, ?_⟩
  · exact Scheme.Cover.mem_grothendieckTopology
      (Scheme.Cover.mkOfCovers (P := @Etale) (PrimeSpectrum B) (fun x => Spec (R x)) g
        (fun x => by obtain ⟨u, hu⟩ := hx x; exact ⟨x, u, hu⟩) hg)
  · intro V k hk
    obtain ⟨W, h, k', hk', rfl⟩ := hk
    obtain ⟨x⟩ := hk'
    rw [res_comp, res_comp]
    congr 1
    rw [hc x]
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (g x)
    have hlc' : lcMap φ.hom ψ = LocallyConstant.const _ (c x) := by
      ext u
      exact key _ (g x) (c x) (hc x) u (by rw [← hφ]; rfl)
    have e := hm.1 B (R x) φ.hom ζ ψ
    rw [hlc', hm.2, LateralTheory.E.LCBijPf.gam_map] at e
    rw [← hφ]
    exact e.symm

end LateralTheory.E.DescentPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PartAPf
noncomputable section
open LateralTheory.E.PartDiagCut

namespace LateralTheory.E.PartAPf

variable {B : Type} [CommRing B]

theorem one_mem_S (I : Ideal B) {e : B ⧸ I} {u : B} (hu : Ideal.Quotient.mk I u = e) (he : IsIdempotentElem e) :
    u ∈ S I e := ⟨1, by rw [hu, mul_one, he.eq]⟩

theorem mem_map_of_comp (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I P)
    (hz : ∀ e : P.1, z e ∈ I.map (algebraMap B (Localization (S I e.1)))) : z ∈ I.map (βP I P) := by
  classical
  choose a ha using fun e : P.1 =>
    (IsLocalization.mem_map_algebraMap_iff (S I e.1) (Localization (S I e.1))).1 (hz e)
  have key : z = ∑ e : P.1, βP I P ((a e).1 : B) *
      Pi.single e (IsLocalization.mk' (Localization (S I e.1)) (1 : B) (a e).2) := by
    funext e'
    rw [Finset.sum_apply, Finset.sum_eq_single e']
    · simp only [Pi.mul_apply, Pi.single_eq_same, βP, RingHom.pi_apply]
      rw [← IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.eq_mk'_iff_mul_eq]
      exact ha e'
    · intro e _ hne
      simp [Pi.single_eq_of_ne' hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [key]
  exact Ideal.sum_mem _ fun e _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (a e).1.2)

theorem comp_mem (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (z : PiLocalization₂ I P) (hz : z ∈ I.map (βP I P)) (e : P.1) :
    z e ∈ I.map (algebraMap B (Localization (S I e.1))) := by
  have h := Ideal.mem_map_of_mem (Pi.evalRingHom (fun e : P.1 => Localization (S I e.1)) e) hz
  rw [Ideal.map_map] at h
  exact h

theorem sum_mul_single (I : Ideal B) (P : PartDiagCut.Part (B ⧸ I)) (c : P.1 → B ⧸ I) (e' : P.1) :
    (∑ e : P.1, c e * e.1) * e'.1 = c e' * e'.1 := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single e']
  · rw [mul_assoc, (P.idem e'.1 e'.2).1.eq]
  · intro e _ hne
    rw [mul_assoc, P.orth e.1 e.2 e'.1 e'.2 (fun h => hne (Subtype.ext h)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem PartA_of : PartA := by
  intro B _ I P
  classical
  constructor
  · apply Ideal.quotientMap_injective'
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hcomp : ∀ e : P.1, Ideal.Quotient.mk I x * e.1 = 0 := by
      intro e
      have h := comp_mem I P _ hx e
      obtain ⟨⟨i, s⟩, hs⟩ := (IsLocalization.mem_map_algebraMap_iff (S I e.1) (Localization (S I e.1))).1 h
      simp only [βP, RingHom.pi_apply] at hs
      rw [← map_mul] at hs
      obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (S I e.1) (Localization (S I e.1))).1 hs
      have hq := congrArg (Ideal.Quotient.mk I) hc
      rw [map_mul, map_mul, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 i.2, mul_zero] at hq
      obtain ⟨t, ht⟩ := c.2
      obtain ⟨t', ht'⟩ := s.2
      calc Ideal.Quotient.mk I x * e.1
          = Ideal.Quotient.mk I x * ((Ideal.Quotient.mk I c * t * e.1) * (Ideal.Quotient.mk I s * t' * e.1)) := by
            rw [ht, ht', (P.idem e.1 e.2).1.eq]
        _ = (Ideal.Quotient.mk I c * (Ideal.Quotient.mk I x * Ideal.Quotient.mk I s)) * (t * t' * e.1 * e.1) := by ring
        _ = 0 := by rw [hq, zero_mul]
    calc Ideal.Quotient.mk I x = Ideal.Quotient.mk I x * ∑ e ∈ P.1, e := by rw [P.sum_eq, mul_one]
      _ = ∑ e : P.1, Ideal.Quotient.mk I x * e.1 := by
          rw [Finset.mul_sum, ← Finset.sum_coe_sort P.1]
      _ = 0 := Finset.sum_eq_zero fun e _ => hcomp e
  · intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hB : ∀ e : P.1, ∃ (b : B) (s : S I e.1), IsLocalization.mk' (Localization (S I e.1)) b s = y e :=
      fun e => by
        obtain ⟨⟨b, s⟩, h⟩ := IsLocalization.mk'_surjective (S I e.1) (y e)
        exact ⟨b, s, h⟩
    choose b s hbs using hB
    have hS : ∀ e : P.1, ∃ t, Ideal.Quotient.mk I (s e : B) * t * e.1 = e.1 := fun e => (s e).2
    choose t ht using hS
    choose τ hτ using fun e : P.1 => Ideal.Quotient.mk_surjective (t e)
    choose ε hε using fun e : P.1 => Ideal.Quotient.mk_surjective e.1
    refine ⟨Ideal.Quotient.mk _ (∑ e : P.1, b e * τ e * ε e), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    apply mem_map_of_comp
    intro e'
    set x := ∑ e : P.1, b e * τ e * ε e
    have hεS : ε e' ∈ S I e'.1 := one_mem_S I (hε e') (P.idem e'.1 e'.2).1
    rw [IsLocalization.mem_map_algebraMap_iff (S I e'.1) (Localization (S I e'.1))]
    refine ⟨⟨⟨(x * s e' - b e') * ε e', ?_⟩, s e' * ⟨ε e', hεS⟩⟩, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_sub, map_mul, hε]
      have hx : Ideal.Quotient.mk I x = ∑ e : P.1, (Ideal.Quotient.mk I (b e) * t e) * e.1 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [x, map_sum, map_mul, hτ, hε]
      rw [sub_mul, mul_right_comm, hx, sum_mul_single]
      calc Ideal.Quotient.mk I (b e') * t e' * e'.1 * Ideal.Quotient.mk I (s e') - Ideal.Quotient.mk I (b e') * e'.1
          = Ideal.Quotient.mk I (b e') * (Ideal.Quotient.mk I (s e') * t e' * e'.1) - Ideal.Quotient.mk I (b e') * e'.1 := by ring
        _ = 0 := by rw [ht e', sub_self]
    · simp only [Pi.sub_apply, βP, RingHom.pi_apply, Submonoid.coe_mul, map_mul, map_sub, ← hbs e']
      rw [sub_mul, sub_mul, ← mul_assoc (IsLocalization.mk' _ _ _), IsLocalization.mk'_spec]
      ring

end LateralTheory.E.PartAPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.BaerFlatZModCriterion
noncomputable section

namespace LateralTheory.E.BaerFlatZModCriterion

open TensorProduct

section General

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_eq_smul_of_baer (hB : Module.Baer R M) {a b : R}
    (hab : ∀ r, b * r = 0 → ∃ s, r = a * s) {m : M} (hm : a • m = 0) : ∃ m' : M, m = b • m' := by
  let f : R →ₗ[R] R := LinearMap.toSpanSingleton R R b
  have hker : LinearMap.ker f ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
    intro x hx
    simp only [LinearMap.mem_ker, f, LinearMap.toSpanSingleton_apply, smul_eq_mul] at hx ⊢
    obtain ⟨s, rfl⟩ := hab x (by rw [mul_comm]; exact hx)
    rw [mul_comm, mul_smul, hm, smul_zero]
  let g : LinearMap.range f →ₗ[R] M :=
    (LinearMap.ker f).liftQ (LinearMap.toSpanSingleton R M m) hker ∘ₗ f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g', hg'⟩ := hB (LinearMap.range f) g
  refine ⟨g' 1, ?_⟩
  have h1 : f 1 = b := by simp [f]
  have hmem : b ∈ LinearMap.range f := ⟨1, h1⟩
  have := hg' b hmem
  have hg : g ⟨b, hmem⟩ = m := by
    have e : (⟨b, hmem⟩ : LinearMap.range f) = ⟨f 1, LinearMap.mem_range_self f 1⟩ := Subtype.ext h1.symm
    rw [e]
    simp only [g, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearMap.quotKerEquivRange_symm_apply_image]
    rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [← hg, ← this, ← map_smul, smul_eq_mul, mul_one]

theorem flat_of_baer [IsPrincipalIdealRing R]
    (hA : ∀ a : R, ∃ b, a * b = 0 ∧ ∀ r, b * r = 0 → ∃ s, r = a * s) (hB : Module.Baer R M) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lift_lsmul_comp_subtype_injective]
  intro I _
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal I
  have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
  have pure : ∀ x : I ⊗[R] M, ∃ m : M, x = (⟨a, haI⟩ : I) ⊗ₜ m := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [tmul_zero]⟩
    | tmul y n =>
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (by rw [← ha]; exact y.2)
      refine ⟨c • n, ?_⟩
      rw [← smul_tmul]
      congr 1
      exact Subtype.ext hc.symm
    | add x y hx hy =>
      obtain ⟨m1, rfl⟩ := hx
      obtain ⟨m2, rfl⟩ := hy
      exact ⟨m1 + m2, by rw [tmul_add]⟩
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨m, rfl⟩ := pure x
  simp only [lift.tmul, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearMap.lsmul_apply] at hx
  obtain ⟨b, hab, hb⟩ := hA a
  obtain ⟨m', rfl⟩ := exists_eq_smul_of_baer hB hb hx
  rw [← smul_tmul]
  have : b • (⟨a, haI⟩ : I) = 0 := Subtype.ext (by simp [smul_eq_mul, mul_comm, hab])
  rw [this, zero_tmul]

end General

section ZModPart

theorem zmod_ann (q : ℕ) [NeZero q] (a : ZMod q) :
    ∃ b : ZMod q, a * b = 0 ∧ ∀ r : ZMod q, b * r = 0 → ∃ s, r = a * s := by
  obtain ⟨n, hn⟩ : ∃ n, n = a.val := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd n q := ⟨_, rfl⟩
  have hq : 0 < q := NeZero.pos q
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_right _ hq
  have hgq : g ∣ q := hg ▸ Nat.gcd_dvd_right n q
  have hgn : g ∣ n := hg ▸ Nat.gcd_dvd_left n q
  have hqg : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgq) hg0
  have ha : a = (n : ZMod q) := by rw [hn, ZMod.natCast_zmod_val]
  refine ⟨((q / g : ℕ) : ZMod q), ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hgn
    rw [ha, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨k, ?_⟩
    rw [hk, mul_comm g k, mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
  · intro r hr
    have hr' : q ∣ (q / g) * r.val := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val]
      exact hr
    have hdiv : g ∣ r.val := by
      have h2 : (q / g) * g ∣ (q / g) * r.val := by rw [Nat.div_mul_cancel hgq]; exact hr'
      exact Nat.dvd_of_mul_dvd_mul_left hqg h2
    obtain ⟨t, ht⟩ := hdiv
    have hz := Nat.gcd_eq_gcd_ab n q
    have hgz : (g : ZMod q) = a * (Nat.gcdA n q : ZMod q) := by
      have := congrArg (Int.cast : ℤ → ZMod q) hz
      push_cast at this
      rw [ZMod.natCast_self, zero_mul, add_zero, ← hg] at this
      rw [this, ha]
    refine ⟨(Nat.gcdA n q : ZMod q) * (t : ZMod q), ?_⟩
    rw [← ZMod.natCast_zmod_val r, ht, Nat.cast_mul, hgz, mul_assoc]

end ZModPart

end LateralTheory.E.BaerFlatZModCriterion

open LateralTheory.E.ZModFlatnessFromBaerCriterion LateralTheory.E.BaerFlatZModCriterion in
theorem LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of : LeafInjFlatZMod := by
  intro q _ M _ _ hinj
  have : IsPrincipalIdealRing (ZMod q) :=
    IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod q)) ZMod.intCast_surjective
  have : IsPrincipalIdealRing (ULift.{1} (ZMod q)) :=
    IsPrincipalIdealRing.of_surjective (ULift.ringEquiv (R := ZMod q)).symm
      (ULift.ringEquiv (R := ZMod q)).symm.surjective
  refine flat_of_baer (fun a => ?_) (Module.Baer.of_injective hinj)
  obtain ⟨b, hab, hb⟩ := zmod_ann q a.down
  refine ⟨ULift.up b, ULift.ext hab, fun r hr => ?_⟩
  obtain ⟨s, hs⟩ := hb r.down (congrArg ULift.down hr)
  exact ⟨ULift.up s, ULift.ext hs⟩
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.OverMVPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf LateralTheory.E.InjStepPf

namespace LateralTheory.E.OverMVPf

variable {X S : Scheme.{0}}

@[reassoc]
theorem resO_fst (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.fst p U.ι = pullback.fst p V.ι := by
  simp only [resO, pullback.map, pullback.lift_fst, Category.comp_id]

theorem resO_snd (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.snd p U.ι ≫ U.ι = pullback.snd p V.ι ≫ V.ι := by
  simp only [resO, pullback.map, pullback.lift_snd_assoc, Category.assoc, Scheme.homOfLE_ι]

instance resO_open (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : IsOpenImmersion (resO p h) := by
  have : IsOpenImmersion (resO p h ≫ pullback.fst p U.ι) := by rw [resO_fst]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst p U.ι)

theorem range_sub {T : Scheme.{0}} (U : S.Opens) (a : T ⟶ U) :
    Set.range (a ≫ U.ι) ⊆ (U : Set S) := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Hom.comp_apply, ← Scheme.Opens.range_ι]
  exact ⟨_, rfl⟩

theorem cover (p : X ⟶ S) (V W : S.Opens) :
    Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) ∪ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  have hy : p (pullback.fst p (V ⊔ W).ι y) ∈ ((V ⊔ W : S.Opens) : Set S) := by
    have := range_sub (V ⊔ W) (pullback.snd p (V ⊔ W).ι) ⟨y, rfl⟩
    rwa [← pullback.condition, Scheme.Hom.comp_apply] at this
  have inj := (pullback.fst p (V ⊔ W).ι).isOpenEmbedding.injective
  rcases hy with hV | hW
  · obtain ⟨s, hs⟩ : p (pullback.fst p (V ⊔ W).ι y) ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := V.ι) _ s hs.symm
    left; refine ⟨z, inj ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hz]
  · obtain ⟨s, hs⟩ : p (pullback.fst p (V ⊔ W).ι y) ∈ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := W.ι) _ s hs.symm
    right; refine ⟨z, inj ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hz]

abbrev PP (p : X ⟶ S) (V W : S.Opens) : Scheme.{0} :=
  pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W))

abbrev g0 (p : X ⟶ S) (V W : S.Opens) : PP p V W ⟶ S := pullback.fst _ _ ≫ pullback.fst p V.ι ≫ p

theorem overOpenPullbackStructureMap_eq_via_left_open (p : X ⟶ S) (V W : S.Opens) : g0 p V W = pullback.fst _ _ ≫ pullback.snd p V.ι ≫ V.ι := by
  rw [g0, pullback.condition]

theorem overOpenPullbackStructureMap_eq_via_right_open (p : X ⟶ S) (V W : S.Opens) : g0 p V W = pullback.snd _ _ ≫ pullback.snd p W.ι ≫ W.ι := by
  rw [g0, ← pullback.condition, ← resO_fst_assoc p (le_sup_left : V ≤ V ⊔ W), pullback.condition_assoc, resO_fst_assoc]

theorem overOpenPullbackStructureMap_range_subset_inter (p : X ⟶ S) (V W : S.Opens) :
    Set.range (g0 p V W) ⊆ Set.range (V ⊓ W).ι := by
  rw [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf]
  intro s hs
  refine ⟨?_, ?_⟩
  · rw [overOpenPullbackStructureMap_eq_via_left_open, ← Category.assoc] at hs; exact range_sub V _ hs
  · rw [overOpenPullbackStructureMap_eq_via_right_open, ← Category.assoc] at hs; exact range_sub W _ hs

def kk (p : X ⟶ S) (V W : S.Opens) : PP p V W ⟶ overO p (V ⊓ W) :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst p V.ι) (IsOpenImmersion.lift (V ⊓ W).ι (g0 p V W) (overOpenPullbackStructureMap_range_subset_inter p V W))
    (by rw [IsOpenImmersion.lift_fac, Category.assoc])

def ee (p : X ⟶ S) (V W : S.Opens) : overO p (V ⊓ W) ⟶ PP p V W :=
  pullback.lift (resO p (inf_le_left : V ⊓ W ≤ V)) (resO p (inf_le_right : V ⊓ W ≤ W))
    (by rw [resO_comp, resO_comp])

@[reassoc]
theorem kk_fst' (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ pullback.fst p (V ⊓ W).ι = pullback.fst _ _ ≫ pullback.fst p V.ι := by
  simp only [kk, pullback.lift_fst]

theorem kk_snd' (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ pullback.snd p (V ⊓ W).ι ≫ (V ⊓ W).ι = g0 p V W := by
  simp only [kk, pullback.lift_snd_assoc, IsOpenImmersion.lift_fac]

theorem kk_l (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ resO p (inf_le_left : V ⊓ W ≤ V) = pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, resO_fst, kk_fst']
  · rw [← cancel_mono V.ι, Category.assoc, Category.assoc, resO_snd, kk_snd', overOpenPullbackStructureMap_eq_via_left_open, Category.assoc]

theorem kk_r (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ resO p (inf_le_right : V ⊓ W ≤ W) = pullback.snd _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, resO_fst, kk_fst', ← resO_fst p (le_sup_left : V ≤ V ⊔ W), pullback.condition_assoc, resO_fst]
  · rw [← cancel_mono W.ι, Category.assoc, Category.assoc, resO_snd, kk_snd', overOpenPullbackStructureMap_eq_via_right_open, Category.assoc]

theorem kk_ee (p : X ⟶ S) (V W : S.Opens) : kk p V W ≫ ee p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, ee, pullback.lift_fst, kk_l, Category.id_comp]
  · rw [Category.assoc, ee, pullback.lift_snd, kk_r, Category.id_comp]

theorem ee_kk (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ kk p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, kk_fst', ee, pullback.lift_fst_assoc, resO_fst, Category.id_comp]
  · rw [← cancel_mono (V ⊓ W).ι, Category.assoc, Category.assoc, kk_snd', g0, ee, pullback.lift_fst_assoc,
      resO_fst_assoc, pullback.condition, Category.id_comp]

theorem ee_fst (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ pullback.fst _ _ = resO p (inf_le_left : V ⊓ W ≤ V) := by
  simp only [ee, pullback.lift_fst]

theorem ee_snd (p : X ⟶ S) (V W : S.Opens) : ee p V W ≫ pullback.snd _ _ = resO p (inf_le_right : V ⊓ W ≤ W) := by
  simp only [ee, pullback.lift_snd]

@[reassoc]
theorem fO_fst {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.fst p U.ι = pullback.fst (f ≫ p) U.ι ≫ f := by
  simp only [fO, pullback.map, pullback.lift_fst]

@[reassoc]
theorem fO_snd {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.snd p U.ι = pullback.snd (f ≫ p) U.ι := by
  simp only [fO, pullback.map, pullback.lift_snd, Category.comp_id]

theorem kk_nat {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (V W : S.Opens) :
    kk (f ≫ p) V W ≫ fO f p (V ⊓ W) = pullback.map _ _ _ _ (fO f p V) (fO f p W) (fO f p (V ⊔ W))
      (fO_res f p le_sup_left) (fO_res f p le_sup_right) ≫ kk p V W := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, fO_fst, kk_fst'_assoc, kk_fst', pullback.lift_fst_assoc, Category.assoc, fO_fst]
  · rw [← cancel_mono (V ⊓ W).ι, Category.assoc, Category.assoc, Category.assoc, Category.assoc, fO_snd_assoc, kk_snd',
      kk_snd', g0, g0, pullback.lift_fst_assoc, Category.assoc, fO_fst_assoc]

theorem OverMV_of : OverMV := by
  intro hM hH q Y X S f p i m V W
  obtain ⟨δ, hex, hnat⟩ := hM hH (ZMod q) (tw q i)
  have cX := cover p V W
  have cY := cover (f ≫ p) V W
  refine ⟨(δ (resO p le_sup_left) (resO p le_sup_right) m).comp (pull _ (sch.map (kk p V W)) _ m),
    (δ (resO (f ≫ p) le_sup_left) (resO (f ≫ p) le_sup_right) m).comp (pull _ (sch.map (kk (f ≫ p) V W)) _ m),
    ?_, ?_, ?_, ?_⟩
  · intro x h1 h2
    obtain ⟨w', hw'⟩ := ((hex _ _ cX m).2.2 x).1 ⟨h1, h2⟩
    refine ⟨pull _ (sch.map (ee p V W)) _ _ w', ?_⟩
    rw [AddMonoidHom.comp_apply, ← pull_comp, ← Functor.map_comp, kk_ee, CategoryTheory.Functor.map_id, pull_id, hw']
  · intro a b
    rw [AddMonoidHom.comp_apply, map_sub, ← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, kk_l, kk_r]
    exact ((hex _ _ cX m).2.1 _).2 ⟨a, b, rfl⟩
  · intro w hw
    obtain ⟨a, b, hab⟩ := ((hex _ _ cY m).2.1 _).1 hw
    refine ⟨a, b, ?_⟩
    have e : w = pull _ (sch.map (ee (f ≫ p) V W)) _ _ (pull _ (sch.map (kk (f ≫ p) V W)) _ _ w) := by
      rw [← pull_comp, ← Functor.map_comp, ee_kk, CategoryTheory.Functor.map_id, pull_id]
    rw [e, hab, map_sub, ← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, ee_fst, ee_snd]
  · intro w
    rw [AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, ← pull_comp, ← Functor.map_comp, kk_nat, Functor.map_comp,
      pull_comp, hnat _ _ _ _ cY cX]

end LateralTheory.E.OverMVPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LocFormPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LocFormPf

instance ls (q : ℕ) (i : ℤ) : Presheaf.IsLocallySurjective Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)) :=
  Presheaf.isLocallySurjective_toSheafify'.{0, 1} (J := Scheme.etaleTopology.{0}) (Scheme.Γ ⋙ twF q i)

theorem loc_top {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hS'⟩ := hP
  obtain ⟨T, hT, hT'⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨hS' V g hg.1, hT' V g hg.2⟩⟩

theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (hP : ∀ (V W : Scheme.{0}) (k : W ⟶ V) (g : V ⟶ U), P V g → P W (k ≫ g))
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P := by
  obtain ⟨S, hS, hS'⟩ := h
  let R : Sieve U := { arrows := fun V g => P V g, downward_closed := fun {V W g} hg k => hP V W k g hg }
  refine ⟨R, Scheme.etaleTopology.transitive hS R fun V g hg => ?_, fun V g hg => hg⟩
  obtain ⟨T, hT, hT'⟩ := hS' V g hg
  exact Scheme.etaleTopology.superset_covering (fun W k hk => hT' W k hk) hT

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {X W V : Scheme.{0}} (k : X ⟶ W) (h : W ⟶ V) (s : Sec F V) :
    Sec.res (k ≫ h) s = Sec.res k (Sec.res h s) := by
  show (F.obj.map (k ≫ h).op).hom s = (F.obj.map k.op).hom ((F.obj.map h.op).hom s)
  rw [op_comp, Functor.map_comp]
  rfl

theorem prim_map_comp {q : ℕ} {X W V : Scheme.{0}} (k : X ⟶ W) (h : W ⟶ V) (ζ : Prim q Γ(V, ⊤)) :
    ζ.map (k ≫ h).appTop.hom = (ζ.map h.appTop.hom).map k.appTop.hom := by
  apply Subtype.ext
  show (k ≫ h).appTop.hom ζ.1 = k.appTop.hom (h.appTop.hom ζ.1)
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem sec_res (q : ℕ) (i : ℤ) {W V : Scheme.{0}} (h : W ⟶ V) (x : (twF q i).obj Γ(V, ⊤)) :
    Sec.res h (ofRings.sec (twF q i) V x) = ofRings.sec (twF q i) W ((twF q i).map (Scheme.Γ.map h.op) x) := by
  unfold Sec.res ofRings.sec
  erw [← ModuleCat.comp_apply, ← NatTrans.naturality, ConcreteCategory.comp_apply]

def Q (q : ℕ) (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U) (V : Scheme.{0}) (g : V ⟶ U) : Prop :=
  ∃ c : ULift.{1} (ZMod q), Sec.res g y = c • twGen i (ζ.map g.appTop.hom)

theorem Q_stable (q : ℕ) (i : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (y : Sec (tw q i) U)
    (V W : Scheme.{0}) (k : W ⟶ V) (g : V ⟶ U) (hg : Q q i ζ y V g) : Q q i ζ y W (k ≫ g) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  rw [res_comp, hc, prim_map_comp, ← LateralTheory.E.LCBijPf.twGen_res q i k (ζ.map g.appTop.hom)]
  exact LinearMap.map_smul ((tw q i).obj.map k.op).hom c _

end LateralTheory.E.LocFormPf

namespace LateralTheory.E.LocFormPf

theorem sec_add (q : ℕ) (i : ℤ) (V : Scheme.{0}) (x y : (twF q i).obj Γ(V, ⊤)) :
    ofRings.sec (twF q i) V (x + y) = ofRings.sec (twF q i) V x + ofRings.sec (twF q i) V y := by
  unfold ofRings.sec; exact map_add _ _ _

theorem sec_smul (q : ℕ) (i : ℤ) (V : Scheme.{0}) (c : ULift.{1} (ZMod q)) (x : (twF q i).obj Γ(V, ⊤)) :
    ofRings.sec (twF q i) V (c • x) = c • ofRings.sec (twF q i) V x := by
  unfold ofRings.sec; exact map_smul _ _ _

theorem sec_zero (q : ℕ) (i : ℤ) (V : Scheme.{0}) : ofRings.sec (twF q i) V 0 = 0 := by
  unfold ofRings.sec; exact map_zero _

def S (q : ℕ) (i : ℤ) (V : Scheme.{0}) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) : Sec (tw q i) V :=
  ofRings.sec (twF q i) V (Submodule.Quotient.mk f)

theorem S_zero (q : ℕ) (i : ℤ) (V : Scheme.{0}) : S q i V 0 = 0 := sec_zero q i V

theorem S_add (q : ℕ) (i : ℤ) (V : Scheme.{0}) (f g : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    S q i V (f + g) = S q i V f + S q i V g :=
  sec_add q i V (Submodule.Quotient.mk f) (Submodule.Quotient.mk g)

theorem S_smul (q : ℕ) (i : ℤ) (V : Scheme.{0}) (a : ULift.{1} (ZMod q)) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    S q i V (a • f) = a • S q i V f :=
  sec_smul q i V a (Submodule.Quotient.mk f)

theorem S_single (q : ℕ) (i : ℤ) (V : Scheme.{0}) (ζ : Prim q Γ(V, ⊤)) (a : ULift.{1} (ZMod q)) :
    S q i V (Finsupp.single ζ a) = a • twGen i ζ := by
  have h3 : Finsupp.single ζ a = a • Finsupp.single ζ (1 : ULift.{1} (ZMod q)) := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h3, S_smul]
  rfl

theorem S_res_single (q : ℕ) (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (ξ : Prim q Γ(V, ⊤)) (a : ULift.{1} (ZMod q)) :
    Sec.res k (S q i V (Finsupp.single ξ a)) = S q i W (Finsupp.single (ξ.map k.appTop.hom) a) := by
  refine (sec_res q i k _).trans ?_
  unfold S
  congr 1
  change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (Scheme.Γ.map k.op).hom) (Finsupp.single ξ a)) = _
  erw [Finsupp.mapDomain_single]
  rfl

theorem S_rel (q : ℕ) (i : ℤ) (W : Scheme.{0}) (ζ ξ : Prim q Γ(W, ⊤)) (e : (ZMod q)ˣ) (he : ξ.1 = ζ.1 ^ (e : ZMod q).val) :
    S q i W (Finsupp.single ξ 1) = S q i W (Finsupp.single ζ (ULift.up ((e ^ i : (ZMod q)ˣ) : ZMod q))) := by
  unfold S
  congr 1
  exact (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨ζ, ξ, e, he, rfl⟩)

theorem res_add {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (x y : Sec (tw q i) V) :
    Sec.res k (x + y) = Sec.res k x + Sec.res k y := map_add _ _ _

theorem res_smul {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) (c : ULift.{1} (ZMod q)) (x : Sec (tw q i) V) :
    Sec.res k (c • x) = c • Sec.res k x := map_smul _ _ _

theorem res_zero {q : ℕ} (i : ℤ) {W V : Scheme.{0}} (k : W ⟶ V) : Sec.res k (0 : Sec (tw q i) V) = 0 := map_zero _

theorem single_loc (q : ℕ) [NeZero q] (i : ℤ) {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) :
    Loc V fun W k => ∃ c : ULift.{1} (ZMod q), Sec.res k (S q i V (Finsupp.single ξ 1)) = c • twGen i (ζ.map k.appTop.hom) := by
  refine LateralTheory.E.L_prim_locPf.loc_mono' (LateralTheory.E.L_prim_locPf.c2 LateralTheory.E.L_prim_locPf.algPow q V ζ ξ)
    fun W k ⟨e, he⟩ => ⟨ULift.up ((e ^ i : (ZMod q)ˣ) : ZMod q), ?_⟩
  rw [S_res_single, S_rel q i W (ζ.map k.appTop.hom) (ξ.map k.appTop.hom) e he, S_single]

theorem elt_loc (q : ℕ) [NeZero q] (i : ℤ) {V : Scheme.{0}} (ζ : Prim q Γ(V, ⊤)) (f : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) :
    Loc V fun W k => ∃ c : ULift.{1} (ZMod q), Sec.res k (S q i V f) = c • twGen i (ζ.map k.appTop.hom) := by
  induction f using Finsupp.induction_linear with
  | zero => exact loc_top fun W k => ⟨0, by rw [S_zero, res_zero, zero_smul]⟩
  | add f g hf hg =>
    refine LateralTheory.E.L_prim_locPf.loc_mono' (loc_and hf hg) fun W k ⟨⟨c1, h1⟩, ⟨c2, h2⟩⟩ => ⟨c1 + c2, ?_⟩
    rw [S_add, res_add, h1, h2, add_smul]
  | single ξ a =>
    refine LateralTheory.E.L_prim_locPf.loc_mono' (single_loc q i ζ ξ) fun W k ⟨c, h⟩ => ⟨a * c, ?_⟩
    have h3 : Finsupp.single ξ a = a • Finsupp.single ξ (1 : ULift.{1} (ZMod q)) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h3, S_smul, res_smul, h, mul_smul]

theorem LocForm_of : LateralTheory.E.LCSurjPf.LocForm := by
  intro q _ i B _ ζ y
  have key : Loc (Spec (CommRingCat.of B)) (Q q i (gam ζ) y) := by
    apply loc_trans (Q_stable q i (gam ζ) y)
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i))
      (U := op (Spec (CommRingCat.of B))) y, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hg
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (x : (twF q i).obj Γ(V, ⊤))
    have hy : Sec.res g y = S q i V f := by
      refine (hx.symm : _ = ofRings.sec (twF q i) V x).trans ?_
      exact (congrArg (ofRings.sec (twF q i) V) hf).symm
    refine LateralTheory.E.L_prim_locPf.loc_mono' (elt_loc q i ((gam ζ).map g.appTop.hom) f) fun W k ⟨c, hc⟩ => ⟨c, ?_⟩
    rw [res_comp, prim_map_comp, hy, hc]
  refine LateralTheory.E.L_prim_locPf.loc_mono' key fun V g ⟨c, hc⟩ => ⟨c.down, ?_⟩
  rw [hc, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have hcv : ((c.down.val : ℕ) : ULift.{1} (ZMod q)) = c := by
    apply ULift.ext
    rw [ULift.down_natCast, ZMod.natCast_zmod_val]
  rw [hcv]

end LateralTheory.E.LocFormPf
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafFibreFieldPf
open AlgebraicGeometry CategoryTheory Topology

namespace LateralTheory.E.LeafFibreFieldPf

open Cardinal IntermediateField in
theorem alg_part (k K : Type) [Field k] [Field K] [Algebra k K] (S : Finset K)
    (hgen : IntermediateField.adjoin k (S : Set K) = ⊤) (d : ℕ) (hd : Algebra.trdeg k K = d + 1) :
    ∃ (F : IntermediateField k K) (s : Finset F) (t : K), s.card ≤ d ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k (s : Set F)) F ∧ Transcendental F t ∧
      FiniteDimensional (IntermediateField.adjoin F {t}) K := by
  classical
  obtain ⟨B, hB⟩ := exists_isTranscendenceBasis k K
  have hcard : #B = ((d + 1 : ℕ) : Cardinal) := by
    rw [hB.cardinalMk_eq_trdeg, hd]; push_cast; rfl
  obtain ⟨T, hTB, hTc⟩ := Cardinal.mk_set_eq_nat_iff_finset.mp hcard
  obtain ⟨a, haT⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
  set T' := T.erase a with hT'
  let F : IntermediateField k K := IntermediateField.adjoin k (T' : Set K)
  let sF : Finset F := T'.attach.image fun x => ⟨x.1, IntermediateField.subset_adjoin k _ x.2⟩
  have hsF : (F.val '' (sF : Set F)) = (T' : Set K) := by
    ext y; simp [sF]; intro h; exact IntermediateField.subset_adjoin k _ (Finset.mem_coe.mpr h)
  refine ⟨F, sF, a, ?_, ?_, ?_, ?_⟩
  · refine (Finset.card_image_le).trans ?_
    rw [Finset.card_attach, Finset.card_erase_of_mem haT, hTc]; simp
  · have hmem : ∀ y : F, y ∈ IntermediateField.adjoin k (sF : Set F) := by
      intro y
      have : (y : K) ∈ (IntermediateField.adjoin k (sF : Set F)).map F.val := by
        rw [IntermediateField.adjoin_map, hsF]; exact y.2
      rw [← SetLike.mem_coe, IntermediateField.coe_map] at this
      obtain ⟨z, hz, hzy⟩ := this
      have : z = y := Subtype.ext hzy
      exact this ▸ hz
    exact ⟨fun y => by
      have := isAlgebraic_algebraMap (R := IntermediateField.adjoin k (sF : Set F)) (A := F) ⟨y, hmem y⟩
      exact this⟩
  · have hind := hB.1
    have hnot : (⟨a, hTB ▸ haT⟩ : B) ∉ {i : B | (i : K) ≠ a} := by simp
    have htr := hind.transcendental_adjoin hnot
    have himg : (Subtype.val '' {i : B | (i : K) ≠ a}) = (T' : Set K) := by
      ext y; simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, exists_and_right,
        exists_eq_right, hT', Finset.coe_erase, Set.mem_diff, Set.mem_singleton_iff, ← hTB]
      tauto
    rw [himg, ← IntermediateField.transcendental_adjoin_iff] at htr
    exact htr
  ·
    set L := IntermediateField.adjoin F {a} with hL
    have hBT : (B : Set K) = (T : Set K) := hTB.symm
    have halgB := hB.isAlgebraic_field
    rw [Subtype.range_coe] at halgB
    set E := IntermediateField.adjoin k B with hE
    have hEL : ∀ x ∈ E, x ∈ L := by
      intro x hx
      have hle : E ≤ L.restrictScalars k := by
        rw [hE, IntermediateField.adjoin_le_iff]
        intro b hb
        rw [← hTB] at hb
        by_cases hba : b = a
        · subst hba; exact IntermediateField.mem_adjoin_simple_self F b
        · have hbF : b ∈ F := IntermediateField.subset_adjoin k _ (by simp [hT', hba, hb])
          exact (IntermediateField.algebraMap_mem L (⟨b, hbF⟩ : F))
      exact hle hx
    let g : E →+* L :=
      { toFun := fun x => ⟨x.1, hEL x.1 x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
        map_zero' := rfl, map_add' := fun _ _ => rfl }
    let _ : Algebra E L := g.toAlgebra
    have : IsScalarTower E L K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hint : ∀ x : K, IsIntegral L x := fun x =>
      ((halgB.isAlgebraic x).extendScalars g.injective).isIntegral
    have hfd := IntermediateField.finiteDimensional_adjoin (K := L) (S := (S : Set K)) (fun x _ => hint x)
    have htop : IntermediateField.adjoin L (S : Set K) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ IntermediateField.adjoin k (S : Set K) := hgen ▸ trivial
      let M : IntermediateField k K :=
        { carrier := (IntermediateField.adjoin L (S : Set K) : Set K)
          mul_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).mul_mem ha hb
          add_mem' := fun ha hb => (IntermediateField.adjoin L (S : Set K)).add_mem ha hb
          inv_mem' := fun _ hx => (IntermediateField.adjoin L (S : Set K)).inv_mem hx
          algebraMap_mem' := fun c => by
            have h1 := IntermediateField.algebraMap_mem (IntermediateField.adjoin L (S : Set K))
              (⟨algebraMap F K (algebraMap k F c), IntermediateField.algebraMap_mem L _⟩ : L)
            rw [IsScalarTower.algebraMap_apply k F K]
            exact h1 }
      have hle : IntermediateField.adjoin k (S : Set K) ≤ M := by
        rw [IntermediateField.adjoin_le_iff]
        intro y hy
        show y ∈ (IntermediateField.adjoin L (S : Set K) : Set K)
        exact IntermediateField.subset_adjoin L _ hy
      exact (hle hx : x ∈ (IntermediateField.adjoin L (S : Set K) : Set K))
    rw [htop] at hfd
    exact LinearEquiv.finiteDimensional (IntermediateField.topEquiv (F := L) (E := K)).toLinearEquiv

theorem gen_top (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ S : Finset (FractionRing A), IntermediateField.adjoin k (S : Set (FractionRing A)) = ⊤ := by
  classical
  obtain ⟨s, hs⟩ := (‹Algebra.FiniteType k A›).out
  refine ⟨s.image (algebraMap A (FractionRing A)), ?_⟩
  have hA : ∀ a : A, algebraMap A (FractionRing A) a ∈
      IntermediateField.adjoin k ((s.image (algebraMap A (FractionRing A)) : Finset _) : Set (FractionRing A)) := by
    intro a
    have ha : a ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have h1 : algebraMap A (FractionRing A) a ∈ (Algebra.adjoin k (s : Set A)).map (IsScalarTower.toAlgHom k A (FractionRing A)) :=
      Subalgebra.mem_map.mpr ⟨a, ha, rfl⟩
    rw [AlgHom.map_adjoin] at h1
    refine IntermediateField.algebra_adjoin_le_adjoin k _ ?_
    simpa [Finset.coe_image] using h1
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  exact div_mem (hA a) (hA b)

theorem dimX_eq (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] (e : ℕ)
    (he : letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
      Algebra.trdeg k X.functionField = e) :
    topologicalKrullDim X = e := by
  have h := GlobalTheory.topologicalKrullDim_eq_of_forall_exists_isOpen (Z := (Set.univ : Set X))
    ⟨genericPoint X, trivial⟩ (d := (e : WithBot ℕ∞)) (fun x _ => by
      obtain ⟨A, _, _, _, _, _, j, _, hx, -, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p x
      refine ⟨Set.range j, j.isOpenEmbedding.isOpen_range, hx, ?_⟩
      rw [Set.inter_univ, GlobalTheory.topologicalKrullDim_eq_of_isEmbedding j.isOpenEmbedding.isEmbedding rfl]
      have hA := GlobalTheory.ringKrullDim_eq_of_trdeg_eq k A (htr.trans he)
      rw [← hA]
      exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A)
  rw [← h]
  exact (GlobalTheory.topologicalKrullDim_eq_of_isEmbedding (e := (id : X → X)) IsEmbedding.id (Set.range_id)).symm

theorem LeafFibreField_of : LateralTheory.E.LeafCurveVCut.LeafFibreField := by
  intro k _ X _ p _ hd
  letI := (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra
  obtain ⟨A, _, _, _, _, _, j, _, hx, hj, htr⟩ := GlobalTheory.exists_affine_chart_trdeg_eq p (genericPoint X)
  obtain ⟨e, -, he2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq k A
  have hdim := dimX_eq k p e (htr.symm.trans he2)
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := by
    cases e with
    | zero => rw [hdim] at hd; simp at hd
    | succ d => exact ⟨d, rfl⟩
  have : Algebra.IsAlgebraic A (FractionRing A) := IsLocalization.isAlgebraic _ (nonZeroDivisors A)
  have htrK : Algebra.trdeg k (FractionRing A) = d + 1 := by
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top k A (FractionRing A), he2]; push_cast; rfl
  obtain ⟨S, hS⟩ := gen_top k A
  obtain ⟨F, s, t, hs, halg, ht, hfin⟩ := alg_part k (FractionRing A) S hS d htrK
  refine ⟨F, inferInstance, inferInstance, FractionRing A, inferInstance, inferInstance, d, s, t,
    Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A))) ≫ j, ?_, hs, halg, ht, hfin, ?_, ?_⟩
  · rw [hdim]; exact_mod_cast Nat.lt_succ_self d
  · rw [Category.assoc, hj, ← Spec.map_comp]
    congr 1
  · obtain ⟨q, hq⟩ := hx
    obtain ⟨pt⟩ : Nonempty (Spec (.of (FractionRing A))) := inferInstance
    refine ⟨pt, ?_⟩
    have hz : (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt ⤳ q := by
      refine (PrimeSpectrum.le_iff_specializes _ _).mp ?_
      show Ideal.comap (algebraMap A (FractionRing A)) pt.asIdeal ≤ q.asIdeal
      have hbot : pt.asIdeal = ⊥ := by
        rcases Ideal.eq_bot_or_top pt.asIdeal with h | h
        · exact h
        · exact absurd h pt.isPrime.ne_top
      intro a ha
      rw [Ideal.mem_comap, hbot, Ideal.mem_bot] at ha
      rw [(IsFractionRing.injective A (FractionRing A)) (ha.trans (map_zero _).symm)]
      exact zero_mem _
    have h1 := hz.map j.continuous
    rw [hq] at h1
    have h2 := (genericPoint_spec X).specializes
      (Set.mem_univ (j ((Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) pt)))
    rw [Scheme.Hom.comp_apply]
    exact (h1.antisymm h2).eq

end LateralTheory.E.LeafFibreFieldPf
end
