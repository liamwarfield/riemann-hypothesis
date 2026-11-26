module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnitNatCastUp
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeSetDescends
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePointIntegralUpToUnitsAnyAlgClosedField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFrameIntAnyField
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HkAnyField

open GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39 GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem pow_eq_one_of_mem {T : Over Xo.X} {C : Subgroup (T ⟶ Xo.univ.t.G)} (hpP : (p : 𝓞 E) ∈ P)
    (hC : Xo.univ.t.HeckeKer T Dw P p i C) {u : T ⟶ Xo.univ.t.G} (hu : u ∈ C) : u ^ p ^ 2 = 1 := by
  refine (GlobalTheory.HeckeKerModel.mem_tors_span Xo.univ.t _ (p ^ 2)).1 fun a ha => hC.2.2.1 hu a ?_
  refine (Ideal.span_singleton_le_iff_mem _).2 ?_ ha
  rw [sq, Nat.cast_mul]
  refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_
  have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
  rwa [map_natCast] at this

theorem exists_isPair (hP : IsHeckePrime H l P p) {Ω : Type} [Field Ω] [IsAlgClosed Ω] {x x' : Sp Ω ⟶ Xo.X}
    {C : Subgroup (Over.mk x ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk x) Dw P p i C)
    {f : Fib Xo x ⟶ Fib Xo x'} {ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)}
    (h : IsHkIsog p x x' C f.left ψp) : ∃ f', IsPair (p ^ 2) f f' := by
  obtain ⟨hP, hco, hp, hpP, hpM⟩ := hP
  obtain ⟨⟨hfin, het, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM hC h
  obtain ⟨-, h0, hf, hact, -, hker, -⟩ := h
  have hL : Out.Laws := abelianSchemeLaws_all.1
  have hA := isAbelianScheme_fib x
  have hB := isAbelianScheme_fib x'
  have := hA.proper
  have := hB.proper
  have := hA.comm
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv x
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv x'
  have hψ : ∀ u, σ (u ≫ f) = ψp (ρ u) := fun u => GlobalTheory.HeckePoint.fibPt_injective _ (by
    rw [s₁, ← hf, e₁]; rfl)
  have one : ∀ (G : Over (Sp Ω)) [GrpObj G], (1 : 𝟙_ (Over (Sp Ω)) ⟶ G) = η[G] := fun G _ => by
    rw [Hom.one_def]; simp
  have hom : IsMonHom f := hL.rigidity _ _ _ hA hB f (by
    rw [← one, ← one]
    exact σ.injective (by rw [hψ, map_one, map_one, map_one]))
  have lin : Lin f := fun a => GlobalTheory.HeckePoint.hom_ext_pts hA.smooth fun u => σ.injective (by
    rw [← Category.assoc, ← Category.assoc, hψ, s₂, hψ, e₂, hact])
  have hkill : ∀ u : 𝟙_ (Over (Sp Ω)) ⟶ Fib Xo x, u ≫ f = 1 → u ^ p ^ 2 = 1 := fun u hu => by
    have hx : ρ u ∈ C := by rw [← hker, MonoidHom.mem_ker, ← hψ, hu, map_one]
    exact ρ.injective (by rw [map_pow, map_one, pow_eq_one_of_mem hpP hC hx])
  have hpow : ∀ m : ℕ, IsMonHom (𝟙 (Fib Xo x) ^ m) := fun m => by
    induction m with
    | zero => rw [pow_zero]; exact inferInstanceAs (IsMonHom (toUnit _ ≫ η[Fib Xo x]))
    | succ m ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 (Fib Xo x) ^ m) (𝟙 _) ≫ μ[Fib Xo x]))
  have := hpow (p ^ 2)
  have : IsFinite f.left := hfin
  have : Etale f.left := het
  have : Surjective f.left := hsur
  obtain ⟨π, hπ⟩ := GlobalTheory.HeckePoint.exists_fac hA.smooth f (𝟙 (Fib Xo x) ^ p ^ 2) fun u hu => by
    rw [MonObj.comp_pow, Category.comp_id, hkill u hu]
  have homπ : IsMonHom π := hL.rigidity _ _ _ hB hA π (by
    rw [← IsMonHom.one_hom f, Category.assoc, hπ, IsMonHom.one_hom])
  have : Epi f.left := Flat.epi_of_flat_of_surjective _
  have : Epi f := Over.epi_of_epi_left f
  refine ⟨π, hom, homπ, hπ, ?_, lin, fun a => ?_⟩
  · rw [← cancel_epi f, ← Category.assoc, hπ, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  · have := Xo.univ.t.act.hom a
    rw [← cancel_epi f, ← Category.assoc, ← lin a, Category.assoc, hπ, ← Category.assoc, hπ, MonObj.pow_comp,
      MonObj.comp_pow, Category.id_comp, Category.comp_id]

section Ext

variable {K L : Type} [Field K] [Field L] (φ : K →+* L)

def down {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} (hw : w = spMap φ ≫ x) : (Over.mk w : Over Xo.X) ⟶ Over.mk x :=
  Over.homMk (spMap φ) hw.symm

def up {x : Sp K ⟶ Xo.X} {w : Sp L ⟶ Xo.X} (hw : w = spMap φ ≫ x) :
    (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk w ⟶ Xo.univ.t.G) :=
  MonoidHom.mk' (fun z => down φ hw ≫ z) fun _ _ => MonObj.comp_mul _ _ _

variable {φ} {x x' : Sp K ⟶ Xo.X} {w w' : Sp L ⟶ Xo.X}

theorem up_injective (hw : w = spMap φ ≫ x) : Function.Injective (up φ hw) := fun _ _ h =>
  TorsionRat.comp_injective φ (down φ hw) rfl h

theorem weilIs_up (hw : w = spMap φ ≫ x) {n : ℤ} {a b : Over.mk x ⟶ Xo.univ.t.G} {v : Kˣ}
    (h : WeilIs Xo.univ.t.G Xo.univ.t.PP.L n a b (unitOn v)) :
    WeilIs Xo.univ.t.G Xo.univ.t.PP.L n (up φ hw a) (up φ hw b) (unitOn (Units.map φ.toMonoidHom v)) := by
  have h₁ := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds (UnivPol.pol Xo).isAb Xo.univ.t.PP.isLB (down φ hw) h
  have e' : Units.map (down φ hw).left.appTop.hom.toMonoidHom (unitOn v) = unitOn (Units.map φ.toMonoidHom v) :=
    Units.ext (congrArg (fun q => q.hom v.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm
  exact e' ▸ h₁

variable [IsAlgClosed K]

theorem exists_weilIs {n : ℕ} (hn : 0 < n) {a b : Over.mk x ⟶ Xo.univ.t.G} (ha : a ^ n = 1) (hb : b ^ n = 1) :
    ∃ v : Kˣ, WeilIs Xo.univ.t.G Xo.univ.t.PP.L n a b (unitOn v) := by
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x (Spec.preimage (x ≫ Xo.s)).hom (Spec.map_preimage _).symm
  obtain ⟨a, rfl⟩ := (I.onto _ hn a).1 ha
  obtain ⟨b, rfl⟩ := (I.onto _ hn b).1 hb
  exact ⟨_, I.isom _ hn a b⟩

variable [IsAlgClosed L]

theorem exists_up (hw : w = spMap φ ≫ x) {n : ℕ} (hn : 0 < n) (u : Over.mk w ⟶ Xo.univ.t.G) (hu : u ^ n = 1) :
    ∃ a, a ^ n = 1 ∧ up φ hw a = u :=
  TorsionRat.exists_eq_comp_of_isAlgClosed Xo hn φ (down φ hw) rfl u hu

theorem heckeKer_down (hw : w = spMap φ ≫ x) (hp : 0 < p) (hpP : (p : 𝓞 E) ∈ P)
    {C : Subgroup (Over.mk w ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk w) Dw P p i C) :
    Xo.univ.t.HeckeKer (Over.mk x) Dw P p i (C.comap (up φ hw)) := by
  refine GlobalTheory.HkSetDesc.heckeKer_comap Dw P p i Xo.univ.t (down φ hw) (up φ hw) (fun _ => rfl) hpP (up_injective hw)
    (fun u hu => (exists_up hw (pow_pos hp 2) u hu).imp fun _ h => h.2) (fun a b ha hb h => ?_) C hC
  obtain ⟨v, hv⟩ := exists_weilIs (pow_pos hp 2) ha hb
  rw [Nat.cast_pow] at hv
  have e := GlobalTheory.weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB L w _ _ _ _ 1 (weilIs_up hw hv)
    (by rw [unitOn, map_one]; exact h)
  obtain rfl : v = 1 := Units.ext (φ.injective ((congrArg Units.val e).trans (map_one φ).symm))
  rwa [unitOn, map_one] at hv

theorem isHkIsog_up (hP : IsHeckePrime H l P p) (hw : w = spMap φ ≫ x)
    {C : Subgroup (Over.mk w ⟶ Xo.univ.t.G)} (hC : Xo.univ.t.HeckeKer (Over.mk w) Dw P p i C)
    {f : Fib Xo x ⟶ Fib Xo x'} {ψp : (Over.mk x ⟶ Xo.univ.t.G) →* (Over.mk x' ⟶ Xo.univ.t.G)}
    (h : IsHkIsog p x x' (C.comap (up φ hw)) f.left ψp) {g : Fib Xo w ⟶ Fib Xo w'} {g' : Fib Xo w' ⟶ Fib Xo w}
    (hg : IsBC φ f g) (hgg : IsPair (p ^ 2) g g') : ∃ χp, IsHkIsog p w w' C g.left χp := by
  obtain ⟨hP, hco, hp, hpP, hpM⟩ := hP
  have hw' := hg.2.1
  obtain ⟨⟨hfin, -, hsur⟩, -⟩ := GlobalTheory.HeckePointLaw.isHkIsog_etale_unique Xo hP hco hp hpP hpM
    (heckeKer_down hw hp.pos hpP hC) h
  obtain ⟨hs, h0, hf, -, -, hker, hweil, hlev⟩ := h
  obtain ⟨π, p₁, p₂, hπ⟩ := PairBC.exists_proj Xo.univ.t.G x w hw
  obtain ⟨π', p₁', p₂', hπ'⟩ := PairBC.exists_proj Xo.univ.t.G x' w' hw'
  have sq := hg.2.2 π π' p₁ p₂ p₁' p₂'
  have cart : IsPullback π g.left f.left π' := by
    refine IsPullback.of_bot ?_ sq.symm hπ'.1
    rw [Over.w g, Over.w f]
    exact hπ.1
  have : IsFinite g.left := MorphismProperty.of_isPullback (P := @IsFinite) cart hfin
  have : Surjective g.left := MorphismProperty.of_isPullback (P := @Surjective) cart hsur
  obtain ⟨ρ, e₁, e₂⟩ := exists_fibPtsEquiv w
  obtain ⟨σ, s₁, s₂⟩ := exists_fibPtsEquiv w'
  have := hgg.1
  have := hgg.2.1
  let m : (𝟙_ (Over (Sp L)) ⟶ Fib Xo w) →* (𝟙_ (Over (Sp L)) ⟶ Fib Xo w') :=
    MonoidHom.mk' (fun z => z ≫ g) fun a b => MonObj.mul_comp a b g
  let χ := σ.toMonoidHom.comp (m.comp ρ.symm.toMonoidHom)
  have hχ : ∀ u, χ (ρ u) = σ (u ≫ g) := fun u => congrArg (fun z => σ (z ≫ g)) (ρ.symm_apply_apply u)
  have hfib : ∀ u, fibPt _ u ≫ g.left = fibPt _ (χ u) := fun u => by
    obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [hχ, e₁, s₁]; rfl
  have hup : ∀ a, fibPt _ (up φ hw a) ≫ π = spMap φ ≫ fibPt _ a := fun a => by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, p₁, fibPt, fibPt, pullback.lift_fst, pullback.lift_fst]; rfl
    · rw [Category.assoc, Category.assoc, p₂, fibPt, fibPt, pullback.lift_snd_assoc, pullback.lift_snd,
        Category.id_comp, Category.comp_id]
  have key : ∀ a, χ (up φ hw a) = up φ hw' (ψp a) := fun a => by
    refine Over.OverMorphism.ext ?_
    have e := congrArg (fun q => fibPt _ (up φ hw a) ≫ q ≫ pullback.fst _ _) sq
    simp only [Category.assoc] at e
    rw [p₁', reassoc_of% (hfib (up φ hw a)), reassoc_of% (hup a), reassoc_of% (hf a), fibPt, fibPt,
      pullback.lift_fst, pullback.lift_fst] at e
    exact e
  have unit : ∀ {y : Sp K ⟶ Xo.X} {y' : Sp L ⟶ Xo.X} (hy : y' = spMap φ ≫ y) (a : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G),
      toUnit _ ≫ a = up φ hy (toUnit _ ≫ a) := fun hy a => by
    show _ = down φ hy ≫ toUnit _ ≫ a
    rw [comp_toUnit_assoc]
  refine ⟨χ, by rw [hw, hw', Category.assoc, Category.assoc, hs], Over.w g, hfib, fun a u => ?_, fun v => ?_,
    Subgroup.ext fun u => ?_, fun n a b v hn hv => ?_, fun p' hp' a => ?_⟩
  · obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [← e₂, hχ, hχ, ← s₂, Category.assoc, Category.assoc, hgg.2.2.2.2.1 a]
  · obtain ⟨v, rfl⟩ := σ.surjective v
    obtain ⟨b, hb⟩ := exists_lift_pt g.left v.left
    let u : 𝟙_ (Over (Sp L)) ⟶ Fib Xo w := Over.homMk b (by rw [← Over.w g, reassoc_of% hb, Over.w v])
    exact ⟨ρ u, (hχ u).trans (congrArg σ (Over.OverMorphism.ext hb))⟩
  · have mem : ∀ a, up φ hw a ∈ χ.ker ↔ up φ hw a ∈ C := fun a => by
      rw [MonoidHom.mem_ker, key, map_eq_one_iff _ (up_injective hw'), ← MonoidHom.mem_ker, hker, Subgroup.mem_comap]
    have tor : u ^ p ^ 2 = 1 → (u ∈ χ.ker ↔ u ∈ C) := fun hu => by
      obtain ⟨a, -, rfl⟩ := exists_up hw (pow_pos hp.pos 2) u hu
      exact mem a
    refine ⟨fun hu => (tor ?_).1 hu, fun hu => (tor (pow_eq_one_of_mem hpP hC hu)).2 hu⟩
    obtain ⟨u, rfl⟩ := ρ.surjective u
    rw [MonoidHom.mem_ker, hχ, map_eq_one_iff _ σ.injective] at hu
    have e := congrArg (u ≫ ·) hgg.2.2.1
    simp only [← Category.assoc, hu, MonObj.one_comp, MonObj.comp_pow, Category.comp_id] at e
    rw [← map_pow, ← e, map_one]
  · have hn0 : 0 < n := Nat.pos_of_ne_zero fun e => hp.one_lt.ne' (by simpa [e] using hn)
    obtain ⟨ta, tb⟩ := GlobalTheory.PairingLawsCompare.mem_tors_of_weilIs (UnivPol.pol Xo) n hv
    obtain ⟨a, ha, rfl⟩ := exists_up hw hn0 a ta
    obtain ⟨b, hb, rfl⟩ := exists_up hw hn0 b tb
    obtain ⟨v₀, hv₀⟩ := exists_weilIs hn0 ha hb
    obtain rfl := GlobalTheory.weilIs_unique_fieldPoint _ _ _ Xo.univ.t.PP.isLB L w _ _ _ _ _ (weilIs_up hw hv₀) hv
    rw [key, key, ← map_pow]
    exact weilIs_up hw' (hweil n a b v₀ hn hv₀)
  · rw [unit hw, unit hw, key, key, (hlev p' hp' a).1, (hlev p' hp' a).2, ← unit, ← unit]
    exact ⟨rfl, rfl⟩

end Ext

theorem exists_hkRelFr_down (hP : IsHeckePrime H l P p) {K L : Type} [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {y : FrPt Xo c K} {w z : FrPt Xo c L}
    (hw : FrMap φ y w) (C : hkKer (Xo := Xo) P p i L w) (hz : hkRelFr P p i (hkTr Xo c p) L w C z) :
    ∃ (C₀ : hkKer (Xo := Xo) P p i K y) (z₀ : FrPt Xo c K), hkRelFr P p i (hkTr Xo c p) K y C₀ z₀ ∧ FrMap φ z₀ z := by
  have hp := hP.2.2.1.pos
  obtain ⟨hT, hU⟩ := GlobalTheory.T.heckeIsogeny_thetaGenerator_transport E H Dw l Xo c P p i hP
  let C₀ : hkKer (Xo := Xo) P p i K y := ⟨_, heckeKer_down hw.1 hp hP.2.2.2.1 C.2⟩
  obtain ⟨z₀, hz₀⟩ := GlobalTheory.HeckePointLaw.exists_hkRelFr hP hT K y C₀
  obtain ⟨z₁, hz₁⟩ := exists_frMap φ z₀
  refine ⟨C₀, z₀, hz₀, ?_⟩
  obtain ⟨ψ, ψp, h, hLie, hTr⟩ := hz₀
  let f : Fib Xo y.x ⟶ Fib Xo z₀.x := Over.homMk ψ h.2.1
  obtain ⟨f', hf⟩ := exists_isPair (f := f) hP C₀.2 h
  obtain ⟨g, hg⟩ := (PairBC.exists_isBC_and_isPair_iff E H Dw l Xo K L φ.toRingHom y.x z₀.x w.x z₁.x).1 hw.1 hz₁.1 f
  obtain ⟨g', hg'⟩ := (PairBC.exists_isBC_and_isPair_iff E H Dw l Xo K L φ.toRingHom z₀.x y.x z₁.x w.x).1 hz₁.1 hw.1 f'
  have e : spMap (algebraMap K K) = 𝟙 (Sp K) := Spec.map_id _
  have hR : AllRat Xo y.x (p ^ 2) := TorsionRat.allRat_of_isAlgClosure Xo (pow_pos hp 2) (F := K) y.x y.x
    (by rw [e, Category.id_comp]) fun a _ => ⟨a, by rw [e, Category.id_comp]⟩
  obtain ⟨a₁, a₂, a₃⟩ := (hkWith_iff φ hp hw hz₁ hg hg' hR).1 ⟨hf, hLie, hTr⟩
  obtain ⟨χ, hχ⟩ := isHkIsog_up (f := f) hP hw.1 C.2 h hg a₁
  rwa [GlobalTheory.HeckePointLaw.hkRelFr_unique hP hU L w C z z₁ hz ⟨g.left, χ, hχ, a₂, a₃⟩]

theorem isIntegralUpToUnits_up {cls : PtClass Xo c} {T : CDVR} {io : c.F →+* T.Fr} {K L : Type} [Field K] [Field L]
    [Algebra c.F K] [Algebra c.F L] (φ : K →ₐ[c.F] L) {k : T.Fr →+* K} {z₀ : FrPt Xo c K} {z : FrPt Xo c L}
    (hz : FrMap φ z₀ z) (h : IsIntegralUpToUnits cls T io k z₀) :
    IsIntegralUpToUnits cls T io (φ.toRingHom.comp k) z := by
  obtain ⟨T', i, hi, j, rfl, y', h₁, h₂, w, u, hw, hb⟩ := h
  letI := (i.comp io).toAlgebra
  obtain ⟨w', hw'⟩ := exists_frMap φ w
  exact ⟨T', i, hi, φ.comp j, rfl, y', h₁, h₂, w', u, frMap_comp hw hw' fun _ => rfl, frBor_map φ hb hw' hz⟩

end GlobalTheory.HkAnyField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePointIntegralUpToUnitsAnyAlgClosedField
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

namespace GlobalTheory.HkAnyFieldOf

theorem heckeFrameInt_anyField_of : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l 𝔓 p → (p : 𝓞 c.F) ∉ la.asIdeal → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω], letI := io.toAlgebra; ∀ k : T.Fr →ₐ[c.F] Ω, ∀ yΩ : FrPt Xo c Ω, FrMap k y.1 yΩ → ∀ (C : hkKer (Xo := Xo) 𝔓 p i Ω yΩ) (z : FrPt Xo c Ω), hkRelFr 𝔓 p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω yΩ C z → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsIntegralUpToUnits (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) T io k.toRingHom z := by
  intro hHI E _ _ _ H Dw l Xo c la 𝔓 p i hP hpla T io e hla y hy Ω _ _ _ k yΩ hyΩ C z hz
  letI : Algebra c.F T.Fr := io.toAlgebra

  letI : Algebra T.Fr Ω := k.toRingHom.toAlgebra
  haveI : IsScalarTower c.F T.Fr Ω := IsScalarTower.of_algebraMap_eq fun a => (k.commutes a).symm
  let k₀ : T.Fr →ₐ[c.F] AlgebraicClosure T.Fr := IsScalarTower.toAlgHom c.F T.Fr (AlgebraicClosure T.Fr)
  let φ₀ : AlgebraicClosure T.Fr →ₐ[T.Fr] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let φ : AlgebraicClosure T.Fr →ₐ[c.F] Ω := φ₀.restrictScalars c.F
  have hφk : ∀ a, φ (k₀ a) = k a := fun a => φ₀.commutes a

  obtain ⟨yK, hyK⟩ := exists_frMap k₀ y.1
  have hKΩ : FrMap φ yK yΩ := frMap_of_comp hyK hyΩ hφk

  obtain ⟨C₀, z₀, hz₀, hz₀z⟩ := GlobalTheory.HkAnyField.exists_hkRelFr_down hP φ hKΩ C hz
  have halg : (letI := k₀.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr (AlgebraicClosure T.Fr)) := by
    have hA : k₀.toRingHom.toAlgebra = AlgebraicClosure.instAlgebra T.Fr :=
      Algebra.algebra_ext _ _ fun _ => rfl
    exact hA ▸ AlgebraicClosure.isAlgebraic T.Fr
  have h₀ := (hHI E H Dw l Xo c).2.1 la 𝔓 p i hP hpla T io e hla y hy trivial (AlgebraicClosure T.Fr) k₀ halg
    yK hyK C₀ z₀ hz₀

  have h₁ := GlobalTheory.HkAnyField.isIntegralUpToUnits_up φ hz₀z h₀
  have hcomp : φ.toRingHom.comp k₀.toRingHom = k.toRingHom := RingHom.ext hφk
  rwa [hcomp] at h₁

end GlobalTheory.HkAnyFieldOf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePointIntegralUpToUnitsAnyAlgClosedFieldStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l 𝔓 p → (p : 𝓞 c.F) ∉ la.asIdeal → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω], letI := io.toAlgebra; ∀ k : T.Fr →ₐ[c.F] Ω, ∀ yΩ : FrPt Xo c Ω, FrMap k y.1 yΩ → ∀ (C : hkKer (Xo := Xo) 𝔓 p i Ω yΩ) (z : FrPt Xo c Ω), hkRelFr 𝔓 p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω yΩ C z → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsIntegralUpToUnits (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) T io k.toRingHom z := by
  first | exact @GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of | exact GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of | (intros; apply GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChange
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori GlobalTheory.HeckeFrCompare GlobalTheory.HeckePointLaw

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeBorelChange

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem isLieImg_comb {Ω : Type} [Field Ω] {x x' : Sp Ω ⟶ Xo.X} {ψ : Gx x ⟶ Gx x'} (hψ : IsLinHom ψ) {p m : ℕ}
    {v v' : Fin m → (Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsLieImg p ψ (v j) (v' j))
    (cf : Fin m → Ω) {w w' : Sp (DualNumber Ω) ⟶ Xo.univ.t.G.left} (htw : IsTanAt x w) (htw' : IsTanAt x' w')
    (hw : IsCombAt x v cf w) (hw' : IsCombAt x' v' cf w') : IsLieImg p ψ w w' := by
  let A : Fin m → (tEps x ⟶ Xo.univ.t.G) := fun j => Over.homMk (v j) (hv j).1.1
  let B : Fin m → (tEps x' ⟶ Xo.univ.t.G) := fun j => Over.homMk (v' j) (hv j).2.1.1
  let W : tEps x ⟶ Xo.univ.t.G := Over.homMk w htw.1
  let W' : tEps x' ⟶ Xo.univ.t.G := Over.homMk w' htw'.1
  have hAB : ∀ j, scaleAt x' (p : Ω) ≫ B j = tanMap hψ (A j) := fun j => by
    obtain ⟨-, -, a, ha, e⟩ := hv j
    have : a = A j := Over.OverMorphism.ext ha
    subst this
    exact Over.OverMorphism.ext e
  have hW : (List.ofFn fun i => scaleAt x (cf i) ≫ A i).prod = W := (isCombAt_iff A cf W).1 hw
  have hW' : (List.ofFn fun i => scaleAt x' (cf i) ≫ B i).prod = W' := (isCombAt_iff B cf W').1 hw'
  let Lc : (tEps x' ⟶ Xo.univ.t.G) →* (tEps x' ⟶ Xo.univ.t.G) :=
    MonoidHom.mk' (fun b => scaleAt x' (p : Ω) ≫ b) fun b b' => MonObj.comp_mul _ _ _
  have key : scaleAt x' (p : Ω) ≫ W' = tanMap hψ W := by
    have e1 : scaleAt x' (p : Ω) ≫ W' = Lc W' := rfl
    rw [e1, ← hW, ← hW', map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    refine congrArg (fun f => (List.ofFn f).prod) (funext fun i => ?_)
    simp only [Function.comp_apply, Lc, MonoidHom.mk'_apply]
    rw [tanMap_scale, ← hAB, ← Category.assoc, ← Category.assoc, scaleAt_comm]
  exact ⟨htw, htw', W, rfl, congrArg (·.left) key⟩

theorem scal_mul'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x (a * b) i = scal x a i * scal x b i := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem scal_one'' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i : (PPx x).ι) : scal x (1 : S) i = 1 := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem secBC_self {Ω : Type} [CommRing Ω] {x : Sp Ω ⟶ Xo.X} {a : Ω} {s s' : LB.Sec (PPx x)}
    (h : GlobalTheory.Frames.SecBC (RingHom.id Ω) a x x s s') : ∀ i, s'.f i = scal x a i * s.f i := by
  obtain ⟨pm, h₁, h₂, h₃⟩ := h
  have e0 : spMap (RingHom.id Ω) = 𝟙 (Sp Ω) := by simp [spMap]
  obtain rfl : pm = 𝟙 _ := gx_ext (h₂.trans (by rw [e0]; simp))
    (h₁.trans (Category.id_comp _).symm)
  intro i
  have e : Scheme.Hom.appLE (𝟙 (Gx x)) ((PPx x).U i) ((PPx x).U i) le_rfl = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)
  have := h₃ i le_rfl
  rw [e] at this
  exact this.symm

end SlopeTestRemainingChoices

theorem hkRelFr_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  intro E _ _ _ H Dw l Xo c P p i hP Ω _ _ _ t w z hb C z' hz
  have hsp : IsSplitOff l P p := hP
  obtain ⟨g, hg0, hgd, hgc⟩ := (GlobalTheory.Frames.frBor_iff_frChg w z t).1 hb
  have hdet : ∀ τ, IsUnit (g τ).det := fun τ =>
    GlobalTheory.Frames.lowerTri_isUnit_det _ (hg0 τ) fun j => by rw [hgd]; exact Units.isUnit _
  have hdet' : ∀ τ, IsUnit ((g τ)⁻¹).det := fun τ => by
    rw [Matrix.det_nonsing_inv]; exact (hdet τ).ringInverse
  obtain ⟨w', hw', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c Ω z' (fun τ => (g τ)⁻¹) (t none)⁻¹ hdet'
  have hdiag : ∀ τ j, (g τ)⁻¹ j j = ((t⁻¹ (some ⟨τ, j⟩) : Ωˣ) : Ω) := fun τ j => by
    have e := GlobalTheory.Frames.lowerTri_mul_diag ((g τ)⁻¹) (g τ) (GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ)) (hg0 τ) j
    rw [Matrix.nonsing_inv_mul _ (hdet τ), Matrix.one_apply_eq, hgd] at e
    rw [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left e.symm
  have hb' : FrBor t⁻¹ z' w' := (GlobalTheory.Frames.frBor_iff_frChg z' w' t⁻¹).2
    ⟨fun τ => (g τ)⁻¹, fun τ => GlobalTheory.Frames.lowerTri_inv _ (hg0 τ) (hdet τ), hdiag, hw'⟩
  have hbw : FrBor t w' z' := by
    simpa using (GlobalTheory.Frames.frBor_calculus E H Dw l Xo c Ω z' w' w').2.2.2 t⁻¹ hb'
  obtain ⟨ψ, hiso, hlie, hth⟩ := (hkPt_iff hsp _ z C.1 z').1 hz
  obtain ⟨hx, hc, hs⟩ := hgc
  obtain ⟨hx', hc', hs'⟩ := hw'
  obtain ⟨zx, zo, zu, ztan, zeig, zbas, zs, zgen⟩ := z
  dsimp only at hx
  subst hx
  obtain ⟨zx', zo', zu', ztan', zeig', zbas', zs', zgen'⟩ := z'
  dsimp only at hx'
  subst hx'
  refine ⟨C, w', (hkPt_iff hsp _ w C.1 w').2 ⟨ψ, hiso, fun τ j => ?_, ?_⟩, hbw⟩
  · have hcomb : IsCombAt w.x (zu τ) ((g τ)⁻¹ j) (w.u τ j) := by
      obtain ⟨a, ha, -⟩ := zbas τ (w.u τ j) (w.tan τ j) (w.eig τ j)
      have h1 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo Ω w.x (w.u τ) (w.tan τ) (zu τ) (g τ).transpose a
        (w.u τ j) (fun k => hc τ k) ha
      have h2 := Formalism.L2.PjFree.isCombAt_single (w.tan τ) j
      have e : (g τ).transpose.mulVec a = Pi.single j 1 :=
        (w.basis τ (w.u τ j) (w.tan τ j) (w.eig τ j)).unique h1 h2
      have ea : a = (g τ)⁻¹ j := by
        have e2 := congrArg ((g τ).transpose⁻¹.mulVec) e
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (by rw [Matrix.det_transpose]; exact hdet τ),
          Matrix.one_mulVec, Matrix.mulVec_single_one] at e2
        rw [e2, ← Matrix.transpose_nonsing_inv]
        ext k
        rfl
      exact ea ▸ ha
    exact isLieImg_comb hiso.2.1 (fun k => hlie τ k) ((g τ)⁻¹ j) (w.tan τ j) (w'.tan τ j) hcomb (hc' τ j)
  · have hth' : GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP ψ p zs zs' := by
      have := hth
      simp only [GlobalTheory.ThetaTrace.hkTr, Equiv.apply_symm_apply] at this
      exact this
    show GlobalTheory.ThetaTrace.IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj w.x w'.x ((conj w.x w'.x).symm ψ)) p w.s w'.s
    rw [Equiv.apply_symm_apply]
    have hs₁ := secBC_self hs
    have hs₂ := secBC_self hs'
    refine GlobalTheory.ThetaTrace.IsThetaTrace.smul hth' (toΓ Ω (((t none)⁻¹ : Ωˣ) : Ω)) (fun k => ?_) (fun k => hs₂ k)
    show w.s.f k = scal w.x (((t none)⁻¹ : Ωˣ) : Ω) k * zs.f k
    rw [hs₁ k, ← _root_.mul_assoc, ← scal_mul'', Units.inv_mul, scal_one'', _root_.one_mul]

end GlobalTheory.HeckeBorelChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientFrameChangeOfTriangularFrameChangeStatement
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l P p → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω] (t : Ix Dw → Ωˣ) (w z : FrPt Xo c Ω), FrBor t w z → ∀ (C : hkKer (Xo := Xo) P p i Ω z) (z' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω z C z' → ∃ (C₀ : hkKer (Xo := Xo) P p i Ω w) (w' : FrPt Xo c Ω), hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω w C₀ w' ∧ FrBor t w' z' := by
  first | exact @GlobalTheory.HeckeBorelChange.hkRelFr_frBor | exact GlobalTheory.HeckeBorelChange.hkRelFr_frBor | (intros; apply GlobalTheory.HeckeBorelChange.hkRelFr_frBor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteField
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeStableAt

theorem heckeStable : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw)
    (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw)
    (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]),
    (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) →
    ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  intro hI D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j k P hk z C
  obtain ⟨hHP, hne⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace D T0 fw.laws i k P hk
  have hP' := GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP
  obtain ⟨z', hz'⟩ := GlobalTheory.HeckePointLaw.heckePointLaws.2.1 D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l
    (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP' (PAt (embC YS iC b)) z.1 C
  obtain ⟨T, io, kk, h, y, u, hy, hu, w, hw, hb⟩ := z.2
  obtain ⟨C₀, w', hw', hb'⟩ := GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change _ _ _ _ _ _ P.asIdeal (charAt P) k hHP _ u w z.1 hb C z' hz'
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h
  have hpla : ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ∉ (placeAt (embC YS iC b)).asIdeal := by
    intro hm
    have hl := natCast_mem_placeAt (embC YS iC b)
    have hcop : Nat.Coprime (charAt P) (D.ntw.l i) :=
      (Nat.coprime_primes (charAt_prime P) (Fact.out : (D.ntw.l i).Prime)).2 hne
    obtain ⟨a, c, hac⟩ : IsCoprime ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ((D.ntw.l i : ℕ) : 𝓞 T0.Q.c.F) :=
      Nat.Coprime.cast hcop
    exact (placeAt (embC YS iC b)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hac ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hl)))
  letI := io.toAlgebra
  have hint := GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField hI D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c
    (placeAt (embC YS iC b)) P.asIdeal (charAt P) k hHP hpla T io e he y hy (PAt (embC YS iC b)) h.alg w hw C₀ w' hw'
  obtain ⟨T', i', hi', j', hj', y', hy', -, w2, u2, hw2, hb2⟩ := hint
  letI := (i'.comp io).toAlgebra
  let jj : T'.Fr →+* ℂ_[D.ntw.l i] := (toCp (embC YS iC b)).comp j'.toRingHom
  have hjj : jj.comp i' = kk := RingHom.ext fun a => congrArg (toCp (embC YS iC b)) (DFunLike.congr_fun hj' a)
  have hR := GlobalTheory.T.isCDVRFractionFieldReadingInCp_finite_extension (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h T' i' hi' jj hjj
  have hRa : hR.alg = j' := AlgHom.ext fun _ => rfl
  let u2' : Ix (T0.Q.Dw ((j : ℕ) + 1)) → (PAt (embC YS iC b))ˣ :=
    fun a => Units.map (j'.toRingHom.comp (algebraMap T'.V T'.Fr)).toMonoidHom (u2 a)
  have hbor := (GlobalTheory.Frames.frBor_calculus _ _ _ _ _ _ _ w2 w' z').2.2.1 u2' u hb2 hb'
  have hunit : ∀ a, ‖toCp (embC YS iC b) (u2' a)‖ = 1 := fun a => by
    have h1 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h2 : ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h3 : jj (algebraMap T'.V T'.Fr (u2 a : T'.V)) * jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    have h5 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ = 1 := by
      refine le_antisymm h1 (by_contra fun hlt => ?_)
      push_neg at hlt
      have : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ * ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ < 1 :=
        (mul_le_of_le_one_right (norm_nonneg _) h2).trans_lt hlt
      exact this.ne h4
    exact h5
  have hnorm : ∀ a, ‖toCp (embC YS iC b) ((u * u2') a)‖ = 1 := fun a => by
    rw [Pi.mul_apply, Units.val_mul, map_mul, norm_mul, hu a, hunit a, one_mul]
  refine ⟨⟨z', T', i'.comp io, jj, hR, y', u * u2', hy', hnorm, w2, hRa ▸ hw2, hbor⟩, hz'⟩

end GlobalTheory.HeckeStableAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteFieldStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_integral_framed_point_complete_field : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw) (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]), (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) → ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  first | exact @GlobalTheory.HeckeStableAt.heckeStable | exact GlobalTheory.HeckeStableAt.heckeStable | (intros; apply GlobalTheory.HeckeStableAt.heckeStable <;> assumption)
end
