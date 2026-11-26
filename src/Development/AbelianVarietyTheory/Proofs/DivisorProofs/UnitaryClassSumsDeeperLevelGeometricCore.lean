module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperUnitaryLevelGaloisActsOnLabels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThetaFourierClassSumsDeeperIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderTermSummable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalTraitsFourierTermsAllLevels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatForcesCongMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.compat_forces_congMod : ∀ (G₁ G Y : Type) [AddCommGroup G₁] [AddCommGroup G] [AddCommGroup Y] (L₁ L K : ℕ), K * L₁ = L → 0 < L → (∀ (n : ℕ) (x : Y), 0 < n → n • x = 0 → x = 0) → ∀ (lab : G₁ →+ G) (yy₁ : G₁ →+ ModN L₁ Y), Function.Surjective yy₁ → ∀ (yy yy' : G →+ ModN L Y), (∀ a μ, yy₁ a = QuotientAddGroup.mk μ → yy (lab a) = QuotientAddGroup.mk (K • μ)) → (∀ a μ, yy₁ a = QuotientAddGroup.mk μ → yy' (lab a) = QuotientAddGroup.mk (K • μ)) → ∀ g : Y →+ Y, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (g μ)) → ∀ x, CongMod L₁ (g x) x := by
  intro G₁ G Y _ _ _ L₁ L K hKL hL htf lab yy₁ hsurj yy yy' h1 h2 g hg x
  obtain ⟨b, hb⟩ := hsurj (QuotientAddGroup.mk x)
  have e1 := h1 b x hb
  have e2 := h2 b x hb
  have e3 := hg (lab b) (K • x) e1
  rw [e2, map_nsmul] at e3
  rw [QuotientAddGroup.eq] at e3
  obtain ⟨w, hw⟩ := e3
  simp only [nsmulAddMonoidHom_apply] at hw
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; omega
    · exact h
  refine ⟨w, ?_⟩
  apply sub_eq_zero.mp
  apply htf K _ hK
  rw [smul_sub, smul_add, smul_smul, hKL, hw]
  abel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliPointCompCompactificationStructure
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ProjOverBase

theorem isProjOver_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (κ : C.o →+* X.o₁), X.uΩ ≫ C.i ≫ C.z = spMap ((algebraMap X.o₁ X.Ω₁).comp κ) → IsProjOver X.M.s := by
  intro E _ _ _ H Dw l Xo cf C X κ h
  have hs : X.M.s ≫ spMap κ = X.π ≫ C.z := by
    refine ext_of_isDominant X.M.pt ?_
    rw [← Category.assoc, X.M.pt_s, ← Category.assoc, X.comp]
    simp only [USetup.uΩ, UCompact.i, Category.assoc] at h ⊢
    rw [h]
    exact (Spec.map_comp (CommRingCat.ofHom κ) (CommRingCat.ofHom (algebraMap X.o₁ X.Ω₁))).symm
  haveI := C.ded
  exact GlobalTheory.FiniteOverProj.isProjOver_of_isFinite_over C.o X.o₁ κ X.M.Z C.Z C.z X.π X.M.s C.proj X.fin inferInstance hs

end GlobalTheory.UPoinc.ProjOverBase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUdeep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UDeepEx

theorem big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := _root_.GlobalTheory.Poinc.GDeep.big_ge g n hn B

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem exists_level (X₁ : USetup C) (K : ℕ) (hK : 0 < K) (hKu : IsUnit (K : X₁.o₁)) :
    ∃ (o₂ Ω₂ : Type) (_ : CommRing o₂) (_ : Field Ω₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (_ : Algebra X₁.Ω₁ Ω₂)
      (κ : X₁.o₁ →+* o₂), FiniteDimensional X₁.Ω₁ Ω₂ ∧ IsGalois X₁.Ω₁ Ω₂ ∧ κ.Finite ∧
      (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) ∧
      ∃ (R : Subalgebra o₂ Ω₂) (h : X₁.S.R →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ X₁.ρ.P.A.left) (ze : o₂ˣ), R.FG ∧
        (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a) ∧ P.g = X₁.ρ.P.g ∧
        IsGrpPullback P.A X₁.ρ.P.A (spMap h) ψ ∧ LBIso P.L (X₁.ρ.P.L.pull ψ) ∧
        Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  haveI : CharZero X₁.Ω₁ := ArithBase.char X₁.o₁
  obtain ⟨Ω₂, _, _, Q, φ, ζ, hfd, hgal, hζ, hg, hpb, hlb, hlev⟩ := GlobalTheory.T.exists_symplecticLevel_genericFibre_galoisExtension X₁.S.R.val.toRingHom X₁.ρ.P K hK
  obtain ⟨o₂, _, _, _, κ, ze, hfin, hcomp, hze⟩ := GlobalTheory.T.exists_arithBase_finite_containing_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hK hζ
  have hKu₂ : IsUnit (K : o₂) := by simpa using hKu.map κ
  have hlev' : Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze))) := by rw [hze]; exact hlev
  obtain ⟨R, h, P, ψ, hR, hfr, hh, hPg, hPpb, hPlb, hPlev⟩ :=
    GlobalTheory.T.levelStructure_genericFibre_spreads_fg_subalgebra X₁.S.R X₁.ρ.P κ Q φ K ze X₁.S.fg X₁.S.frac hfd hcomp hKu₂ hg hpb hlb hlev'
  exact ⟨o₂, Ω₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, κ, hfd, hgal, hfin, hcomp,
    R, h, P, ψ, ze, hR, hfr, hh, hPg, hPpb, hPlb, hPlev⟩

end GlobalTheory.UPoinc.UDeepEx

namespace GlobalTheory.UPoinc.UDeepEx

end GlobalTheory.UPoinc.UDeepEx
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UDeepP

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem isUnit_n (X₁ : USetup C) : IsUnit ((X₁.ρ.n : ℕ) : C.o) := by
  haveI := C.ded
  set n := X₁.ρ.n with hn
  have hdvd : n ∣ X₁.S.r * X₁.S.N := by
    rw [X₁.ρ.N_eq]
    exact Dvd.dvd.mul_left (dvd_pow (dvd_pow_self n (by have := X₁.ρ.two_le; omega)) two_ne_zero) _
  have hu₁ : IsUnit ((n : ℕ) : X₁.o₁) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hdvd) X₁.S.unit
  have hM : IsUnit ((n : ℕ) : Γ(X₁.M.Z, ⊤)) := by
    have := hu₁.map ((X₁.M.s.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of X₁.o₁)).inv.hom)
    simpa only [map_natCast] using this
  let g : X₁.M.Z ⟶ Sp C.o := X₁.π ≫ C.z
  have hD : ∀ y, (n : C.o) ∉ (g y).asIdeal := by
    intro y
    have h1 : g ⁻¹ᵁ (Sp C.o).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C.o)).inv.hom (n : C.o)) = ⊤ := by
      rw [Scheme.preimage_basicOpen]
      apply Scheme.basicOpen_of_isUnit
      have := hM.map (X₁.M.Z.presheaf.map (homOfLE (le_top : g ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
      simpa only [map_natCast] using this
    have h2 : y ∈ g ⁻¹ᵁ (Sp C.o).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C.o)).inv.hom (n : C.o)) := by
      rw [h1]; trivial
    have h3 : g y ∈ (Sp C.o).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C.o)).inv.hom (n : C.o)) := h2
    rw [basicOpen_eq_of_affine] at h3
    exact (PrimeSpectrum.mem_basicOpen _ _).1 h3
  haveI : IsProper C.z := GlobalTheory.ProperFamily.isProper_of_isProjOver C.proj
  haveI := X₁.fin
  have hcl : IsClosed (Set.range g) := by
    have := g.isClosedMap
    simpa [Set.image_univ] using this _ isClosed_univ
  let w : Sp X₁.Ω₁ := IsLocalRing.closedPoint X₁.Ω₁
  have hgen : ∀ a ∈ (g (X₁.M.pt w)).asIdeal, a = 0 := by
    intro a ha
    have e : X₁.M.pt ≫ g = (spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) ≫ spMap C.b := by
      simp only [g, ← Category.assoc, X₁.comp]
      simp only [Category.assoc, UCompact.i, pullback.condition]
    have e2 : g (X₁.M.pt w) = (spMap C.b) ((spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) w) := by
      rw [show g (X₁.M.pt w) = (X₁.M.pt ≫ g) w from rfl, e]; rfl
    rw [e2] at ha
    change C.b a ∈ (((spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) w).asIdeal) at ha
    have hbot : ((spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) w).asIdeal = ⊥ :=
      @Ideal.eq_bot_of_prime _ _ _ ((spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.iF ≫ pullback.snd _ _) w).isPrime
    rw [hbot, Ideal.mem_bot] at ha
    exact C.inj (by rw [ha, map_zero])
  have hall : ∀ P : Sp C.o, P ∈ Set.range g := by
    intro P
    have hsp : g (X₁.M.pt w) ⤳ P := (PrimeSpectrum.le_iff_specializes (g (X₁.M.pt w)) P).1 (fun a ha => by
      rw [hgen a ha]; exact zero_mem _)
    exact hsp.mem_closed hcl ⟨_, rfl⟩
  by_contra hnu
  obtain ⟨m, hm, hnm⟩ := exists_max_ideal_of_mem_nonunits hnu
  obtain ⟨y, hy⟩ := hall ⟨m, hm.isPrime⟩
  exact hD y (by rw [hy]; exact hnm)

theorem moduli_point_comp_compactification_structure {K : Type} [CommRing K] (y : Sp K ⟶ Xo.XF cf) :
    y ≫ C.i ≫ C.z = y ≫ pullback.snd _ _ ≫ spMap C.b := by
  simp only [UCompact.i, Category.assoc, pullback.condition]
  rw [← Category.assoc C.iF, C.iF_over]

theorem exists_fg_over {o₂ o₃ Ω : Type} [CommRing o₂] [CommRing o₃] [Field Ω] [Algebra o₂ Ω] [Algebra o₃ Ω]
    (h₂ : Algebra.FiniteType ℤ o₂) (R : Subalgebra o₂ Ω) (hR : R.FG) :
    ∃ R₃ : Subalgebra o₃ Ω, R₃.FG ∧ ∀ x ∈ R, x ∈ R₃ := by
  obtain ⟨t, ht⟩ := hR
  obtain ⟨s, hs⟩ := h₂.out
  refine ⟨Algebra.adjoin o₃ ((t : Set Ω) ∪ (s.image (algebraMap o₂ Ω) : Set Ω)),
    Subalgebra.fg_def.2 ⟨_, (t.finite_toSet.union (s.image _).finite_toSet), rfl⟩, ?_⟩
  set R₃ := Algebra.adjoin o₃ ((t : Set Ω) ∪ (s.image (algebraMap o₂ Ω) : Set Ω))
  have hb : ∀ a : o₂, algebraMap o₂ Ω a ∈ R₃ := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (s : Set o₂) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin (Or.inr (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap m => simpa using intCast_mem R₃ m
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  intro x hx
  rw [← ht] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (Or.inl hx)
  | algebraMap a => exact hb a
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem exists_rebase {o₂ o₃ Ω : Type} [CommRing o₂] [CommRing o₃] [Field Ω] [Algebra o₂ Ω] [Algebra o₃ Ω]
    [b₂ : ArithBase o₂ Ω] [b₃ : ArithBase o₃ Ω] (R : Subalgebra o₂ Ω) (hR : R.FG) (P : PolAV (Sp R)) (K : ℕ)
    (ze : o₂ˣ) (ze₃ : o₃ˣ) (hz : algebraMap o₃ Ω ze₃ = algebraMap o₂ Ω ze)
    (lev : Out.Level P K (unitOn (Units.map (algebraMap o₂ R : o₂ →* R) ze))) :
    ∃ (R₃ : Subalgebra o₃ Ω) (ι : R →+* R₃) (P₃ : PolAV (Sp R₃)) (φ : P₃.A.left ⟶ P.A.left), R₃.FG ∧
      (∀ x ∈ R, x ∈ R₃) ∧ (∀ a, ((ι a : R₃) : Ω) = a) ∧ P₃.g = P.g ∧ IsGrpPullback P₃.A P.A (spMap ι) φ ∧
      LBIso P₃.L (P.L.pull φ) ∧
      Nonempty (Out.Level P₃ K (unitOn (Units.map (algebraMap o₃ R₃).toMonoidHom ze₃))) := by
  obtain ⟨hL, -⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨R₃, hR₃, hle⟩ := exists_fg_over (o₃ := o₃) b₂.ft R hR
  let ι : R →+* R₃ := R.val.toRingHom.codRestrict R₃ fun x => hle _ x.2
  have hι : Function.Injective ι := fun a b h => Subtype.ext (congrArg Subtype.val h :)
  haveI := b₂.ded
  haveI := b₃.ded
  haveI := (Subalgebra.fg_iff_finiteType R).1 hR
  haveI := (Subalgebra.fg_iff_finiteType R₃).1 hR₃
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing o₂ R
  haveI : IsNoetherianRing R₃ := Algebra.FiniteType.isNoetherianRing o₃ R₃
  obtain ⟨P₃, φ, hg, hpb, hlb⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 ι P
  have e : Units.map ι.toMonoidHom (Units.map (algebraMap o₂ R : o₂ →* R) ze) =
      Units.map (algebraMap o₃ R₃).toMonoidHom ze₃ := Units.ext (Subtype.ext hz.symm)
  have hprim := (SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).1 lev.prim
  obtain ⟨lev₃, -⟩ := exists_level_baseChange hL _ _ _ P P₃ φ hpb (LBIso.symm hlb) hg _ _
    (unitOn (Units.map (algebraMap o₃ R₃).toMonoidHom ze₃)) (by rw [GSetup.map_unitOn', e])
    ((SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).2
      (e ▸ hprim.map_of_injective (f := Units.map ι.toMonoidHom) (Units.map_injective hι))) lev
  exact ⟨R₃, ι, P₃, φ, hR₃, hle, fun _ => rfl, hg, hpb, LBIso.symm hlb, ⟨lev₃⟩⟩

theorem exists_base (X₁ : USetup C) (Ω₂ : Type) [Field Ω₂] [Algebra X₁.Ω₁ Ω₂] (ζ : Ω₂ˣ) (K : ℕ) (hK : 1 ≤ K)
    (hζ : ζ ^ K = 1) :
    ∃ (o₃ : Type) (_ : CommRing o₃) (_ : Algebra o₃ Ω₂) (_ : ArithBase o₃ Ω₂) (κ : C.o →+* o₃) (ze : o₃ˣ), κ.Finite ∧
      algebraMap o₃ Ω₂ ze = ζ ∧
      (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.uΩ) ≫ C.i ≫ C.z = spMap ((algebraMap o₃ Ω₂).comp κ) := by
  haveI := C.ded
  haveI : CharZero X₁.Ω₁ := ArithBase.char X₁.o₁
  haveI : CharZero Ω₂ := charZero_of_injective_algebraMap (algebraMap X₁.Ω₁ Ω₂).injective
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  obtain ⟨β, hβ⟩ := Spec.map_surjective
    ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.uΩ) ≫ pullback.snd _ _ : Sp Ω₂ ⟶ Sp cf.F)
  obtain ⟨o₃, _, _, κ, ze, hded, hκ, hinj, hc, hze⟩ := GSetup.exists_base_root C.o cf.F Ω₂ β.hom ζ K hK hζ
  have hft : Algebra.FiniteType ℤ o₃ := by
    have h₁ : (Int.castRingHom C.o).FiniteType := by
      have := C.ft
      exact RingHom.finiteType_algebraMap.2 this
    have h₂ := RingHom.FiniteType.comp hκ.finiteType h₁
    rw [RingHom.ext_int (κ.comp (Int.castRingHom C.o)) (algebraMap ℤ o₃)] at h₂
    exact RingHom.finiteType_algebraMap.1 h₂
  refine ⟨o₃, _, _, ⟨hded, hft, inferInstance, hinj⟩, κ, ze, hκ, congrArg Units.val hze, ?_⟩
  rw [moduli_point_comp_compactification_structure, ← Category.assoc, ← hβ, hc]
  exact UDeepEx.spMap_comp C.b β.hom

theorem exists_model (X₁ : USetup C) (o₃ Ω₂ : Type) [CommRing o₃] [Field Ω₂] [Algebra o₃ Ω₂] [ArithBase o₃ Ω₂]
    [Algebra X₁.Ω₁ Ω₂] [FiniteDimensional X₁.Ω₁ Ω₂] (κ : C.o →+* o₃) (hκ : κ.Finite)
    (hc : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.uΩ) ≫ C.i ≫ C.z = spMap ((algebraMap o₃ Ω₂).comp κ)) :
    ∃ (M : RatModel o₃ Ω₂) (q : M.Z ⟶ X₁.M.Z), GlobalTheory.IsNormalScheme M.Z ∧ IsFinite q ∧
      M.pt ≫ q = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt := by
  haveI := C.ded
  haveI : IsProper C.z := GlobalTheory.ProperFamily.isProper_of_isProjOver C.proj
  haveI := X₁.fin
  have hp : (spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt) ≫ X₁.π ≫ C.z = spMap ((algebraMap o₃ Ω₂).comp κ) := by
    rw [← hc, Category.assoc, ← Category.assoc X₁.M.pt, X₁.comp]
    simp only [Category.assoc]
  have hst : ((spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.M.pt).stalkMap (genericPoint (Sp Ω₂))).hom.Finite := by
    rw [Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp (stalkMap_spMap_finite _ (RingHom.finite_algebraMap.2 inferInstance) _)
      (RingHom.Finite.of_surjective _ (RatModel.stalkMap_pt_surjective X₁.M _))
  obtain ⟨M, q, hn, hq, hpt⟩ := exists_ratModel_normalization C.o o₃ Ω₂ κ hκ X₁.M.Z (X₁.π ≫ C.z) inferInstance
    inferInstance inferInstance _ hp hst
  exact ⟨M, q, GlobalTheory.IsNormalScheme.of_pred hn, hq, hpt⟩

theorem exists_udeep_proj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q →
    ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (m₀ : ℕ),
      ∃ D : UDeep X₁, m₀ ≤ D.m ∧ IsProjOver D.X.M.s := by
  intro E _ _ _ H Dw _ l Xo cf C X₁ m₀
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hℓp : X₁.ρ.n.Prime := X₁.ρ.n_prime
  have hℓ2 : 2 ≤ X₁.ρ.n := hℓp.two_le
  obtain ⟨j₁, hj₁, hr⟩ := X₁.ρ.r_eq
  have hL₁ : X₁.S.r * X₁.S.N = X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := by
    rw [hr, X₁.ρ.N_eq, ← pow_mul, ← pow_add, mul_comm X₁.ρ.k 2]
  obtain ⟨k, j, hk, hB, hj, big⟩ :=
    UDeepEx.big_ge X₁.ρ.P.g X₁.ρ.n hℓ2 ((X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) * max m₀ 1) ^ 2)
  have hun1 : IsUnit (X₁.ρ.n : X₁.o₁) := by
    have hd : X₁.ρ.n ∣ X₁.S.r * X₁.S.N := by
      rw [hL₁]; exact dvd_pow_self _ (by omega)
    exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) X₁.S.unit
  have hunK : IsUnit ((((X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 : ℕ)) : X₁.o₁) := by
    push_cast
    exact ((hun1.pow _).mul ((hun1.pow _).pow _)).pow _
  have hKpos : 0 < (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 := by have := hℓp.pos; positivity
  obtain ⟨o₁, Ω₂, _, _, _, _, _, -, fd, gal, -, -, R₀, h₀, P₀, ψ₀, ze₀, hfg₀, hfr₀, hh₀, hPg₀, hpb₀, hlb₀, ⟨lev₀⟩⟩ :=
    UDeepEx.exists_level X₁ _ hKpos hunK
  have hζ : Units.map (algebraMap o₁ Ω₂).toMonoidHom ze₀ ^ (X₁.ρ.n ^ j * (X₁.ρ.n ^ k) ^ 2) ^ 2 = 1 := by
    have h₁ := ((SymLevelDescent.isPrimitiveRoot_unitOn_iff _ _).1 lev₀.prim).pow_eq_one
    have h₂ := congrArg (Units.map R₀.val.toRingHom.toMonoidHom) h₁
    rw [map_pow, map_one] at h₂
    exact h₂
  obtain ⟨o₂, _, _, _, κ, ze, hκ, hze, hc⟩ := exists_base X₁ Ω₂ _ _ hKpos hζ
  obtain ⟨R, ι, P, φ₀, hfg, hle₀, hι, hPg₁, hpb₁, hlb₁, ⟨lev⟩⟩ := exists_rebase R₀ hfg₀ P₀ _ ze₀ ze hze lev₀
  have hfr : ∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b := fun x =>
    let ⟨a, ha, b, hb, e⟩ := hfr₀ x
    ⟨a, hle₀ a ha, b, hle₀ b hb, e⟩
  let h : X₁.S.R →+* R := ι.comp h₀
  have hh : ∀ a, ((h a : R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => (hι _).trans (hh₀ a)
  have hPg : P.g = X₁.ρ.P.g := hPg₁.trans hPg₀
  let ψ := φ₀ ≫ ψ₀
  have hpb : IsGrpPullback P.A X₁.ρ.P.A (spMap h) ψ := by
    rw [← UDeepEx.spMap_comp]
    exact hpb₁.comp hpb₀
  have hlb : LBIso P.L (X₁.ρ.P.L.pull ψ) :=
    LBIso.trans P.isLB (pull_isLB P₀.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₁ (UDeepEx.lbIso_pull_comp hlb₀ φ₀ rfl)
  clear_value h ψ
  have hS := GlobalTheory.Poinc.hypS_polAV_pullback X₁.ρ.P P (spMap h) ψ hpb hlb X₁.ρ.hypS
  have hun2 : IsUnit (X₁.ρ.n : o₂) := by simpa using (isUnit_n X₁).map κ
  obtain ⟨S₂, ρ₂, hR, φ, -, hN₂, hr₂, hg₂, hpb₂, hlb₂, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o₂ Ω₂ R hfg hfr P X₁.ρ.n k j ze hℓp X₁.ρ.n_odd hk hj hun2 hS lev
  set h' : X₁.S.R →+* S₂.R := (Subalgebra.inclusion hR).toRingHom.comp h with hh'
  have hval : ∀ a, ((h' a : S₂.R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a := fun a => hh a
  have hpb' : IsGrpPullback ρ₂.P.A X₁.ρ.P.A (spMap h') (φ ≫ ψ) := by
    rw [hh', ← UDeepEx.spMap_comp]
    exact hpb₂.comp hpb
  have hlb' : LBIso ρ₂.P.L (X₁.ρ.P.L.pull (φ ≫ ψ)) :=
    LBIso.trans ρ₂.P.isLB (pull_isLB P.isLB _) (pull_isLB X₁.ρ.P.isLB _) hlb₂ (UDeepEx.lbIso_pull_comp hlb φ rfl)

  have hsub : ∀ x : ratHull X₁.S.R, algebraMap X₁.Ω₁ Ω₂ x ∈ ratHull S₂.R := by
    rintro ⟨x, hx⟩
    obtain ⟨n, hn, hnx⟩ := mem_ratHull.1 hx
    refine mem_ratHull.2 ⟨n, hn, ?_⟩
    have e : (n : Ω₂) * algebraMap X₁.Ω₁ Ω₂ x = ((h' ⟨_, hnx⟩ : S₂.R) : Ω₂) := by
      rw [hval]; simp
    rw [e]; exact (h' ⟨_, hnx⟩).2
  let τ : ratHull X₁.S.R →+* ratHull S₂.R :=
    ((algebraMap X₁.Ω₁ Ω₂).comp (ratHull X₁.S.R).val.toRingHom).codRestrict _ hsub
  have hτ : (toRat S₂.R).comp h' = τ.comp (toRat X₁.S.R) := by
    ext a
    exact hval a
  have key : spMap (ratHull S₂.R).val.toRingHom ≫ spMap τ =
      spMap (algebraMap X₁.Ω₁ Ω₂) ≫ spMap (ratHull X₁.S.R).val.toRingHom := by
    rw [UDeepEx.spMap_comp, UDeepEx.spMap_comp]
    rfl
  have hpulled : UOver Xo cf ρ₂.P (toRat S₂.R) (spMap τ ≫ X₁.u) := by
    rw [uOver_baseChange_iff hpb' hlb', hτ]
    exact X₁.pulled.comp τ
  have hpt : spMap (ratHull S₂.R).val.toRingHom ≫ spMap τ ≫ X₁.u = spMap (algebraMap X₁.Ω₁ Ω₂) ≫ X₁.uΩ := by
    rw [← Category.assoc, key, Category.assoc]
  have hgen : ∀ w, (spMap (ratHull S₂.R).val.toRingHom ≫ spMap τ ≫ X₁.u) w ∈ genericPoints (Xo.XF cf) := by
    intro w
    rw [hpt, Scheme.Hom.comp_apply]
    exact X₁.gen _
  obtain ⟨M₂, q, hMn, hq, hqgen⟩ := exists_model X₁ o₂ Ω₂ κ hκ hc
  haveI := hq
  haveI := X₁.fin
  have hcomp : M₂.pt ≫ q ≫ X₁.π = spMap (ratHull S₂.R).val.toRingHom ≫ (spMap τ ≫ X₁.u) ≫ C.i := by
    rw [← Category.assoc, hqgen, Category.assoc, X₁.comp, ← Category.assoc (spMap (algebraMap X₁.Ω₁ Ω₂)), ← key]
    simp only [Category.assoc]
  have hbig : S₂.Big := big j le_rfl o₂ Ω₂ S₂ (hg₂.trans hPg) hN₂ hr₂
  let X₂ : USetup C := USetup.mk o₂ Ω₂ S₂ ρ₂ hbig (spMap τ ≫ X₁.u) hpulled hgen M₂ hMn (q ≫ X₁.π) inferInstance hcomp
  have hle : X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) * max m₀ 1 ≤ X₁.ρ.n ^ k :=
    (Nat.pow_le_pow_iff_left two_ne_zero).1 hB
  have hpos : 1 ≤ X₁.ρ.n ^ (j₁ + 2 * X₁.ρ.k) := Nat.one_le_pow _ _ (by omega)
  have hm₁ : 1 ≤ max m₀ 1 := le_max_right _ _
  have hm₀ : m₀ ≤ X₁.ρ.n ^ k :=
    (le_max_left m₀ 1).trans ((Nat.le_mul_of_pos_left _ (by omega)).trans hle)
  have hdm : X₁.S.r * X₁.S.N ∣ X₁.ρ.n ^ k := by
    rw [hL₁]
    refine pow_dvd_pow _ ((Nat.pow_le_pow_iff_right hℓ2).1 ?_)
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans hle
  have hd₂ : X₁.S.r * X₁.S.N ∣ S₂.r * S₂.N := by
    rw [hN₂]
    exact (hdm.trans (dvd_pow_self _ two_ne_zero)).trans (dvd_mul_left _ _)
  obtain ⟨lab, hsame, hrange⟩ :=
    GlobalTheory.T.exists_thetaLabel_common_generic_fibre_pullback X₁.S S₂ X₁.ρ ρ₂ (fun _ => 𝟙 _) (fun _ => 𝟙 _) (algebraMap X₁.Ω₁ Ω₂) h' (φ ≫ ψ) hval hpb' hlb'
      (fun _ => by simp) hd₂
  have hsame' : USame X₁.ρ ρ₂ lab (algebraMap X₁.Ω₁ Ω₂) := by
    obtain ⟨P₀, a, a', -, h₁, h₂, h₃, h₄, -, h₅⟩ := hsame
    exact ⟨P₀, a, a', h₁, h₂, h₃, h₄, h₅⟩
  have hproj : IsProjOver X₂.M.s :=
    GlobalTheory.UPoinc.ProjOverBase.isProjOver_model E H Dw l Xo cf C X₂ κ ((congrArg (· ≫ C.i ≫ C.z) hpt).trans hc)
  exact ⟨UDeep.mk (X := X₂) fd gal hpt q hq hqgen rfl (X₁.ρ.n ^ k) hN₂ hdm lab hsame' hrange, hm₀, hproj⟩

end GlobalTheory.UPoinc.UDeepP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntClosureAutExtends
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem intClosure_aut_extends : ∀ (o₁ Ω₁ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (Ω₂ : Type) [Field Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (z₁ : M₁.Z), letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ σ : (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[M₁.Z.presheaf.stalk z₁] (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂), ∃ σ' : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, σ' (b : Ω₂) = ((σ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂) : Ω₂) := by
  intro o₁ Ω₁ _ _ _ Ω₂ _ _ _ M₁ z₁ σ
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₁ := (M₁.stalkHom z₁).toAlgebra
  haveI : IsDomain (M₁.Z.presheaf.stalk z₁) := (M₁.stalkHom_injective z₁).isDomain _
  haveI : FaithfulSMul (M₁.Z.presheaf.stalk z₁) Ω₁ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M₁.stalkHom_injective z₁)
  haveI : IsFractionRing (M₁.Z.presheaf.stalk z₁) Ω₁ := by
    refine IsFractionRing.of_field _ _ fun x => ?_
    obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M₁.O z₁) x
    refine ⟨(M₁.stalkEquiv z₁).symm a, (M₁.stalkEquiv z₁).symm b, ?_⟩
    have h : ∀ c : M₁.O z₁, algebraMap (M₁.Z.presheaf.stalk z₁) Ω₁ ((M₁.stalkEquiv z₁).symm c) = c := fun c => by
      change M₁.stalkHom z₁ _ = _
      rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    rw [h, h, ← hx]
    rfl
  haveI : IsScalarTower (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.IsAlgebraic Ω₁ Ω₂ := inferInstance
  refine ⟨(galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ, fun b => ?_⟩
  have := algebraMap_galRestrict_apply (M₁.Z.presheaf.stalk z₁)
    ((galRestrict (M₁.Z.presheaf.stalk z₁) Ω₁ Ω₂ (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)).symm σ) b
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassLimitNormLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem class_limit_norm_le : ∀ (p : ℕ) [Fact p.Prime] (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (e : X ≃+ Y) (β : LinearMap.BilinForm ℤ X) (be : LinearMap.BilinForm ℤ Y) (sc sc' : ℝ), 0 < sc → (∀ a b, sc * (β a b : ℝ) = sc' * (be (e a) (e b) : ℝ)) → ∀ (m : ℕ) (t : Y → PadicAlgCl p), (∀ μ, ‖t μ‖ ≤ Real.exp (-(sc' * (be μ μ : ℝ) / 2))) → ∀ (v : PadicAlgCl p) (ν : Y), (∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ μ ∈ S, CongMod m μ ν) → (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ) → ∀ μ : X, CongMod m (e μ) ν → (∀ μ' : X, CongMod m μ' μ → β μ μ ≤ β μ' μ') → ‖v‖ ≤ Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
  intro p _ X Y _ _ e β be sc sc' hsc hid m t ht v ν hv μ hμν hmin
  set R := Real.exp (-(sc * (β μ μ : ℝ)) / 2) with hR
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hterm : ∀ μ' : Y, CongMod m μ' ν → ‖t μ'‖ ≤ R := by
    intro μ' h'
    obtain ⟨w1, hw1⟩ := h'
    obtain ⟨w2, hw2⟩ := hμν
    have hc : CongMod m (e.symm μ') μ := by
      refine ⟨e.symm (w1 - w2), ?_⟩
      have : μ' = e μ + m • (w1 - w2) := by rw [hw1, hw2, smul_sub]; abel
      rw [this, map_add (f := _), map_nsmul, AddEquiv.symm_apply_apply]
    have hle := hmin _ hc
    have hle' : sc * (β μ μ : ℝ) ≤ sc' * (be μ' μ' : ℝ) := by
      have h2 := hid (e.symm μ') (e.symm μ')
      rw [AddEquiv.apply_symm_apply] at h2
      rw [← h2]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hsc.le
    refine (ht μ').trans ?_
    rw [hR]
    apply Real.exp_le_exp.mpr
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨S₀, hS₀⟩ := hv δ hδ
  have h1 := hS₀ (S₀.filter (fun x => CongMod m x ν)) (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx hc => Finset.mem_filter.mpr ⟨hx, hc⟩)
  have h2 : ‖∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ ≤ R :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun x hx => hterm x (Finset.mem_filter.mp hx).2
  calc ‖v‖ = ‖(v - ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x) + ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖v - ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ + ‖∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ := norm_add_le _ _
    _ ≤ R + δ := by linarith

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CPtEqOfNormValLtOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ z₁ : M₁.Z, letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra; ∀ (𝔷 : Ideal (integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂)), 𝔷.IsMaximal → ∀ z₂ : M₂.Z, q z₂ = z₁ → (∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, b ∈ 𝔷 ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M₂.Z), q (y (cPt p)) = z₁ → (∀ b ∈ 𝔷, ‖M₂.val (gPt p ≫ y) (b : Ω₂)‖ < 1) → y (cPt p) = z₂ := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hN hF hg z₁
  letI : Algebra (M₁.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap Ω₁ Ω₂).comp (M₁.stalkHom z₁)).toAlgebra
  intro 𝔷 h𝔷 z₂ hz₂ hmem p _ y hy hsmall
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre o₁ Ω₁ o₂ Ω₂ M₁ M₂ q hN hF hg z₁
  have hO : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂, (b : Ω₂) ∈ M₂.O (y (cPt p)) :=
    fun b => (h1 b).1 b.2 _ hy
  let ι : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂ →+* M₂.O (y (cPt p)) :=
    (RingHom.id Ω₂).restrict _ _ fun c hc => hO ⟨c, hc⟩
  have hle : 𝔷 ≤ (IsLocalRing.maximalIdeal (M₂.O (y (cPt p)))).comap ι := by
    intro b hb
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (RatModel.norm_val_lt_one_iff rfl (hO b)).1 (hsmall b hb)
  have heq := h𝔷.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hle
  have key : ∀ b : integralClosure (M₁.Z.presheaf.stalk z₁) Ω₂,
      ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O z₂) ↔ ((b : Ω₂) = 0 ∨ (b : Ω₂)⁻¹ ∉ M₂.O (y (cPt p))) := by
    intro b
    rw [← hmem b, heq, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, RatModel.isUnit_O_iff]
    show ¬ ((b : Ω₂) ≠ 0 ∧ (b : Ω₂)⁻¹ ∈ M₂.O (y (cPt p))) ↔ _
    tauto
  refine (h3 z₂ (y (cPt p)) hz₂ hy fun b => ?_).symm
  by_cases hb0 : (b : Ω₂) = 0
  · rw [hb0, inv_zero]
    exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  · have := key b
    simp only [hb0, false_or] at this
    exact not_iff_not.1 this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTie
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem UDeep.exists_tie (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (_hpq : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf)
    (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) : ∃ w₂ : UWit D.X, D.Comparison₂ w₁ w₂ := by
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hpt⟩ := D.same
  have e : spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) := by
    rw [← Spec.map_comp]; rfl
  have w : a ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [Category.assoc, e]; exact ha.1.w
  have e₁ := w₁.hα.1.lift_fst _ _ w
  let m : P₀.A.left ⟶ w₁.G.left := w₁.hα.1.lift _ _ w
  have hm : IsGrpPullback P₀.A w₁.G (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m :=
    w₁.hα.cancel (ha.congr e.symm e₁.symm) (w₁.hα.1.lift_snd _ _ w)
  have hβ : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (m ≫ w₁.β) :=
    (hm.comp w₁.hβ).congr (by rw [D.pt]; simp only [USetup.uΩ, Category.assoc]) rfl
  have hLβ : LBIso (D.X.ρ.P.L.pull a') (Xo.univ.t.PP.L.pull (m ≫ w₁.β)) :=
    LBIso.trans (pull_isLB D.X.ρ.P.isLB _) P₀.isLB (pull_isLB Xo.univ.t.PP.isLB _) hL'.symm
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL
        (GenSpread.lbIso_pull_comp m e₁.symm rfl w₁.hL))
  refine ⟨{ G := P₀.A, α := a', β := m ≫ w₁.β, hα := ha', hβ := hβ, hL := hLβ }, m, hm, rfl, fun x => ?_⟩
  obtain ⟨v, hv, hv'⟩ := hpt x
  refine ⟨v, ?_, hv'⟩
  show v ≫ m ≫ w₁.α = _
  rw [e₁, hv, ← Category.assoc, e]

end GlobalTheory.UPoinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumNormEqOfUniqueLeast
open GlobalTheory.Poinc
open Classical

namespace GlobalTheory.UPoinc

theorem classSum_norm_eq_of_unique_least : ∀ (p : ℕ) [Fact p.Prime] (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (e : X ≃+ Y) (β : LinearMap.BilinForm ℤ X) (be : LinearMap.BilinForm ℤ Y) (sc sc' : ℝ), 0 < sc → (∀ a b, sc * (β a b : ℝ) = sc' * (be (e a) (e b) : ℝ)) → ∀ (m : ℕ) (t : Y → PadicAlgCl p), (∀ μ, ‖t μ‖ ≤ Real.exp (-(sc' * (be μ μ : ℝ) / 2))) → ∀ (v : PadicAlgCl p) (ν : Y), (∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ μ ∈ S, CongMod m μ ν) → (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ) → ∀ μ : X, CongMod m (e μ) ν → ‖t (e μ)‖ = Real.exp (-(sc' * (be (e μ) (e μ) : ℝ) / 2)) → (∀ μ' : X, CongMod m μ' μ → μ' ≠ μ → β μ μ < β μ' μ') → ‖v‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
  intro p _ X Y _ _ e β be sc sc' hsc hid m t ht v ν hv μ hμν htμ hmin
  have hR' : ‖t (e μ)‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
    rw [htμ, hid μ μ]; congr 1; ring
  have hlt1 : Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) < Real.exp (-(sc * (β μ μ : ℝ)) / 2) :=
    Real.exp_lt_exp.2 (by nlinarith)
  have hbound : ∀ y : Y, CongMod m y ν → y ≠ e μ →
      ‖t y‖ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := by
    intro y h1 h2
    obtain ⟨w1, hw1⟩ := h1
    obtain ⟨w2, hw2⟩ := hμν
    have hx : CongMod m (e.symm y) μ := by
      refine ⟨e.symm (w1 - w2), ?_⟩
      apply e.injective
      rw [e.apply_symm_apply, map_add (f := _), map_nsmul, e.apply_symm_apply, hw1, hw2, smul_sub]
      abel
    have hne : e.symm y ≠ μ := by
      intro h; apply h2; rw [← h, e.apply_symm_apply]
    have hlt := Int.add_one_le_of_lt (hmin (e.symm y) hx hne)
    have hle : (β μ μ : ℝ) + 1 ≤ (β (e.symm y) (e.symm y) : ℝ) := by exact_mod_cast hlt
    calc ‖t y‖ ≤ Real.exp (-(sc' * (be y y : ℝ) / 2)) := ht y
      _ = Real.exp (-(sc * (β (e.symm y) (e.symm y) : ℝ)) / 2) := by
          have h3 := hid (e.symm y) (e.symm y)
          rw [e.apply_symm_apply] at h3
          rw [h3]; congr 1; ring
      _ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := Real.exp_le_exp.2 (by nlinarith)
  have hRpos : 0 < Real.exp (-(sc * (β μ μ : ℝ)) / 2) := Real.exp_pos _
  obtain ⟨S₀, hS₀⟩ := hv (Real.exp (-(sc * (β μ μ : ℝ)) / 2) / 2) (by positivity)
  have hSc : ∀ x ∈ insert (e μ) (S₀.filter (fun x => CongMod m x ν)), CongMod m x ν := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hμν
    · exact (Finset.mem_filter.1 hx).2
  have hclose := hS₀ (insert (e μ) (S₀.filter (fun x => CongMod m x ν))) hSc
    (fun x hx hc => Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hx, hc⟩))
  set S := insert (e μ) (S₀.filter (fun x => CongMod m x ν)) with hSdef
  have hsum : ∑ x ∈ S, t x = t (e μ) + ∑ x ∈ S.erase (e μ), t x :=
    (Finset.add_sum_erase S t (Finset.mem_insert_self _ _)).symm
  have hrest : ‖∑ x ∈ S.erase (e μ), t x‖ ≤ Real.exp (-(sc * ((β μ μ : ℝ) + 1)) / 2) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.exp_pos _).le
    intro x hx
    exact hbound x (hSc x (Finset.mem_of_mem_erase hx)) (Finset.ne_of_mem_erase hx)
  have hnS : ‖∑ x ∈ S, t x‖ = Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
    rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hR']; linarith), hR']
    exact max_eq_left (by linarith)
  have hv' : v = (v - ∑ x ∈ S, t x) + ∑ x ∈ S, t x := by abel
  rw [hv', IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hnS]; linarith), hnS]
  exact max_eq_right (by linarith)

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdDetSubOneOfCongModThreeLe
open GlobalTheory.Poinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L N : ℕ) (hL : 3 ≤ L)
    (γ : X ≃ₗ[ℤ] X) (hγ : ∀ x, CongMod L (γ x) x) : (N : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
  set b := Module.Free.chooseBasis ℤ X
  have hdet : LinearMap.det (γ : X →ₗ[ℤ] X) = (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)).det :=
    (LinearMap.det_toMatrix b _).symm
  have hmap : (Int.castRingHom (ZMod L)).mapMatrix (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)) = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hγ (b j)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hw,
      map_add, map_nsmul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Matrix.one_apply]
    rw [Finsupp.single_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, add_zero]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcast : ((LinearMap.det (γ : X →ₗ[ℤ] X) : ℤ) : ZMod L) = 1 := by
    rw [hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod L)) (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X))
    simp only [eq_intCast] at this
    rw [this, hmap, Matrix.det_one]
  have hdvd : (L : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast, sub_self]
  rcases Int.isUnit_iff.mp (LinearEquiv.isUnit_det' γ) with h | h
  · rw [h, sub_self]; exact dvd_zero _
  · exfalso
    rw [h] at hdvd
    have h2 : (L : ℤ) ∣ 2 := by
      have : (2 : ℤ) = -(-1 - 1) := by norm_num
      rw [this]; exact (dvd_neg).2 hdvd
    have : L ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCore
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UCore

theorem qW_one {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (μ : Fin 1 → X) :
    qW !![(1 : ℤ)] β μ = β (μ 0) (μ 0) := by
  simp [qW]

theorem classSums_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ p _ z₁ Φ hΦ y₀ N₀
  choose ct hct using hΦ
  have hev : ∀ y a, Φ.ev y a = (ct y).val a := fun y => (hct y).1
  choose e he using fun y => (hct y).2
  obtain ⟨D, hD, hproj⟩ := GlobalTheory.UPoinc.UDeepP.exists_udeep_proj E H Dw hpq l Xo cf C X₁ N₀
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun x => ⟨D.X.normal.isDomain_stalk x, D.X.normal.isIntegrallyClosed_stalk x⟩
  obtain ⟨w₁⟩ := nonempty_uWit X₁
  obtain ⟨w₂, htie⟩ := GlobalTheory.UPoinc.UDeep.exists_tie E H Dw hpq l Xo cf C X₁ D w₁
  refine ⟨D.m, hD, D.dvd, D.X.Ω₁, inferInstance, D.alg, D.fd, D.gal, ?_⟩
  intro 𝔷 h𝔷 ev' hev' hle hlt
  obtain ⟨hB, hmax, -, hlift⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q
    hN D.fin D.gen z₁
  obtain ⟨z₂, hz₂, h𝔷z⟩ := hmax 𝔷 h𝔷
  haveI := D.fd
  haveI := D.gal
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have hl : ∀ y, ∃ y₂ : Sp (OO p) ⟶ D.X.M.Z, y₂ ≫ D.q = (ct y).y ∧
      ∀ b, ev' y b = D.X.M.val (gPt p ≫ y₂) (b : D.X.Ω₁) :=
    fun y => hlift p (ct y).y (ct y).cen (ev' y) (fun a => by rw [hev', hev]; rfl)
  choose y₂ hq hval using hl
  have hcen : ∀ y, y₂ y (cPt p) = z₂ := by
    intro y
    refine GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q hN D.fin D.gen z₁ 𝔷 h𝔷 z₂ hz₂ h𝔷z p (y₂ y) ?_ ?_
    · rw [← Scheme.Hom.comp_apply, hq]; exact (ct y).cen
    · intro b hb; rw [← hval]; exact hlt y b hb
  let ct₂ : ∀ y, UCTrait D.X p z₂ := fun y => { D.lift (ct y) (y₂ y) (hq y) with cen := hcen y }
  choose yy₁ hyy₁ using fun y => GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ (ct y)
  choose yy hyy hcomp using fun y => GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ (ct y) (yy₁ y) (hyy₁ y) (y₂ y) (hq y)
  have hyy₂ : ∀ y, UIsLabW D.X w₂ (ct₂ y) (yy y) := fun y => hyy y
  choose d hd using fun y => GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ (ct₂ y₀) (ct₂ y) (yy y₀) (yy y) (hyy₂ y₀) (hyy₂ y)
  let k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y := fun y =>
    if h : y = y₀ then (by subst h; exact LinearEquiv.refl _ _) else (e y₀).trans ((d y).trans (e y).symm)
  have hk0 : k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) := by simp [k]
  have hk : ∀ y a x, yy y₀ a = QuotientAddGroup.mk (e y₀ x) → yy y a = QuotientAddGroup.mk (e y (k y x)) := by
    intro y a x hax
    by_cases h : y = y₀
    · subst h; simpa [hk0] using hax
    · simp only [k, dif_neg h, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      exact hd y a _ hax
  have hsurj := (GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C D.X p z₂ (ct₂ y₀) (yy y₀) (hyy₂ y₀).uIsLab).1
  choose A hA using fun x : (ct y₀).T.P.D.toPre.X =>
    hsurj (QuotientAddGroup.mk x : ModN (D.X.S.r * D.X.S.N) (ct y₀).T.P.D.toPre.X)
  obtain ⟨f, t, hfO, hft⟩ := GlobalTheory.T.unitary_thetaFourier_classSums_deeper_integral E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂
  have hfapp : (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) := fun ct yy₁ h1 => (hft ct yy₁ h1).2.2
  let F : (Fin 1 → Φ.X y₀) → ↥(X₁.S.HH X₁.M z₁) → integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ :=
    fun c κ => ⟨f (A (e y₀ (c 0))) κ, (hB _).2 fun z' hz' => hfO _ κ z' hz'⟩
  have hF : ∀ c κ, ((F c κ : integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁) : D.X.Ω₁) = f (A (e y₀ (c 0))) κ :=
    fun _ _ => rfl
  refine ⟨k, ↥(X₁.S.HH X₁.M z₁), F, hk0, ?_, ?_, ?_, ?_⟩
  ·
    intro c c' κ hcc
    apply Subtype.ext
    rw [hF, hF]
    obtain ⟨w, hw⟩ := hcc 0
    refine GlobalTheory.UPoinc.DeepSame.deep_eq_of_congMod E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂ f t hfO hfapp w₁ w₂ htie hproj (ct₂ y₀) (yy y₀) (hyy₂ y₀) _ _ _ _
      (hA _) (hA _) ⟨e y₀ w, ?_⟩ κ
    rw [hw, map_add (f := _), map_nsmul]
  ·
    intro y c κ μ hμ hmin
    rw [hval y, qW_one]
    obtain ⟨hle_t, -, -⟩ := hft (ct y) (yy₁ y) (hyy₁ y).uIsLab
    have hyyA : yy y (A (e y₀ (c 0))) = QuotientAddGroup.mk (e y (k y (c 0))) := hk y _ _ (hA _)
    refine GlobalTheory.UPoinc.class_limit_norm_le p (Φ.X y) (ct y).T.P.D.toPre.X (e y).toAddEquiv (Φ.β y) (ct y).T.be (Φ.sc y) (ct y).sc
      (Φ.sc_pos y) (he y) D.m (fun μ' => t (ct y) (yy₁ y) μ' κ) (fun μ' => hle_t μ' κ) _ _
      (hfapp (ct y) (yy₁ y) (hyy₁ y).uIsLab (y₂ y) (hq y) (hcen y) (yy y) (hyy y).uIsLab (hcomp y) _ _ κ hyyA) (μ 0) ?_ ?_
    · obtain ⟨w, hw⟩ := hμ 0
      exact ⟨e y w, by simp [hw, map_add (f := _), map_nsmul]⟩
    · intro x' hx'
      have := hmin (fun _ => x') (fun u => by rw [Subsingleton.elim u 0]; exact hx')
      simpa [qW_one] using this
  ·
    intro y μ huniq
    obtain ⟨-, heq_t, -⟩ := hft (ct y) (yy₁ y) (hyy₁ y).uIsLab
    obtain ⟨κ, hκ⟩ := heq_t (e y (μ 0))
    refine ⟨fun u => (k y).symm (μ u), κ, fun u => ⟨0, by simp⟩, ?_⟩
    rw [hval y, qW_one]
    have hyyA : yy y (A (e y₀ ((k y).symm (μ 0)))) = QuotientAddGroup.mk (e y (μ 0)) := by
      simpa using hk y _ _ (hA (e y₀ ((k y).symm (μ 0))))
    refine GlobalTheory.UPoinc.classSum_norm_eq_of_unique_least p (Φ.X y) (ct y).T.P.D.toPre.X (e y).toAddEquiv (Φ.β y) (ct y).T.be (Φ.sc y) (ct y).sc
      (Φ.sc_pos y) (he y) D.m (fun μ' => t (ct y) (yy₁ y) μ' κ) (fun μ' => (hft (ct y) (yy₁ y) (hyy₁ y).uIsLab).1 μ' κ) _ _
      (hfapp (ct y) (yy₁ y) (hyy₁ y).uIsLab (y₂ y) (hq y) (hcen y) (yy y) (hyy y).uIsLab (hcomp y) _ _ κ hyyA) (μ 0)
      ⟨0, by simp⟩ hκ ?_
    intro x' hx' hne
    have := huniq (fun _ => x') (fun u => by rw [Subsingleton.elim u 0]; exact hx')
      (fun h => hne (congrFun h 0))
    simpa [qW_one] using this
  ·
    intro σ hσ
    obtain ⟨σ', hσ'⟩ := GlobalTheory.UPoinc.intClosure_aut_extends X₁.o₁ X₁.Ω₁ D.X.Ω₁ X₁.M z₁ σ
    obtain ⟨s, hs_pt, hs_q, hs_val⟩ := GlobalTheory.Poinc.GalAut.autAct X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q
      hN D.fin D.gen σ'
    have hcs : (y₂ y₀ ≫ s) (cPt p) = z₂ := by
      refine GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q hN D.fin D.gen z₁ 𝔷 h𝔷 z₂ hz₂ h𝔷z p _ ?_ ?_
      · rw [← Scheme.Hom.comp_apply, Category.assoc, hs_q, hq]; exact (ct y₀).cen
      · intro b hb
        rw [← Category.assoc, hs_val, hσ', ← hval]
        apply hlt y₀
        have h2 : b ∈ 𝔷.comap σ := by rw [hσ]; exact hb
        exact h2
    have hsz : s z₂ = z₂ := by
      have h3 := hcs
      rw [Scheme.Hom.comp_apply, hcen y₀] at h3
      exact h3
    obtain ⟨aσ, -, haσ⟩ := GlobalTheory.T.deeperUnitaryLevel_galois_acts_on_labels E H Dw hpq l Xo cf C X₁ D σ' s hs_pt
    have hqs : (y₂ y₀ ≫ s) ≫ D.q = (ct y₀).y := by rw [Category.assoc, hs_q, hq]
    obtain ⟨yy', hyy', hcomp'⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀) (y₂ y₀ ≫ s) hqs
    let ct₂' : UCTrait D.X p z₂ := { D.lift (ct y₀) (y₂ y₀ ≫ s) hqs with cen := hcs }
    have hyy'₂ : UIsLabW D.X w₂ ct₂' yy' := hyy'
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ (ct₂ y₀) ct₂' (yy y₀) yy' (hyy₂ y₀) hyy'₂
    have hrel : ∀ x, yy' x = yy y₀ (aσ x) :=
      haσ p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀).uIsLab (y₂ y₀) (hq y₀) hqs (yy y₀) yy' (hyy y₀).uIsLab (hcomp y₀) hyy'.uIsLab hcomp'
    let γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀ := (e y₀).trans (g.trans (e y₀).symm)
    have hL : 3 ≤ X₁.S.r * X₁.S.N := by
      have h6 := X₁.big.2.2
      have : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega)) (Nat.factorial_ne_zero _))
      omega
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]; exact D.dvd.trans ((dvd_pow_self _ two_ne_zero).trans (dvd_mul_left _ _))
    have hLpos : 0 < D.X.S.r * D.X.S.N :=
      Nat.mul_pos (by have := D.X.S.r_pos; omega) (by have := D.X.S.N_ge; omega)
    have htf : ∀ (n : ℕ) (x : (ct y₀).T.P.D.toPre.X), 0 < n → n • x = 0 → x = 0 := by
      intro n x hn hx
      have h1 : ((n : ℤ)) • (e y₀).symm x = 0 := by
        rw [natCast_zsmul, ← map_nsmul, hx, map_zero]
      rcases smul_eq_zero.1 h1 with h | h
      · omega
      · simpa using congrArg (e y₀) h
    have hcongY := GlobalTheory.UPoinc.compat_forces_congMod X₁.S.Gam D.X.S.Gam (ct y₀).T.P.D.toPre.X (X₁.S.r * X₁.S.N) (D.X.S.r * D.X.S.N)
      (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) (Nat.div_mul_cancel hdvd) hLpos htf D.lab (yy₁ y₀)
      (GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C X₁ p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀).uIsLab).1 (yy y₀) yy' (hcomp y₀) hcomp'
      g.toLinearMap.toAddMonoidHom (fun a μ h => hg a μ h)
    have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x := by
      intro x
      obtain ⟨w, hw⟩ := hcongY (e y₀ x)
      have hw' : g (e y₀ x) = e y₀ x + (X₁.S.r * X₁.S.N) • w := hw
      refine ⟨(e y₀).symm w, ?_⟩
      simp only [γ, LinearEquiv.trans_apply]
      rw [hw', map_add (f := _), map_nsmul, LinearEquiv.symm_apply_apply]
    refine ⟨γ, GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (Φ.X y₀) (X₁.S.r * X₁.S.N) D.m hL (γ.restrictScalars ℤ) hcong, hcong, ?_⟩
    · intro c κ
      apply Subtype.ext
      rw [← hσ']
      show σ' (f (A (e y₀ (c 0))) κ) = f (A (e y₀ (γ (c 0)))) κ
      refine GlobalTheory.UPoinc.GalLab.main E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂ f t hfO hfapp w₁ w₂ htie hproj σ' s hs_q hs_val hsz aσ
        (fun ct yy₁ h1 y h h' yy yy' h2 h3 h4 h5 => haσ p z₁ ct yy₁ h1 y h h' yy yy' h2 h3 h4 h5)
        (ct₂ y₀) (yy y₀) (hyy₂ y₀) _ _ _ _ (by rw [← hrel]; exact hg _ _ (hA _)) (hA _) ⟨0, ?_⟩ κ
      simp [γ]

end GlobalTheory.UPoinc.UCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCoreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_classSums_deeper_level_geometric_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.UPoinc.UCore.classSums_core | exact GlobalTheory.UPoinc.UCore.classSums_core | (intros; apply GlobalTheory.UPoinc.UCore.classSums_core <;> assumption)
end
