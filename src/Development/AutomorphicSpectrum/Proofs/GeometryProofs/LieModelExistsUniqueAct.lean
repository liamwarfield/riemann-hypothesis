module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieModel_exists_unique_act : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E)
    (O : Type) [CommRing O] (act : O → (G ⟶ G)), (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G →
    (∀ a b, act (a * b) = act a ≫ act b) → (∀ a b, act (a + b) = act a * act b) →
    ∃! ρ : O →+* Module.End R E, M.IsActOf act ρ := by
  intro S G _ R _ x E _ _ M O _ act hmon h1 hmul hadd
  have hex : ∀ a, ∃ A : E →ₗ[R] E, (∀ e, M.pt (A e) = M.pt e ≫ act a) ∧
      ∀ B : E →ₗ[R] E, (∀ e, M.pt (B e) = M.pt e ≫ act a) → B = A := by
    intro a
    have := hmon a
    exact lieModel_exists_unique_diff S G G R x E E M M (act a)
  choose A hA hAu using hex
  have hone : LinearMap.id = A 1 := hAu 1 LinearMap.id fun e => by
    rw [h1, Category.comp_id]
    rfl
  have hmul' : ∀ a b, A (a * b) = A a * A b := fun a b => (hAu (a * b) (A a * A b) fun e => by
    rw [Module.End.mul_apply, hA a, hA b, Category.assoc, ← hmul b a, mul_comm]).symm
  have hadd' : ∀ a b, A (a + b) = A a + A b := fun a b => (hAu (a + b) (A a + A b) fun e => by
    rw [LinearMap.add_apply, M.add, hA a, hA b, ← MonObj.comp_mul, hadd]).symm
  refine ⟨RingHom.mk' { toFun := A, map_one' := hone.symm, map_mul' := hmul' } hadd',
    fun a e => hA a e, fun ρ hρ => ?_⟩
  ext a : 1
  exact hAu a (ρ a) (hρ a)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordLoc

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (hξ : genPt ξ ∈ U) (q : Cpt ξ) (hq : q.1 ∈ U)
    (f : Γ(X, U)) :
    genMap ξ q ((X.presheaf.germ U q.1 hq).hom f) =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hξ).hom f) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hq q.2
  have h2 := congrArg (fun g => g.hom f) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  show (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes q.2).hom
    ((X.presheaf.germ U q.1 hq).hom f)) = _
  rw [h2]

end GlobalTheory.CompanionTheory.Ar.CoordLoc

namespace GlobalTheory.CompanionTheory.Ar

theorem regAt_iff_exists_chart_fraction : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ) (p : Cpt ξ), InChart ξ x c p → ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ Algebra.adjoin o (Set.range fun j => x j / x c), unitAt ξ p s ∧ s * a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
  intro X Ω _ ξ o _ _ κ x hT c p hp a
  have hc : x c ≠ 0 := hp.1
  constructor
  · intro ha
    obtain ⟨U, hU, hUmem⟩ := hT.affine c hc
    have hpU : p.1 ∈ U := (hUmem p.1).2 ⟨p.2, hp⟩
    have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
    let φ : Γ(X, U) → Ω := fun f =>
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.germ U (genPt ξ) hgU).hom f)
    have hφA : ∀ f, φ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := by
      intro f
      rw [hT.ring c hc]
      intro q hq
      have hqU : q.1 ∈ U := (hUmem q.1).2 ⟨q.2, hq⟩
      exact RingHom.mem_range.mpr ⟨(X.presheaf.germ U q.1 hqU).hom f, CoordLoc.genMap_germ ξ U hgU q hqU f⟩
    have hφp : ∀ f, φ f = genMap ξ p ((X.presheaf.germ U p.1 hpU).hom f) := fun f =>
      (CoordLoc.genMap_germ ξ U hgU p hpU f).symm
    have ha' : a ∈ (genMap ξ p).range := ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp ha'
    let xU : U := ⟨p.1, hpU⟩
    have := hU.isLocalization_stalk xU
    have hgerm : ∀ f, algebraMap Γ(X, U) (X.presheaf.stalk xU.1) f = (X.presheaf.germ U p.1 hpU).hom f :=
      fun f => rfl
    obtain ⟨⟨t, s⟩, hts⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf xU).asIdeal.primeCompl
      (S := X.presheaf.stalk xU.1) g
    have hspec := IsLocalization.mk'_spec (X.presheaf.stalk xU.1) t s
    simp only at hts
    rw [hts, hgerm, hgerm] at hspec
    have hunit := IsLocalization.map_units (X.presheaf.stalk xU.1) s
    rw [hgerm] at hunit
    obtain ⟨u, hu⟩ := hunit
    refine ⟨φ s, hφA s, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hφp, ← hu]
      exact (u.isUnit.map (genMap ξ p)).ne_zero
    · exact ⟨(X.presheaf.germ U p.1 hpU).hom s, (hφp s).symm⟩
    · refine RingHom.mem_range.mpr ⟨(↑u⁻¹ : X.presheaf.stalk p.1), ?_⟩
      rw [hφp, ← hu]
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, Units.inv_mul, map_one]
    · have hmul : φ s * genMap ξ p g = φ t := by
        rw [hφp, hφp, ← map_mul, mul_comm, hspec]
      rw [hmul]
      exact hφA t
  · rintro ⟨s, _, ⟨hs0, _, hsinv⟩, hsa⟩
    have hsa' : s * a ∈ regAt ξ p := (hT.ring c hc (s * a)).mp hsa p hp
    have heq : a = s⁻¹ * (s * a) := by
      rw [← _root_.mul_assoc, inv_mul_cancel₀ hs0, _root_.one_mul]
    rw [heq]
    exact Subring.mul_mem _ hsinv hsa'

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.regAt_iff_chart_localization := GlobalTheory.CompanionTheory.Ar.regAt_iff_exists_chart_fraction
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def Char0 (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Prop := ∀ r : ℕ, r.Prime → ¬ InFibre ξ r p

def Pts (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Set (Subring Ω) :=
  {R | ∃ p : Cpt ξ, Char0 ξ p ∧ R = regAt ξ p}

def IsLocAt [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (q : Ideal A) (R : Subring Ω) : Prop :=
  ∀ a : Ω, a ∈ R ↔ ∃ s : A, s ∉ q ∧ (s : Ω) * a ∈ A

structure IsSncPatch [Algebra ℚ Ω] (Pt Bd : Set (Subring Ω)) (e : ℕ) (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) :
    Prop where
  fg : A.FG
  smooth : Algebra.Smooth ℚ A
  le : n ≤ e
  li : LinearIndependent A fun i => KaehlerDifferential.D ℚ A (z i)
  span : Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤
  pts : ∀ q : Ideal A, q.IsPrime → ∃ R ∈ Pt, IsLocAt A q R ∧ (R ∈ Bd ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q)

end GlobalTheory.CompanionTheory.Ar.SncBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartPrimes

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : X.Opens) (hg : genPt ξ ∈ V) : Γ(X, V) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ V (genPt ξ) hg).hom

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_germ_eq (V : X.Opens) (hg : genPt ξ ∈ V) (p : Cpt ξ) (hp : p.1 ∈ V) (f : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hp f) = secVal ξ V hg f := by
  change _ = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hg f)
  rw [← X.presheaf.germ_stalkSpecializes hp p.2]
  rfl

theorem isUnit_iff_unitAt (p : Cpt ξ) (hinj : Function.Injective (genMap ξ p))
    (s : X.presheaf.stalk p.1) : IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro h
    have h1 : IsUnit (genMap ξ p s) := h.map (genMap ξ p)
    refine ⟨h1.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := h
    refine ⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ), ?_⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    simp
  · rintro ⟨h0, -, ⟨w, hw⟩⟩
    refine IsUnit.of_mul_eq_one w (hinj ?_)
    rw [map_mul, hw, map_one]
    exact mul_inv_cancel₀ h0

theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec y ∈ U := by
  change hU.fromSpec y ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨y, rfl⟩

theorem exists_secVal_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genPt ξ ∈ U)
    (hs : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω)
    (ha : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → a ∈ regAt ξ ⟨q, h⟩) :
    ∃ f : Γ(X, U), secVal ξ U hg f = a := by
  let ρ := secVal ξ U hg
  let I : Ideal Γ(X, U) :=
    { carrier := {r | ∃ f, ρ f = ρ r * a}
      add_mem' := by
        rintro r s ⟨f, hf⟩ ⟨g, hg⟩
        exact ⟨f + g, by rw [map_add (f := _), map_add (f := _), hf, hg, add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r s ⟨f, hf⟩
        exact ⟨r * f, by rw [smul_eq_mul, map_mul, map_mul, hf, _root_.mul_assoc]⟩ }
  by_cases hI : I = ⊤
  · obtain ⟨f, hf⟩ : (1 : Γ(X, U)) ∈ I := hI ▸ Submodule.mem_top
    exact ⟨f, by rw [hf, map_one, _root_.one_mul]⟩
  · exfalso
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    let q : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
    have hq : hU.fromSpec q ∈ U := fromSpec_mem hU q
    have hsp := hs _ hq
    obtain ⟨σ, hσ⟩ := ha _ hsp hq
    have hloc := hU.isLocalization_stalk' q hq
    obtain ⟨⟨r, s⟩, e⟩ := @IsLocalization.surj _ _ _ _ _
      (X.presheaf.algebra_section_stalk ⟨hU.fromSpec q, hq⟩) hloc σ
    have e' : σ * X.presheaf.germ U _ hq s.1 = X.presheaf.germ U _ hq r := e
    have e2 := congrArg (genMap ξ ⟨_, hsp⟩) e'
    rw [map_mul, hσ, genMap_germ_eq U hg ⟨_, hsp⟩ hq s.1, genMap_germ_eq U hg ⟨_, hsp⟩ hq r] at e2
    exact s.2 (hIm ⟨r, by rw [← e2, mul_comm]⟩)

theorem notMem_iff_isUnit_germ {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (hq : hU.fromSpec y ∈ U) (f : Γ(X, U)) :
    f ∉ y.asIdeal ↔ IsUnit (X.presheaf.germ U (hU.fromSpec y) hq f) := by
  rw [← X.mem_basicOpen f _ hq, ← PrimeSpectrum.mem_basicOpen]
  have h := hU.fromSpec_preimage_basicOpen f
  change _ ↔ y ∈ (hU.fromSpec ⁻¹ᵁ X.basicOpen f)
  rw [h]
  rfl

theorem inChart_genPt (hξ : IsCptGen ξ) {κ : Type} (x : κ → Ω) (c : κ) (hc : x c ≠ 0) :
    InChart ξ x c ⟨genPt ξ, specializes_rfl⟩ := by
  refine ⟨hc, fun j => ?_⟩
  obtain ⟨s, hs⟩ := hξ.bij.2 (x j / x c)
  refine ⟨s, ?_⟩
  rw [← hs]
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

end GlobalTheory.CompanionTheory.Ar.ChartPrimes

namespace GlobalTheory.CompanionTheory.Ar


open ChartPrimes in
theorem chart_point_of_prime : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type)
    [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ), x c ≠ 0 →
    ∀ I : Ideal (Algebra.adjoin o (Set.range fun j => x j / x c)), I.IsPrime →
    ∃! p : Cpt ξ, InChart ξ x c p ∧ ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ I ↔ unitAt ξ p (s : Ω) := by
  intro X Ω _ ξ o _ _ κ x T c hc I hI
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hg : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩
  have hs : ∀ q ∈ U, genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h, -⟩ := (hmem q).1 hq
    exact h
  have hin : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → InChart ξ x c ⟨q, h⟩ := fun q h hq => by
    obtain ⟨_, h'⟩ := (hmem q).1 hq
    exact h'
  let ρ := secVal ξ U hg
  have hρA : ∀ f, ρ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := fun f =>
    (T.ring c hc _).2 fun p hp => ⟨_, genMap_germ_eq U hg p ((hmem _).2 ⟨p.2, hp⟩) f⟩
  have hsurj : ∀ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c), ∃ f, ρ f = a := fun a ha =>
    exists_secVal_eq hU hg hs a fun q h hq => (T.ring c hc a).1 ha _ (hin q h hq)
  let ρ' : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c) := ρ.codRestrict _ hρA
  have hρ' : ∀ f, ((ρ' f : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = ρ f := fun _ => rfl

  have key : ∀ (y : PrimeSpectrum Γ(X, U)) (h : genPt ξ ⤳ hU.fromSpec y) (f : Γ(X, U)),
      f ∉ y.asIdeal ↔ unitAt ξ ⟨hU.fromSpec y, h⟩ (ρ f) := fun y h f => by
    have hq := fromSpec_mem hU y
    rw [notMem_iff_isUnit_germ hU y hq f, ← genMap_germ_eq U hg ⟨_, h⟩ hq f]
    exact isUnit_iff_unitAt ⟨_, h⟩ (T.gen.inj _) _
  let y : PrimeSpectrum Γ(X, U) := ⟨I.comap ρ', inferInstance⟩
  have hy := fromSpec_mem hU y
  refine ⟨⟨hU.fromSpec y, hs _ hy⟩, ⟨hin _ _ hy, fun s => ?_⟩, ?_⟩
  · obtain ⟨f, hf⟩ := hsurj s s.2
    have hfs : ρ' f = s := Subtype.ext hf
    have := key y (hs _ hy) f
    rw [hf] at this
    rw [← this, ← hfs]
    rfl
  · rintro ⟨p, hp⟩ ⟨hpc, hpI⟩
    have hpU : p ∈ U := (hmem p).2 ⟨hp, hpc⟩
    obtain ⟨y', rfl⟩ : ∃ y', hU.fromSpec y' = p := ⟨_, hU.fromSpec_primeIdealOf ⟨p, hpU⟩⟩
    have hyy : y' = y := PrimeSpectrum.ext (Ideal.ext fun f => not_iff_not.1 ((key y' hp f).trans (hpI (ρ' f)).symm))
    exact Subtype.ext (congrArg (fun t => hU.fromSpec t) hyy)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.prime_chart_existsUnique_point := GlobalTheory.CompanionTheory.Ar.chart_point_of_prime
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumber
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumber
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TanLift

theorem comp_one_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) : u ≫ (1 : X ⟶ M) = 1 := by
  exact MonObj.comp_one u

theorem comp_mul_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a b : X ⟶ M) :
    u ≫ (a * b) = (u ≫ a) * (u ≫ b) := by
  exact MonObj.comp_mul u a b

theorem comp_pow_over {S : Scheme.{0}} {X Y M : Over S} [GrpObj M] (u : Y ⟶ X) (a : X ⟶ M) (n : ℕ) :
    u ≫ a ^ n = (u ≫ a) ^ n := by
  induction n with
  | zero => simp only [pow_zero]; exact GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_one_over u
  | succ n ih => rw [pow_succ, pow_succ, GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_mul_over, ih]

section

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  {L : Type} [AddCommGroup L] [Module R L]

theorem pt_zero (M : LieModel G x L) : M.pt 0 = 1 := by
  have h : M.pt 0 * M.pt 0 = M.pt 0 := by rw [← M.5, add_zero]
  exact mul_eq_left.mp h

theorem pt_nsmul (M : LieModel G x L) (e : L) (n : ℕ) : M.pt (n • e) = M.pt e ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, GlobalTheory.CompanionTheory.Ar.BT.TanLift.pt_zero]
  | succ n ih => rw [succ_nsmul, M.5, ih, pow_succ]

theorem dualMap_epsMul (I : Ideal R) (c : R) (hc : Ideal.Quotient.mk I c = 0) :
    (dualMap (Ideal.Quotient.mk I)).comp (epsMul c) =
      ((algebraMap (R ⧸ I) (DualNumber (R ⧸ I))).comp (Ideal.Quotient.mk I)).comp
        (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl, hc]

theorem dualMap_algebraMap (I : Ideal R) :
    (dualMap (Ideal.Quotient.mk I)).comp (algebraMap R (DualNumber R)) =
      (algebraMap (R ⧸ I) (DualNumber (R ⧸ I))).comp (Ideal.Quotient.mk I) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end

theorem tangent_mod_torsion : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (e : L), ∃! (v : Spec (CommRingCat.of (DualNumber (R ⧸ Ideal.span {(N : R)}))) ⟶ Γ.G.left), v ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp (Ideal.Quotient.mk _))) ∧ v ≫ i = Spec.map (CommRingCat.ofHom (dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫ (M.pt e).left := by
  intro R _ _ T _ _ Γ S G _ _ x N i hi L _ _ M e
  obtain ⟨-, -, hinj, htors⟩ := hi
  let Y : Over (Spec (CommRingCat.of R)) := Over.mk (Spec.map (CommRingCat.ofHom
    ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp
      (Ideal.Quotient.mk (Ideal.span {(N : R)})))))
  have hu : Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
      (GlobalTheory.CompanionTheory.Ar.epsAt x).hom = (Over.mk (Y.hom ≫ x)).hom := by
    simp only [GlobalTheory.CompanionTheory.Ar.epsAt, Over.mk_hom, Y]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, GlobalTheory.CompanionTheory.Ar.BT.TanLift.dualMap_algebraMap]
  let u : Over.mk (Y.hom ≫ x) ⟶ GlobalTheory.CompanionTheory.Ar.epsAt x := Over.homMk _ hu
  let u₀ : Over.mk (Y.hom ≫ x) ⟶ Over.mk x := Over.homMk Y.hom rfl
  have hN : Ideal.Quotient.mk (Ideal.span {(N : R)}) (N : R) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have htan : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (M.pt e).left =
      (1 : Over.mk x ⟶ G).left := M.2 e
  have hg : (u ≫ M.pt e) ^ N = 1 := by
    rw [← GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_pow_over, ← GlobalTheory.CompanionTheory.Ar.BT.TanLift.pt_nsmul, ← Nat.cast_smul_eq_nsmul R,
      ← GlobalTheory.CompanionTheory.Ar.BT.TanLift.comp_one_over u₀]
    apply Over.OverMorphism.ext
    have e₁ : (u ≫ M.pt ((N : R) • e)).left =
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
          Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul (N : R))) ≫ (M.pt e).left := by
      rw [Over.comp_left, M.6]
      rfl
    have e₂ : (u₀ ≫ (1 : Over.mk x ⟶ G)).left =
        Spec.map (CommRingCat.ofHom
          ((algebraMap (R ⧸ Ideal.span {(N : R)}) (DualNumber (R ⧸ Ideal.span {(N : R)}))).comp
            (Ideal.Quotient.mk (Ideal.span {(N : R)})))) ≫
          Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (M.pt e).left := by
      rw [Over.comp_left, htan]
      rfl
    rw [e₁, e₂, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, GlobalTheory.CompanionTheory.Ar.BT.TanLift.dualMap_epsMul _ _ hN]
  obtain ⟨y, hy⟩ := (htors Y (u ≫ M.pt e)).1 hg
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · rw [hy]
    rfl
  · rintro v ⟨hv₁, hv₂⟩
    have hv : Over.homMk (U := Y) (V := Γ.G) v hv₁ = y := by
      refine hinj Y _ y ?_
      change v ≫ i = _
      rw [hv₂, hy]
      rfl
    calc v = (Over.homMk (U := Y) (V := Γ.G) v hv₁).left := rfl
      _ = y.left := by rw [hv]

end GlobalTheory.CompanionTheory.Ar.BT.TanLift
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT
alias GlobalTheory.T.existsUnique_tangent_dual_number := GlobalTheory.CompanionTheory.Ar.BT.TanLift.tangent_mod_torsion
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitIffUnitAt
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ValHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

def stalkEquiv {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => hξ.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩

theorem stalkEquiv_coe {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    ((stalkEquiv ξ hξ p s : regAt ξ p) : Ω) = genMap ξ p s := rfl

theorem isUnit_iff_unitAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (hξ : IsCptGen ξ) (p : Cpt ξ) (s : X.presheaf.stalk p.1) :
    IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro hs
    obtain ⟨u, rfl⟩ := hs
    refine ⟨((u.isUnit).map (genMap ξ p)).ne_zero, ⟨_, rfl⟩, ⟨((u⁻¹ : _ˣ) : X.presheaf.stalk p.1), ?_⟩⟩
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul, Units.inv_mul, map_one]
  · rintro ⟨h0, -, ⟨t, ht⟩⟩
    refine IsUnit.of_mul_eq_one t (hξ.inj p ?_)
    rw [map_mul, map_one, ht, mul_inv_cancel₀ h0]

theorem exists_valAt_hom (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (R : Type) [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X)
    (h : genPt ξ ⤳ centre z) (hξ : IsCptGen ξ) :
    ∃ φ : regAt ξ ⟨centre z, h⟩ →+* R,
      (∀ (a : Ω) (r : R), ValAt ξ z a r ↔ ∃ ha : a ∈ regAt ξ ⟨centre z, h⟩, φ ⟨a, ha⟩ = r) ∧
      ∀ a : regAt ξ ⟨centre z, h⟩, IsUnit (φ a) ↔ unitAt ξ ⟨centre z, h⟩ (a : Ω) := by
  let p : Cpt ξ := ⟨centre z, h⟩
  let e := stalkEquiv ξ hξ p
  let v : X.presheaf.stalk (centre z) →+* R := (Scheme.stalkClosedPointTo z).hom
  have hv : IsLocalHom v := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo z).hom)
  have key : ∀ s, e.symm (e s) = s := e.symm_apply_apply
  refine ⟨v.comp (e.symm : regAt ξ p →+* X.presheaf.stalk p.1), ?_, ?_⟩
  · intro a r
    constructor
    · rintro ⟨h', s, hs, hr⟩
      have hs' : genMap ξ p s = a := hs
      refine ⟨⟨s, hs'⟩, ?_⟩
      have : (⟨a, ⟨s, hs'⟩⟩ : regAt ξ p) = e s := Subtype.ext hs'.symm
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [this, key]
      exact hr
    · rintro ⟨ha, hr⟩
      refine ⟨h, e.symm ⟨a, ha⟩, ?_, hr⟩
      have := stalkEquiv_coe ξ hξ p (e.symm ⟨a, ha⟩)
      rw [RingEquiv.apply_symm_apply] at this
      exact this.symm
  · intro a
    obtain ⟨s, rfl⟩ := e.surjective a
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [key]
    have : IsUnit (v s) ↔ IsUnit s := isUnit_map_iff v s
    exact this.trans (isUnit_iff_unitAt ξ hξ p s)

end GlobalTheory.CompanionTheory.Ar.ValHom
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherian
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordNoeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

lemma genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U)
    (h : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq s) = secVal ξ U h s := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes _ _ _
  simp only [genMap, secVal, ← e]
  rfl

lemma secVal_res (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (h : genPt ξ ∈ V)
    (s : Γ(X, U)) : secVal ξ V h (X.presheaf.map i.op s) = secVal ξ U (leOfHom i h) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply i (genPt ξ) h s)

lemma secVal_injective {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (U : X.Opens)
    (h : genPt ξ ∈ U) (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (secVal ξ U h) := by
  intro s t e
  refine TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => ?_
  apply hg.inj ⟨q, hU q hq⟩
  exact (genMap_germ ξ ⟨q, hU q hq⟩ U hq h s).trans (e.trans (genMap_germ ξ ⟨q, hU q hq⟩ U hq h t).symm)

lemma exists_secVal_eq {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (U : X.Opens)
    (h : genPt ξ ∈ U) (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω)
    (ha : ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) : ∃ s, secVal ξ U h s = a := by
  have key : ∀ q : U, ∃ (W : X.Opens) (_ : q.1 ∈ W) (_ : W ⟶ U) (hW : genPt ξ ∈ W) (s : Γ(X, W)),
      secVal ξ W hW s = a := by
    intro q
    obtain ⟨t, ht⟩ := ha ⟨q.1, hU _ q.2⟩ q.2
    obtain ⟨V, hqV, s, rfl⟩ := X.presheaf.germ_exist t
    have hqW : q.1 ∈ V ⊓ U := ⟨hqV, q.2⟩
    have hW : genPt ξ ∈ V ⊓ U := (hU _ q.2).mem_open (V ⊓ U).isOpen hqW
    refine ⟨V ⊓ U, hqW, homOfLE inf_le_right, hW, X.presheaf.map (homOfLE inf_le_left).op s, ?_⟩
    rw [secVal_res, ← genMap_germ ξ ⟨q.1, hU _ q.2⟩ V hqV]
    exact ht
  choose W hq i hW s hs using key
  have comp : TopCat.Presheaf.IsCompatible X.sheaf.1 W s := by
    intro p q
    apply secVal_injective hg (W p ⊓ W q) ⟨hW p, hW q⟩ (fun r hr => hU r (leOfHom (i p) hr.1))
    refine (secVal_res ξ _ _ _).trans (Eq.trans ?_ (secVal_res ξ _ _ _).symm)
    rw [hs, hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W U i
    (fun r hr => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, hr⟩, hq _⟩) s comp
  refine ⟨t, ?_⟩
  rw [← hs ⟨_, h⟩, ← ht ⟨_, h⟩]
  exact (secVal_res ξ _ _ _).symm

lemma mem_regAt_self {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨t, ht⟩ := hg.bij.2 a
  refine ⟨t, ?_⟩
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact ht

lemma isNoetherianRing_chart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type} [CommRing o]
    [IsNoetherianRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (tie : CoordTie o ξ x)
    (c : κ) (hc : x c ≠ 0) (U : X.Opens) (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩)
    (h : genPt ξ ∈ U) : IsNoetherianRing Γ(X, U) := by
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hU q).1 hq).elim fun h _ => h
  have hA : IsNoetherianRing (Algebra.adjoin o (Set.range fun j => x j / x c)) := by
    have : Algebra.FiniteType o (Algebra.adjoin o (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => x j / x c).toFinset, by simp⟩
    exact Algebra.FiniteType.isNoetherianRing o _
  have mem : ∀ a, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ s, secVal ξ U h s = a := by
    intro a
    rw [tie.ring c hc a]
    constructor
    · intro H
      refine exists_secVal_eq tie.gen U h hsp a fun q hq => ?_
      obtain ⟨_, hc'⟩ := (hU q.1).1 hq
      exact H q hc'
    · rintro ⟨s, rfl⟩ p hp
      have hpU : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
      exact ⟨_, genMap_germ ξ p U hpU h s⟩
  let g : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c) :=
    (secVal ξ U h).codRestrict _ fun s => (mem _).2 ⟨s, rfl⟩
  have hb : Function.Bijective g := by
    constructor
    · intro s t e
      exact secVal_injective tie.gen U h hsp (congrArg Subtype.val e)
    · rintro ⟨a, ha⟩
      obtain ⟨s, rfl⟩ := (mem a).1 ha
      exact ⟨s, rfl⟩
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective g hb).symm

theorem noetherian_of_coordTie (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω)
    (tie : CoordTie o ξ x) :
    (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  refine ⟨fun p => ?_, fun hall => ?_⟩
  · obtain ⟨c, hcp⟩ := tie.cover p
    obtain ⟨U, hUa, hU⟩ := tie.affine c hcp.1
    have hp : p.1 ∈ U := (hU p.1).2 ⟨p.2, hcp⟩
    have h : genPt ξ ∈ U := p.2.mem_open U.isOpen hp
    haveI := isNoetherianRing_chart tie c hcp.1 U hU h
    letI := X.presheaf.algebra_section_stalk (⟨p.1, hp⟩ : U)
    haveI := hUa.isLocalization_stalk ⟨p.1, hp⟩
    haveI : IsNoetherianRing (X.presheaf.stalk p.1) :=
      IsLocalization.isNoetherianRing (hUa.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl _ ‹_›
    exact isNoetherianRing_of_surjective _ _ (genMap ξ p).rangeRestrict
      (genMap ξ p).rangeRestrict_surjective
  · have ex : ∀ c : {c // x c ≠ 0}, ∃ U : X.affineOpens,
        ∀ q : X, q ∈ (U : X.Opens) ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c.1 ⟨q, h⟩ := fun c => by
      obtain ⟨U, hUa, hU⟩ := tie.affine c.1 c.2
      exact ⟨⟨U, hUa⟩, hU⟩
    choose S hS using ex
    have hcov : (⨆ c, (S c : X.Opens)) = ⊤ := by
      refine eq_top_iff.2 fun q _ => ?_
      obtain ⟨c, hc⟩ := tie.cover ⟨q, hall q⟩
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨c, hc.1⟩, (hS _ q).2 ⟨hall q, hc⟩⟩
    have hgen : ∀ c, genPt ξ ∈ (S c : X.Opens) := fun c =>
      (hS c _).2 ⟨specializes_rfl, c.2, fun _ => mem_regAt_self tie.gen _⟩
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_affine_cover hcov fun c =>
      isNoetherianRing_chart tie c.1 c.2 _ (hS c) (hgen c)
    haveI : CompactSpace X := by
      refine ⟨?_⟩
      have e : (Set.univ : Set X) = ⋃ c, ((S c : X.Opens) : Set X) := by
        have := congrArg (fun V : X.Opens => (V : Set X)) hcov
        simpa using this.symm
      rw [e]
      exact isCompact_iUnion fun c => (S c).2.isCompact
    have hcl : closure {genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (hall q)
    have hirr : IsIrreducible (Set.univ : Set X) := hcl ▸ isIrreducible_singleton.closure
    haveI : IrreducibleSpace X := (irreducibleSpace_def X).2 hirr
    haveI : ∀ q : X, _root_.IsReduced (X.presheaf.stalk q) := fun q =>
      isReduced_of_injective (genMap ξ ⟨q, hall q⟩) (tie.gen.inj _)
    haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
    exact ⟨{}, isIntegral_of_irreducibleSpace_of_isReduced X⟩

end GlobalTheory.CompanionTheory.Ar.CoordNoeth

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtNoetherianModelNoetherianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
alias GlobalTheory.T.regAt_noetherian_model_noetherian := GlobalTheory.CompanionTheory.Ar.CoordNoeth.noetherian_of_coordTie
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegular
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.RegDenom

theorem exists_denom_of_injective {R K B S : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing B] [Finite S]
    (ρ : R →+* B) (v : S → B →+* K) (hv : Function.Injective v)
    (hρ : ∀ i r, v i (ρ r) = algebraMap R K r) (f : S → K) :
    ∃ d : R, d ≠ 0 ∧ ∃ b : B, ∀ i, v i b = algebraMap R K d * f i := by
  classical
  cases nonempty_fintype S
  have inj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  let W : Submodule K (S → K) := Submodule.span K (Set.range fun b : B => fun i => v i b)
  have hW : W = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top W (lt_top_iff_ne_top.mpr hne)
    have hm : Function.Injective (fun i : S => ((v i : B →+* K) : B →* K)) := by
      intro i j hij
      apply hv
      ext b
      exact DFunLike.congr_fun hij b
    have hli : LinearIndependent K (fun i : S => (fun b => v i b : B → K)) :=
      (linearIndependent_monoidHom B K).comp _ hm
    have hc : ∀ i, φ (Pi.single i 1) = 0 := by
      have h0 := Fintype.linearIndependent_iff.mp hli (fun i => φ (Pi.single i 1)) (by
        funext b
        have hb : φ (fun i => v i b) = 0 := hle (Submodule.subset_span ⟨b, rfl⟩)
        have hx : (fun i => v i b) = ∑ i, (v i b) • (Pi.single i (1 : K) : S → K) := by
          funext j
          simp [Finset.sum_apply, Pi.single_apply]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hx, map_sum] at hb
        simp only [map_smul, smul_eq_mul] at hb
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← hb]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _)
      exact h0
    apply hφ
    ext i
    simpa using hc i

  have key : ∀ x ∈ W, ∃ d : R, d ≠ 0 ∧ ∃ b : B, ∀ i, v i b = algebraMap R K d * x i := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x h =>
      obtain ⟨b, rfl⟩ := h
      exact ⟨1, one_ne_zero, b, fun i => by simp⟩
    | zero => exact ⟨1, one_ne_zero, 0, fun i => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, b, hb⟩ := hx
      obtain ⟨e, he, c, hc⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ρ e * b + ρ d * c, fun i => ?_⟩
      simp only [map_add (f := _), map_mul, hρ, hb, hc, Pi.add_apply]
      ring
    | smul k x _ hx =>
      obtain ⟨d, hd, b, hb⟩ := hx
      obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) k
      have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
      have hcK : algebraMap R K c ≠ 0 := fun h => hc0 (inj (by simpa using h))
      refine ⟨c * d, mul_ne_zero hc0 hd, ρ a * b, fun i => ?_⟩
      simp only [map_mul, hρ, hb, Pi.smul_apply, smul_eq_mul]
      field_simp
  exact key f (hW ▸ Submodule.mem_top)

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

def valHom {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valHom x U h s = valAt x U h s := rfl

theorem eq_of_valHom_eq {B : Type} [CommRing B] {X : Scheme.{0}} {x y : Spec (CommRingCat.of B) ⟶ X} {U : X.Opens}
    (hU : IsAffineOpen U) (hx : ⊤ ≤ x ⁻¹ᵁ U) (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : valHom x U hx = valHom y U hy) : x = y := by
  have ha : x.appLE U ⊤ hx = y.appLE U ⊤ hy := by
    ext s
    have := DFunLike.congr_fun e s
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of B)).hom).1 this
  have htop : IsAffineOpen (⊤ : (Spec (CommRingCat.of B)).Opens) := isAffineOpen_top _
  have h1 := hU.SpecMap_appLE_fromSpec x htop hx
  have h2 := hU.SpecMap_appLE_fromSpec y htop hy
  rw [ha, h2] at h1
  have : IsIso htop.fromSpec := by
    rw [show htop = isAffineOpen_top _ from rfl, IsAffineOpen.fromSpec_top]
    infer_instance
  exact (cancel_epi htop.fromSpec).mp h1.symm

theorem le_preimage_top {X Y : Scheme.{0}} (p : X ⟶ Y) (U : X.Opens) : U ≤ p ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

def structHom {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (le_preimage_top p U)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem valHom_structHom {B : Type} [CommRing B] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R))
    (i : R →+* B) (x : Spec (CommRingCat.of B) ⟶ X) (hx : x ≫ p = Spec.map (CommRingCat.ofHom i))
    (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (r : R) : valHom x U h (structHom p U r) = i r := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appLE ⊤ U (le_preimage_top p U) ≫ x.appLE U ⊤ h ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom = CommRingCat.ofHom i := by
    have e1 : p.appLE ⊤ U (le_preimage_top p U) ≫ x.appLE U ⊤ h = (x ≫ p).appTop := by
      rw [Scheme.Hom.appLE_comp_appLE]
      simp only [Scheme.Hom.appLE, Scheme.Hom.comp_appTop, Scheme.Hom.appTop]
      refine Eq.trans (congrArg _ ?_) (Category.comp_id _)
      exact (Spec (CommRingCat.of B)).presheaf.map_id _
    rw [reassoc_of% e1, hx, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact congr($(e).hom r)

theorem exists_denom_regularAt : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T]
    (Γ : QFGroup R T) (f : T → FractionRing R) (g : Γ.G.left),
    ∃ d : R, d ≠ 0 ∧ Γ.RegularAt (fun t => algebraMap R _ d * f t) g := by
  intro R _ _ T _ _ Γ f g
  obtain ⟨U, hU, hg, -⟩ := exists_isAffineOpen_mem_and_subset (x := g) (U := ⊤) trivial
  let S := {t : T // ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U}
  let v : S → Γ(Γ.G.left, U) →+* FractionRing R := fun t => valHom (Γ.pt t.1).left U t.2
  have hv : Function.Injective v := by
    intro s t e
    have hst := eq_of_valHom_eq hU s.2 t.2 e
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := inferInstance
    exact Subtype.ext (Γ.pt_inj s.1 t.1 x x (by rw [hst]))
  have hρ : ∀ t r, v t (structHom Γ.G.hom U r) = algebraMap R _ r := fun t r =>
    valHom_structHom Γ.G.hom _ _ (Over.w (Γ.pt t.1)) U t.2 r
  obtain ⟨d, hd, b, hb⟩ := exists_denom_of_injective (structHom Γ.G.hom U) v hv hρ (fun t => f t.1)
  exact ⟨d, hd, U, hg, b, fun t h => hb ⟨t, h⟩⟩

end GlobalTheory.CompanionTheory.Ar.BT.RegDenom
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegularStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
alias GlobalTheory.T.exists_denominator_regular := GlobalTheory.CompanionTheory.Ar.BT.RegDenom.exists_denom_regularAt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompat
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem genericBaseChange_ringHom_eq {R : Type} [CommRing R] [IsDomain R]
    {R' : Type} [CommRing R'] [IsDomain R'] [Algebra R R'] {B : Type} [CommRing B]
    (i : R →+* B) (j : B →+* FractionRing R) (j' : B →+* FractionRing R')
    (κ : FractionRing R →+* FractionRing R')
    (hκ : κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R'))
    (hj : Function.Injective j) (hji : j.comp i = algebraMap R _)
    (hj'i : j'.comp i = (algebraMap R' _).comp (algebraMap R R')) :
    j' = κ.comp j := by
  ext b
  obtain ⟨r, s, hs, hrs⟩ := IsFractionRing.div_surjective (A := R) (j b)
  have hs0 : algebraMap R (FractionRing R) s ≠ 0 := by
    simpa using IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := FractionRing R) hs
  have e1 : algebraMap R (FractionRing R) s * j b = algebraMap R (FractionRing R) r := by
    rw [← hrs]; field_simp
  have hjs : ∀ x : R, j (i x) = algebraMap R (FractionRing R) x := fun x =>
    RingHom.congr_fun hji x
  have e2 : i s * b = i r := by
    apply hj
    rw [map_mul, hjs, hjs, e1]
  have hj's : ∀ x : R, j' (i x) = κ (algebraMap R (FractionRing R) x) := fun x =>
    (RingHom.congr_fun hj'i x).trans (RingHom.congr_fun hκ x).symm
  have e3 : κ (algebraMap R (FractionRing R) s) * j' b = κ (algebraMap R (FractionRing R) r) := by
    rw [← hj's, ← hj's, ← map_mul, e2]
  have e4 : κ (algebraMap R (FractionRing R) s) * κ (j b) = κ (algebraMap R (FractionRing R) r) := by
    rw [← map_mul, e1]
  have hκs : κ (algebraMap R (FractionRing R) s) ≠ 0 := by
    simpa using hs0
  exact mul_left_cancel₀ hκs (e3.trans e4.symm)

theorem genericPoint_baseChange :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ t, (Γ'.pt t).left ≫ F = Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ t
  obtain ⟨B, _, i, j, j', σ, hj, hji, hj'i, -, hσ, hσ'⟩ := hF.pts
  have hjj : j' = κ.comp j := genericBaseChange_ringHom_eq i j j' κ hκ hj hji hj'i
  rw [← hσ' t, ← hσ t, hjj, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.BT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompatStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
alias GlobalTheory.T.base_change_points_compat := GlobalTheory.CompanionTheory.Ar.BT.genericPoint_baseChange
end
end
