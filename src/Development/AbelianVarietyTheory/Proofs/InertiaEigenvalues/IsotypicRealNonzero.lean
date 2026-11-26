module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPairThetaLowest
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LevEnvLevelSubgroupLeLevJAndCharacterEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzero
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open ReciprocityTheory.Aut Formalism.AUTREP
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section

namespace GlobalTheory.LiftRefIrr

theorem exists_ne_of_mem_iSup' {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Sort*} (p : ι → Submodule ℂ M)
    (ℓ : M →+ ℂ) {x : M} (hx : x ∈ ⨆ i, p i) (h : ℓ x ≠ 0) : ∃ i, ∃ y ∈ p i, ℓ y ≠ 0 := by
  by_contra H
  push_neg at H
  exact h (Submodule.iSup_induction p (motive := fun z => ℓ z = 0) hx (fun i y hy => H i y hy) (map_zero ℓ)
    (fun a b ha hb => by rw [map_add (f := _), ha, hb, add_zero]))

theorem exists_irr_pair {D : D7} {μ : D.what₂.Tup} {j : ℕ} (Mr : MtReal D μ j) (x : D.what₂.Mt μ j) (hx : x ≠ 0) :
    ∃ (S : Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)) (_ : NG.IsIrrRep Mr.wt.ρ S),
      ∃ F ∈ (NG.isoTyp Mr.wt.ρ S).comap Mr.real, inner ℂ F x ≠ 0 := by
  obtain ⟨-, ι, -, S, hirr, -, -, -, -, hsum⟩ := GlobalTheory.T.typeSpaces_orthogonal_of_classSum_inner D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  let p : ι → Submodule ℂ (D.what₂.Mt μ j) :=
    fun i => (NG.isoTyp Mr.wt.ρ (S i) ⊓ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ).comap Mr.real
  have htop : (⨆ i, p i) = ⊤ := by
    apply Submodule.map_injective_of_injective Mr.real_inj
    rw [Submodule.map_iSup, Submodule.map_top, Mr.real_range]
    conv_rhs => rw [← hsum]
    refine iSup_congr fun i => ?_
    show Submodule.map Mr.real (Submodule.comap Mr.real _) = _
    rw [Submodule.map_comap_eq, Mr.real_range]
    exact inf_eq_right.2 inf_le_right
  have hxm : x ∈ ⨆ i, p i := htop ▸ Submodule.mem_top
  let ℓ : D.what₂.Mt μ j →+ ℂ := AddMonoidHom.mk' (fun F => inner ℂ F x) (fun a b => inner_add_left a b x)
  obtain ⟨i, F, hF, hne⟩ := exists_ne_of_mem_iSup' p ℓ hxm (by
    show inner ℂ x x ≠ 0
    exact inner_self_ne_zero.2 hx)
  exact ⟨S i, hirr i, F, (Submodule.mem_inf.1 hF).1, hne⟩

end GlobalTheory.LiftRefIrr


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPosition
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPosition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie.PlacesGood

variable {D : D7}

theorem over_pde_of_mem_pD (i : D.ntw.Tw) {P : Pl D.host.E} (hP : P ∈ D.ntw.pD i) :
    ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  have h : P ∈ (D.ntw.pD i : Set (Pl D.host.E)) := hP
  rw [D.ntw.pD_eq i] at h
  split_ifs at h
  · exact ⟨_, Or.inr rfl, h⟩
  · exact ⟨_, Or.inl rfl, h⟩

theorem natCast_mem_of_conj {P P' : Pl D.host.E} (h : IsConjPl D.host P P') {n : ℕ}
    (hn : ((n : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : ((n : ℕ) : 𝓞 D.host.E) ∈ P'.asIdeal :=
  (h (n : 𝓞 D.host.E) (n : 𝓞 D.host.E) (by simp)).1 hn

theorem splitsC_of_primesOver {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E) :
    GlobalTheory.Mem.Chr.SplitsC D.host.E p := by
  have e := GlobalTheory.HostSplit.ncard_placesOver D.host.E hp
  rw [h] at e
  exact e

theorem coprime_of_level {p : ℕ} (hp : p.Prime) (hs : p ∉ D.host.small) (hq : p ≠ D.host.q) (hl : p ∈ D.host.levelPrimes) :
    Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p :=
  Nat.Coprime.mul_left (UpperTheory.Ram.coprime_QSq D.host hp hs hq)
    (D.host.ccK_coprime p (by simp [hl]))

theorem count_AA_eq_zero {P : Pl D.host.E} {p : ℕ} (hc : Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p)
    (hp : ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : FractionalIdeal.count D.host.E P D.host.AA = 0 :=
  GlobalTheory.HalfCompare.primeToAA_of_not_mem (GlobalTheory.HalfCompare.not_mem_of_coprime P hc hp)

theorem placesOK : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (μ0 : T), Rl.toLevCh.Is μ0 → (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧ (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E → D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → PlacesOK Rl.Pg (half ch (D.ntw.pD i)) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl μ0 hL hsp hq i ch hch
  classical
  have hPg : ∀ P ∈ Rl.Pg, ∃ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal ∧ Rl.C.P.Div k P := fun P hP => by
    obtain ⟨k, hk⟩ := (hL.Pg P).1 hP
    exact ⟨k, GlobalTheory.Mem.TypePl.div_over Rl.C.P hk, hk⟩
  have hQ : ∀ P ∈ half ch (D.ntw.pD i), ∃ p, (p = D.host.pde ∨ p = D.host.pde') ∧ ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
    fun P hP => over_pde_of_mem_pD i (mem_half.1 hP).1
  have hsm : ∀ p : ℕ, p.Prime → GlobalTheory.Mem.Chr.SplitsC D.host.E p → p ∉ D.host.small := fun p hp h hs =>
    UpperTheory.Ram.not_dvd_condN_of_unram D.host hp (fun w hw => (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p hp h w hw).2.1)
      (((Nat.dvd_of_mem_primeFactors hs).mul_right _).mul_right _)
  have hpp : ∀ p, (p = D.host.pde ∨ p = D.host.pde') → p.Prime ∧ GlobalTheory.Mem.Chr.SplitsC D.host.E p ∧
      Nat.Coprime (GlobalTheory.HalfCompare.badInt D) p ∧ ∀ k, p ≠ D.host.g k := by
    rintro p (rfl | rfl)
    · exact ⟨D.host.pde_prime, splitsC_of_primesOver D.host.pde_prime hsp.1,
        coprime_of_level D.host.pde_prime (hsm _ D.host.pde_prime (splitsC_of_primesOver D.host.pde_prime hsp.1)) hq.1 D.host.pde_level.1, fun k => (D.host.pde_ne_g k).1⟩
    · exact ⟨D.host.pde'_prime, splitsC_of_primesOver D.host.pde'_prime hsp.2,
        coprime_of_level D.host.pde'_prime (hsm _ D.host.pde'_prime (splitsC_of_primesOver D.host.pde'_prime hsp.2)) hq.2 D.host.pde_level.2, fun k => (D.host.pde_ne_g k).2⟩
  refine ⟨⟨Rl.Pg ∪ half ch (D.ntw.pD i), Finset.subset_union_left, Finset.subset_union_right, ?_⟩, ?_, ?_⟩
  · refine GlobalTheory.UnivGood.splitSet_of_split (fun P hP => ?_) fun P hP P' hP' hc => ?_
    · rcases Finset.mem_union.1 hP with hP | hP
      · obtain ⟨k, hk, -⟩ := hPg P hP
        exact (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) P hk).2.2.1
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        exact (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1
    · rcases Finset.mem_union.1 hP with hP | hP <;> rcases Finset.mem_union.1 hP' with hP' | hP'
      · obtain ⟨k, hk, hd⟩ := hPg P hP
        obtain ⟨k', hk', hd'⟩ := hPg P' hP'
        have e := GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (D.host.g_prime k) (D.host.g_prime k') (natCast_mem_of_conj hc hk) hk'
        have hkk : k = k' := by
          have := D.host.g_ne
          fin_cases k <;> fin_cases k' <;> simp_all
        subst hkk
        exact GlobalTheory.Mem.TypePl.not_isConjPl Rl.C.P (D.nd.g_split k) hd hd' hc
      · obtain ⟨k, hk, -⟩ := hPg P hP
        obtain ⟨p, hp, hm⟩ := hQ P' hP'
        exact (hpp p hp).2.2.2 k
          (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) hm (natCast_mem_of_conj hc hk))
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        obtain ⟨k, hk, -⟩ := hPg P' hP'
        exact (hpp p hp).2.2.2 k
          (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' (hpp p hp).1 (D.host.g_prime k) (natCast_mem_of_conj hc hm) hk)
      · obtain ⟨p, hp, hm⟩ := hQ P hP
        have hs := (GlobalTheory.Mem.Chr.splitsC_main D.R D.host p (hpp p hp).1 (hpp p hp).2.1 P hm).2.2.1
        exact (hch.pair P P' hc (ne_of_split hs hc)).1 (mem_half.1 hP).2 (mem_half.1 hP').2
  · refine Finset.disjoint_left.2 fun P hP hP' => ?_
    obtain ⟨k, hk, -⟩ := hPg P hP
    obtain ⟨p, hp, hm⟩ := hQ P hP'
    exact (hpp p hp).2.2.2 k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P (hpp p hp).1 (D.host.g_prime k) hm hk)
  · intro PP hPP PP' hPP'
    have hmem : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ PP'.asIdeal := fun n hn => by
      rcases hPP' with rfl | hc
      · exact hn
      · exact GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc hn
    rcases hPP with hPP | hPP
    · obtain ⟨k, hk, -⟩ := hPg PP hPP
      exact count_AA_eq_zero (GlobalTheory.CoverHalf.g_coprime D k).symm (hmem _ hk)
    · obtain ⟨p, hp, hm⟩ := hQ PP hPP
      exact count_AA_eq_zero (hpp p hp).2.2.1 (hmem _ hm)

end GlobalTheory.SeriesTie.PlacesGood

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlacesTwistPlacesGoodPositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePlaces_twistPlaces_goodPosition : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (μ0 : T), Rl.toLevCh.Is μ0 → (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧ (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E → D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q → ∀ (i : D.ntw.Tw) (ch : Set (Pl D.host.E)), IsChoice ch → PlacesOK Rl.Pg (half ch (D.ntw.pD i)) := by
  first | exact @GlobalTheory.SeriesTie.PlacesGood.placesOK | exact GlobalTheory.SeriesTie.PlacesGood.placesOK | (intros; apply GlobalTheory.SeriesTie.PlacesGood.placesOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteComplexFormsEqTwistComplexFormsFockModel
section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AutomorphicFormIffRationalLevelLaw
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem exists_finPt {D : D7} (V : HSp D) (x : Bridge.Gf V) : ∃ k ∈ GfC V, finPt V k = x := by
  obtain ⟨hsplit, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨g, hg⟩ := x.2
  obtain ⟨a, ha, k, hk, rfl⟩ := hsplit g
  have ha' : finHom V a = 1 := ha
  refine ⟨k, hk, Subtype.ext ?_⟩
  rw [MonoidHom.coe_rangeRestrict, ← hg, map_mul, ha', one_mul]

private theorem lev_iff {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : GA D S →* Module.End ℂ W) (hρ : ∀ h ∈ GfC S, ρ h = 1) (J : Set (GA D S)) (χ : GA D S → ℂ)
    (hJ : ∀ k, (k ∈ J ↔ k ∈ Lev.levG S B.F.βS (B.levS ψ)) ∧
      (k ∈ Lev.levG S B.F.βS (B.levS ψ) → χ k = Lev.levChi S B.F.βS (B.levS ψ) k))
    (f : Bridge.Gf S → W) (F : GA D S → W) (hF : ∀ g, F g = ρ g⁻¹ (f (finPt S g))) :
    F ∈ RecTie.levSubV S W J χ ↔
      ∀ (h : Bridge.Gf S) (k : B.levJ ψ), f (h * (k : Bridge.Gf S)) = ((B.levLam ψ k : ℂˣ) : ℂ) • f h := by
  change (∀ k ∈ J, ∀ g, F (g * k) = χ k • F g) ↔ _
  constructor
  · rintro H h ⟨k, hk⟩
    obtain ⟨h, hh, rfl⟩ := exists_finPt S h
    obtain ⟨k, hk', rfl⟩ := exists_finPt S k
    have hkG := (B.finPt_mem_levJ ψ hk').1 hk
    have := H k ((hJ k).1.2 hkG) h
    rw [hF, hF, hρ _ ((GfC S).inv_mem hh), hρ _ ((GfC S).inv_mem ((GfC S).mul_mem hh hk')), (hJ k).2 hkG,
      ← B.levLam_finPt ψ hk, finPt, map_mul] at this
    exact this
  · intro H k hk g
    have hkG := (hJ k).1.1 hk
    have hk' : k ∈ GfC S := hkG.1
    have hkJ := (B.finPt_mem_levJ ψ hk').2 hkG
    have h1 := H (finPt S g) ⟨_, hkJ⟩
    have h2 : finPt S (g * k) = finPt S g * finPt S k := map_mul _ _ _
    rw [hF, hF, h2, h1, (hJ k).2 hkG, ← B.levLam_finPt ψ hkJ, mul_inv_rev, map_mul ρ, hρ _ ((GfC S).inv_mem hk'),
      Module.End.mul_apply, Module.End.one_apply]
    exact LinearMap.map_smul (ρ g⁻¹) _ _

private theorem adForms_left {G Γ W : Type} [Group G] [Group Γ] {ι : Γ →* G} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : F ∈ Bridge.AdForms ι ρ J χ) (γ : Γ) (g : G) : F (ι γ * g) = ρ γ (F g) := by
  simpa using hF γ g 1

private theorem law_right {G A W : Type} [Group G] [Group A] {Γ : Subgroup A} {ι : Γ →* G} [AddCommGroup W] [Module ℂ W]
    {ρ : A →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * (k : G)) = ((χ k : ℂˣ) : ℂ) • ρ (γ : A) (F h)) (h : G) (k : J) :
    F (h * (k : G)) = ((χ k : ℂˣ) : ℂ) • F h := by
  simpa using hF 1 h k

theorem _root_.UpperTheory.KN.automorphic_form_iff_rational_level_law :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ f : Bridge.Gf (Vc D j) → (X.R.cV j).W, (∃ x, (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x) = f) ↔
      ∀ (γ : Formalism.L2.Theta.GQ (Vc D j)) (h : Bridge.Gf (Vc D j)) (k : (baseOf Z c w j).levJ (twVia Z.ρ ι)),
        f (Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j))) = (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) (f h) := by
  intro D X X0 Y S YS Z c w j H ι hι f
  have hrange := (X.char.models.HV j (Y.tupT (D.what₂.muTw w))).2.1
  have key := fun y : (X.R.HV j (Y.tupT (D.what₂.muTw w))).H =>
    lev_iff (baseOf Z c w j) (twVia Z.ρ ι) (X.R.cV j).ρ (X.char.models.cV j).1 _ _
      (UpperTheory.KN.levS_iff_levG_and_levChi_eq D X X0 Y S YS Z c w j H ι hι) ((X.R.HV j (Y.tupT (D.what₂.muTw w))).e y)
      (X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) y) (fun _ => rfl)
  constructor
  · rintro ⟨x, rfl⟩ γ h k
    have h1 := (key (formOf Y (used_of_tw H.tw) j x)).1 (by
      rw [extV_formOf]
      exact (Y.IL.jMt _ (used_of_tw H.tw) j x).2.2)
    have h2 := adForms_left (hrange.le (LinearMap.mem_range_self _ (formOf Y (used_of_tw H.tw) j x))) γ h
    exact (h1 _ k).trans (congrArg (fun v => (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) • v) h2)
  · intro hf
    have hA : f ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (Y.tupT (D.what₂.muTw w)))).J
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (Y.tupT (D.what₂.muTw w)))).χ := by
      intro γ h k
      obtain ⟨hk, hχ⟩ := UpperTheory.KN.levEnv_level_subgroup_le_levJ_and_character_eq D X X0 Y S YS Z c w j H ι hι k
      exact (hf γ h ⟨k, hk⟩).trans (congrArg (fun u : ℂˣ => (u : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) (f h)) hχ)
    obtain ⟨y, rfl⟩ := hrange.ge hA
    have h1 := (key y).2 (law_right hf)
    refine ⟨(Y.IL.jMt _ (used_of_tw H.tw) j).symm ⟨X.R.toRealDat.extV j _ y, ⟨y, rfl⟩, h1⟩, congrArg _ ?_⟩
    apply Y.hinj j
    rw [extV_formOf]
    exact congrArg Subtype.val ((Y.IL.jMt _ (used_of_tw H.tw) j).apply_symm_apply _)
end

section -- merged from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IoPTprodIntertwinesAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

theorem _root_.UpperTheory.KN.ioP_tprod_intertwines_action :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ (g : GA D (Vc D j)) (v : (X.R.cV j).W), (baseOf Z c w j).act g (X.R.ioP j (PiTensorProduct.tprod ℂ u) v) = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.cV j).ρ g v) := by
  intro D X X0 Y S YS Z c w j H ι hι u _ g v
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 := ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo := GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  obtain ⟨hg, -, -⟩ := GlobalTheory.PlaceRead.twVia_good D c w Z.ρ Z.good H.ok j ι
  have ht := H.tup ι hι
  exact (GlobalTheory.CoefActIo.act_ioP hC hB hBo hg ht).2 g _ v
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem eigen_law_absolute {M G Γ A V P : Type*} {J : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup P] [Module ℂ P] (io : V →ₗ[ℂ] P) (hinj : Function.Injective io) (val : Submodule ℂ P)
    (hran : LinearMap.range io = val) (act : A → P → P) (ρ : A → V → V) (hact : ∀ g v, act g (io v) = io (ρ g v))
    (E : M → G → V) (mv : Γ → G → J → G) (a : Γ → A) (lam : J → ℂ)
    (hlaw : ∀ f : G → V, (∃ x, E x = f) ↔ ∀ γ h k, f (mv γ h k) = lam k • ρ (a γ) (f h)) (F : G → P) :
    (∃ x, ∀ h, io (E x h) = F h) ↔ (∀ h, F h ∈ val) ∧ ∀ γ h k, F (mv γ h k) = lam k • act (a γ) (F h) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨fun h => ?_, fun γ h k => ?_⟩
    · rw [← hran, ← hx]
      exact ⟨_, rfl⟩
    · rw [← hx, ← hx, (hlaw _).1 ⟨x, rfl⟩ γ h k, map_smul, hact]
  · rintro ⟨hv, hl⟩
    subst hran
    choose f hf using hv
    obtain ⟨x, hx⟩ := (hlaw f).2 fun γ h k => hinj (by rw [map_smul, ← hact, hf, hf, hl])
    exact ⟨x, fun h => by rw [hx, hf]⟩

theorem _root_.GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel : ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
  ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
  ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u → Function.Injective (fockOf Y (used_of_tw H.tw) j u) ∧
  LinearMap.range (fockOf Y (used_of_tw H.tw) j u) = (baseOf Z c w j).formsC (twVia Z.ρ ι) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu
  obtain ⟨hinj, hran⟩ := UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u hu
  have hact := UpperTheory.KN.ioP_tprod_intertwines_action D X X0 Y S YS Z c w j H ι hι u hu
  have hlaw := UpperTheory.KN.automorphic_form_iff_rational_level_law D X X0 Y S YS Z c w j H ι hι
  refine ⟨?_, Submodule.ext fun F => ?_⟩
  · intro x y hxy
    have h1 : (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x) =
        (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j y) :=
      funext fun h => hinj (congrFun hxy h)
    have h2 : X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j x) =
        X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) (formOf Y (used_of_tw H.tw) j y) := by
      have h3 := (X.char.models.HV j (Y.tupT (D.what₂.muTw w))).1 h1
      rw [h3]
    rw [extV_formOf, extV_formOf] at h2
    exact (Y.IL.jMt _ (used_of_tw H.tw) j).injective (Subtype.ext h2)
  · have key := eigen_law_absolute (X.R.ioP j (PiTensorProduct.tprod ℂ u)) hinj _ hran (fun g P => (baseOf Z c w j).act g P)
      (fun g v => (X.R.cV j).ρ g v) hact
      (fun x => (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x))
      (fun (γ : Formalism.L2.Theta.GQ (Vc D j)) (h : Bridge.Gf (Vc D j)) (k : (baseOf Z c w j).levJ (twVia Z.ρ ι)) =>
        Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j))) (fun γ => (γ : GA D (Vc D j)))
      (fun k => (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ)) hlaw F
    refine Iff.trans ?_ (key.trans (Base.mem_formsC _).symm)
    exact ⟨fun ⟨x, hx⟩ => ⟨x, fun h => congrFun hx h⟩, fun ⟨x, hx⟩ => ⟨x, funext hx⟩⟩
end
