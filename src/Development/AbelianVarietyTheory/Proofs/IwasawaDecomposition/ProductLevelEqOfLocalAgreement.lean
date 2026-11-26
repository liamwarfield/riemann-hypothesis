module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftAtReferenceTupleOverEnlargedBase

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductLevelEqOfLocalAgreement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductLevelEqOfLocalAgreement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LevCmp

section Glue

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def compHom (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    GAf L n →* GL (Fin n) (L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L)) :=
  (Matrix.GeneralLinearGroup.map (compAt L v)).comp (ReciprocityTheory.Aut.GA L n).subtype

theorem compHom_eq_one_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x : GAf L n) :
    compHom v x = 1 ↔ (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = 1 := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

theorem compHom_eq_iff (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n) :
    compHom v x = compHom v y ↔
      (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) = (y.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [compHom] using this
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    simpa [compHom] using this

theorem mem_of_agree {J J' : Subgroup (GAf L n)} {χ : J →* ℂˣ} {χ' : J' →* ℂˣ}
    {S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (hS : S.Finite) (hJ : NG.IsProdLevel J)
    (hO : NG.HypOutside J χ S) (hO' : NG.HypOutside J' χ' S)
    (hloc : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩)
    (κ : GAf L n) (hκ : κ ∈ J) : ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by

  have hone : ∀ u κ, TrivOutside {u} κ → ∀ hκ : κ ∈ J, ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro u κ hu hκ
    by_cases huS : u ∈ S
    · obtain ⟨h1, h2⟩ := hloc u huS κ hu
      exact ⟨h1.mp hκ, h2 hκ (h1.mp hκ)⟩
    · have ht : TrivOutside Sᶜ κ := by
        intro v hv
        apply hu v
        rintro rfl
        exact huS (not_not.mp hv)
      obtain ⟨a1, a2⟩ := hO κ ht
      obtain ⟨b1, b2⟩ := hO' κ ht
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
  have key : ∀ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), ∀ κ (hκ : κ ∈ J),
      TrivOutside (Sᶜ ∪ (T : Set _)) κ → ∃ h' : κ ∈ J', χ ⟨κ, hκ⟩ = χ' ⟨κ, h'⟩ := by
    intro T
    classical
    induction T using Finset.induction_on with
    | empty =>
      intro κ hκ ht
      have ht' : TrivOutside Sᶜ κ := by
        intro v hv
        exact ht v (by simpa using hv)
      obtain ⟨a1, a2⟩ := hO κ ht'
      obtain ⟨b1, b2⟩ := hO' κ ht'
      have h' : κ ∈ J' := b1.mpr (a1.mp hκ)
      exact ⟨h', by rw [a2 hκ, b2 h']⟩
    | insert u T huT ih =>
      intro κ hκ ht
      obtain ⟨κu, hκu, hu, hcomp⟩ := hJ κ hκ u
      have hκ1 : κ * κu⁻¹ ∈ J := J.mul_mem hκ (J.inv_mem hκu)
      have ht1 : TrivOutside (Sᶜ ∪ (T : Set _)) (κ * κu⁻¹) := by
        intro v hv
        rw [← compHom_eq_one_iff, map_mul, map_inv, mul_inv_eq_one]
        by_cases hvu : v = u
        · subst hvu
          exact ((compHom_eq_iff v κ κu).mpr hcomp.symm)
        · have e1 : compHom v κ = 1 := by
            rw [compHom_eq_one_iff]
            apply ht v
            simp only [Finset.coe_insert, Set.mem_union, Set.mem_insert_iff, not_or] at hv ⊢
            exact ⟨hv.1, hvu, hv.2⟩
          have e2 : compHom v κu = 1 := by
            rw [compHom_eq_one_iff]
            exact hu v (by simpa using hvu)
          rw [e1, e2]
      obtain ⟨h1', e1⟩ := ih (κ * κu⁻¹) hκ1 ht1
      obtain ⟨h2', e2⟩ := hone u κu hu hκu
      have hprod : κ = κ * κu⁻¹ * κu := by group
      have h' : κ ∈ J' := by
        rw [hprod]; exact J'.mul_mem h1' h2'
      refine ⟨h', ?_⟩
      have s1 : (⟨κ, hκ⟩ : J) = ⟨κ * κu⁻¹, hκ1⟩ * ⟨κu, hκu⟩ := Subtype.ext hprod
      have s2 : (⟨κ, h'⟩ : J') = ⟨κ * κu⁻¹, h1'⟩ * ⟨κu, h2'⟩ := Subtype.ext hprod
      rw [s1, s2, map_mul, map_mul, e1, e2]
  apply key hS.toFinset κ hκ
  intro v hv
  exfalso
  apply hv
  by_cases h : v ∈ S
  · right; simpa using h
  · left; exact h

theorem levEq_of_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), S.Finite → NG.IsProdLevel J → NG.IsProdLevel J' → NG.HypOutside J χ S → NG.HypOutside J' χ' S → (∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩) → LevEq J χ J' χ' := by
  intro L _ _ _ n J J' χ χ' S hS hJ hJ' hO hO' hloc
  have hloc' : ∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J' ↔ κ ∈ J) ∧ ∀ (h : κ ∈ J') (h' : κ ∈ J), χ' ⟨κ, h⟩ = χ ⟨κ, h'⟩ :=
    fun u hu κ hκ => ⟨(hloc u hu κ hκ).1.symm, fun h h' => ((hloc u hu κ hκ).2 h' h).symm⟩
  refine ⟨le_antisymm (fun κ hκ => (mem_of_agree hS hJ hO hO' hloc κ hκ).1)
    (fun κ hκ => (mem_of_agree hS hJ' hO' hO hloc' κ hκ).1), fun κ h h' => ?_⟩
  obtain ⟨h'', e⟩ := mem_of_agree hS hJ hO hO' hloc κ h
  exact e

end Glue

end GlobalTheory.LevCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProductLevelEqOfLocalAgreementStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productLevel_eq_of_local_agreement : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), S.Finite → NG.IsProdLevel J → NG.IsProdLevel J' → NG.HypOutside J χ S → NG.HypOutside J' χ' S → (∀ u ∈ S, ∀ κ, TrivOutside {u} κ → (κ ∈ J ↔ κ ∈ J') ∧ ∀ (h : κ ∈ J) (h' : κ ∈ J'), χ ⟨κ, h⟩ = χ' ⟨κ, h'⟩) → LevEq J χ J' χ' := by
  first | exact @GlobalTheory.LevCmp.levEq_of_agree | exact GlobalTheory.LevCmp.levEq_of_agree | (intros; apply GlobalTheory.LevCmp.levEq_of_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitCharacterNontrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitCharacterNontrivial
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.CompRamified

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem le_exp_neg_one_of_lt_one' {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · exact zero_le'
  · rw [← WithZero.exp_log hx0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem exists_int_locK_ne (χ : HChar L) (t : SplitPlace L) (ht : χ.TameAt t.w) (hr : ¬ χ.UnrAt t.w) :
    ∃ b : 𝓞 (maximalRealSubfield L), b ∉ t.v.asIdeal ∧ ∃ k : Lˣ,
      (k : L) = ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b : 𝓞 L) : L) ∧ χ.locK t.w k ≠ 1 := by
  classical
  simp only [HChar.UnrAt, not_forall] at hr
  obtain ⟨x, hx, hne⟩ := hr
  have hx' : Valued.v (x : t.w.adicCompletion L) = 1 := hx
  obtain ⟨a, ha⟩ := adic_exists_approx t.w (x : t.w.adicCompletion L) (le_of_eq hx')
  obtain ⟨b, hb⟩ := adic_exists_approx t.v (t.i (a : L)) (t.split_le_one a)
  set c : 𝓞 L := algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) b with hcdef
  have hac : a - c ∈ t.w.asIdeal := by
    show a - c ∈ t.ideal
    rw [t.split_mem_ideal]
    have e : t.i ((c : 𝓞 L) : L) =
        algebraMap (𝓞 (maximalRealSubfield L)) (t.v.adicCompletion (maximalRealSubfield L)) b := by
      rw [hcdef, split_coe_algebraMap, AlgHom.commutes]; rfl
    have e2 : ((a - c : 𝓞 L) : L) = (a : L) - (c : L) := by push_cast; rfl
    rw [e2, map_sub, e]
    exact hb
  have hval : ∀ z : 𝓞 L, Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) z) = t.w.valuation L (z : L) := fun z => by
    exact adic_valued_algebraMap (R := 𝓞 L) (K := L) t.w (z : L)
  have hxc : Valued.v ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) < 1 := by
    have e : (x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c =
        ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ a) + algebraMap (𝓞 L) _ (a - c) := by
      rw [map_sub]; ring
    rw [e]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha ?_)
    rw [hval]
    exact (t.w.valuation_lt_one_iff_mem (a - c)).2 hac
  have hc1 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) = 1 := by
    have e : algebraMap (𝓞 L) (t.w.adicCompletion L) c =
        (x : t.w.adicCompletion L) - ((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) := by ring
    rw [e, Valuation.map_sub_eq_of_lt_left _ (by rw [hx']; exact hxc)]
    exact hx'
  have hbv : b ∉ t.v.asIdeal := by
    intro hm
    have h1 := (t.split_alg_mem b).2 hm
    have h2 : Valued.v (algebraMap (𝓞 L) (t.w.adicCompletion L) c) < 1 := by
      rw [hval]; exact (t.w.valuation_lt_one_iff_mem c).2 h1
    rw [hc1] at h2
    exact lt_irrefl _ h2
  have hc0 : (c : L) ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 L) (t.w.adicCompletion L) c = 0 := by
      show algebraMap L (t.w.adicCompletion L) (c : L) = 0
      rw [h0, map_zero]
    rw [this, map_zero] at hc1
    exact zero_ne_one hc1
  refine ⟨b, hbv, Units.mk0 (c : L) hc0, rfl, ?_⟩
  intro h1
  apply hne
  set y : (t.w.adicCompletion L)ˣ := atFin t.w (Units.mk0 (c : L) hc0) with hydef
  have hy : (y : t.w.adicCompletion L) = algebraMap (𝓞 L) (t.w.adicCompletion L) c := rfl
  have hu : IsUnitAt t.w (y * x⁻¹) := by
    show Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ)) : t.w.adicCompletion L) = 1
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hy, hc1, hx', inv_one, mul_one]
  have hsub : Valued.v (((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    have e : ((y * x⁻¹ : (t.w.adicCompletion L)ˣ) : t.w.adicCompletion L) - 1 =
        -((x : t.w.adicCompletion L) - algebraMap (𝓞 L) _ c) * (x : t.w.adicCompletion L)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hy]
      field_simp
      ring
    rw [e, map_mul, Valuation.map_neg, map_inv₀, hx', inv_one, mul_one]
    exact le_exp_neg_one_of_lt_one' hxc
  have h2 := ht (y * x⁻¹) hu hsub
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [← h2]
  exact h1

end Gen

end GlobalTheory.CompRamified


open GlobalTheory.CompRamified in
theorem GlobalTheory.CompRamified.exists_unit_ne_one : ∀ (D : D7) (cf : CharFrame D) (j : Fin D.R.m) (ξH : HChar D.host.E) (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), ξH.TrivOn D.host.F → (∀ u, ξH.TameAt u) → s.v ∈ qPl D (cf.mu0 j * ξH) → NG.IsCompAt (cf.mu0 j * ξH) s ξ → ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1 := by
  classical
  intro D cf j ξH s ξ htr hta hq hc
  set η := cf.mu0 j * ξH with hη
  have htame : ∀ u, η.TameAt u := fun u x hx h1 => by
    change (cf.mu0 j).loc u x * ξH.loc u x = 1
    rw [(cf.isMu0 j).tame u x hx h1, hta u x hx h1, one_mul]
  have htriv : ∀ k : (D.host.F)ˣ, ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, η.locK P (upF D.host.F k) = 1 := fun k => by
    have h1 := (cf.isMu0 j).triv.1 s.v k
    have h2 := htr.1 s.v k
    rw [GlobalTheory.GalToHecke.resFin_eq] at h1 h2
    rw [hη]
    show ∏ P ∈ aboveF (L := D.host.E) D.host.F s.v, ((cf.mu0 j).locK P (upF D.host.F k) * ξH.locK P (upF D.host.F k)) = 1
    rw [Finset.prod_mul_distrib, h1, h2, one_mul]
  obtain ⟨-, w, hw, hram⟩ := hq
  have key : ∃ b : 𝓞 (maximalRealSubfield D.host.E), b ∉ s.v.asIdeal ∧ ∃ k : (D.host.E)ˣ,
      (k : D.host.E) = ((algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) b : 𝓞 D.host.E) : D.host.E) ∧
        η.locK w k ≠ 1 := by
    rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw with e | e
    · subst e
      exact exists_int_locK_ne η s (htame _) hram
    · have e2 := (GlobalTheory.TypeTame.conjSP_w_of_isConjPl D s w e).1
      have h := exists_int_locK_ne η (GlobalTheory.TypeTame.conjSP s) (e2 ▸ htame _) (e2 ▸ hram)
      rw [e2] at h
      exact h
  obtain ⟨b, hbv, k, hk, hne⟩ := key
  have hb0 : ((b : maximalRealSubfield D.host.E) : D.host.E) ≠ 0 := by
    intro h0
    apply hbv
    have : (b : maximalRealSubfield D.host.E) = 0 := by exact_mod_cast h0
    have : b = 0 := RingOfIntegers.coe_eq_zero_iff.mp this
    rw [this]; exact s.v.asIdeal.zero_mem
  have hF0 : (b : maximalRealSubfield D.host.E) ≠ 0 := fun h => hb0 (by rw [h]; rfl)
  set f : (D.host.F)ˣ := Units.mk0 (b : maximalRealSubfield D.host.E) hF0 with hfdef
  have hfk : upF D.host.F f = k := by
    apply Units.ext
    rw [hk]
    rfl
  have hsw : η.locK s.w k ≠ 1 := by
    by_cases e : s.w = w
    · rwa [e]
    have hc' : IsConjPl D.host w s.w := (GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s w hw).resolve_left e
    have hab : aboveF (L := D.host.E) D.host.F s.v = {s.w, w} := by
      ext P
      rw [GlobalTheory.GalToHecke.mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hP
        have hov : NG.OverPl P s.v := by rw [← hP]; rfl
        rcases GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s P hov with e' | e'
        · exact Or.inl e'.symm
        · exact Or.inr (GlobalTheory.HeightCounting.TrueConjLabels.eq_of_isConjPl e' hc')
      · rintro (rfl | rfl)
        · exact HeightOneSpectrum.ext s.w_under
        · exact HeightOneSpectrum.ext hw
    have h := htriv f
    rw [hab, Finset.prod_pair e, hfk] at h
    intro h1
    rw [h1, one_mul] at h
    exact hne h
  refine ⟨Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k, ?_, ?_⟩
  · show Valued.v (s.i (k : D.host.E)) = 1
    rw [hk, s.split_val_alg]
    refine le_antisymm (s.v.valuation_le_one b) (not_lt.1 fun h => hbv ((s.v.valuation_lt_one_iff_mem b).1 h))
  · rw [hc.2 k]
    exact hsw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalUnitCharacterNontrivialStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_unit_character_nontrivial : ∀ (D : D7) (cf : CharFrame D) (j : Fin D.R.m) (ξH : HChar D.host.E) (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), ξH.TrivOn D.host.F → (∀ u, ξH.TameAt u) → s.v ∈ qPl D (cf.mu0 j * ξH) → NG.IsCompAt (cf.mu0 j * ξH) s ξ → ∃ a : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ, Valued.v (a : s.v.adicCompletion (maximalRealSubfield D.host.E)) = 1 ∧ ξ a ≠ 1 := by
  first | exact @GlobalTheory.CompRamified.exists_unit_ne_one | exact GlobalTheory.CompRamified.exists_unit_ne_one | (intros; apply GlobalTheory.CompRamified.exists_unit_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReferenceTupleHilbertModelDefiniteFormsEnlarged
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.ModVExt

section Generic

variable {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]

private theorem is_move (ι : Γ →* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ χ' : J →* ℂˣ) (e : χ' = χ)
    (hρ : ∀ γ x x', inner ℂ (ρ γ x) (ρ γ x') = inner ℂ x x') (hχ : ∀ k, ‖(χ k : ℂ)‖ = 1)
    {I I' : Type} [Fintype I] [Fintype I'] (y : I → G) (y' : I' → G) (hy : Bridge.IsReps ι J y) (hy' : Bridge.IsReps ι J y')
    (H : HMod (G → W)) (h : H.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J y)) :
    H.Is (Bridge.AdForms ι ρ J χ') (Bridge.adInner ι J y') := by
  subst e
  refine ⟨h.1, h.2.1, fun x x' => ?_⟩
  rw [h.2.2]
  exact Bridge.adInnerIndep_holds ι ρ J χ' hρ hχ I I' y y' hy hy' _ (h.2.1 ▸ LinearMap.mem_range_self _ x) _
    (h.2.1 ▸ LinearMap.mem_range_self _ x')

private theorem norm_units_of_finite {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (u : H) : ‖((χ u : ℂˣ) : ℂ)‖ = 1 := by
  have hfin := Fintype.ofFinite H
  have h1 : (χ u) ^ (Fintype.card H) = 1 := by rw [← map_pow, pow_card_eq_one, map_one]
  have h2 : ‖((χ u : ℂˣ) : ℂ)‖ ^ (Fintype.card H) = 1 := by
    rw [← norm_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h2

end Generic

section Free

variable {D : D7}

private theorem norm_chi (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ‖((levEnv V β L).χ k : ℂ)‖ = 1 := by
  have hf : ∀ PP : Pl D.host.E, Finite (kP PP)ˣ := fun PP => Finite.of_injective _ Units.val_injective
  show ‖((levFn β (flag1L L) (Formalism.UG.bc (swapAE D) k.1.1) : ℂˣ) : ℂ)‖ = 1
  generalize Formalism.UG.bc (swapAE D) k.1.1 = x
  unfold levFn
  simp only [Units.val_mul, norm_mul, Units.coe_prod, norm_prod]
  rw [show ext1 (flag1L L).P.H (flag1L L).P.chi (rTup β (flag1L L) x) = 1 from subgroupCharExtension_one_apply _ _]
  simp [norm_units_of_finite]

private def datC (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  datY _ D.R.r D.R.t 1 hr Pg Q (LevelP.triv _ _ _) (fun _ => chi) xi Frm.A

private def MV (V : HSp D) (c : CoefA V) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    {I : Type} [Fintype I] (y : I → Bridge.Gf V) (H : HMod (Bridge.Gf V → c.W)) (ν : Measure (GA D V)) (fd : Set (GA D V)) : Prop :=
  H.Is (Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) (Bridge.adInner (Bridge.ratF V) (levEnv V β L).J y) ∧
  IsMeasDef V (lev D.sp.cm V.gram β L) ν fd

private def RP (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    {I : Type} (y : I → Bridge.Gf V) : Prop := Bridge.IsReps (Bridge.ratF V) (levEnv V β L).J y

private theorem mv_move (V : HSp D) (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (hr : D.R.r ≤ V.rank)
    (Pg : Finset (Pl D.host.E)) (chi xi chi' xi' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (hchi : ∀ PP ∈ Pg, chi' PP = chi PP)
    {I I' : Type} [Fintype I] [Fintype I'] (y : I → Bridge.Gf V) (y' : I' → Bridge.Gf V)
    (hy : RP V β (datC V hr Pg ∅ chi xi) y) (hy' : RP V β (datC V hr Pg ∅ chi' xi') y')
    (H : HMod (Bridge.Gf V → c.W)) (ν : Measure (GA D V)) (fd : Set (GA D V))
    (h : MV V c β (datC V hr Pg ∅ chi xi) y H ν fd) : MV V c β (datC V hr Pg ∅ chi' xi') y' H ν fd := by
  refine ⟨?_, h.2⟩
  refine is_move (Bridge.ratF V) c.coef.ρ (levEnv V β (datC V hr Pg ∅ chi xi)).J _ (levEnv V β (datC V hr Pg ∅ chi' xi')).χ ?_
    (fun γ => hc.2.1 γ.1) (norm_chi V β _) y y' hy hy' H h.1
  ext1 k
  show levFn β (flag1L (datC V hr Pg ∅ chi' xi')) (Formalism.UG.bc (swapAE D) k.1.1) =
    levFn β (flag1L (datC V hr Pg ∅ chi xi)) (Formalism.UG.bc (swapAE D) k.1.1)
  generalize Formalism.UG.bc (swapAE D) k.1.1 = x
  unfold levFn
  congr 1
  congr 1
  refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c _ => ?_
  show (chi' PP)⁻¹ _ = (chi PP)⁻¹ _
  rw [hchi PP hP]
  rfl

end Free

section Comparison₂

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

private theorem mv_of (hP : B'.toPre = B.toPre) {V : HSp a.D} {V' : HSp a'.D} (hV : HEq V' V) {c : CoefA V} {c' : CoefA V'}
    (c1 : HEq c'.W c.W) (c2 : HEq c'.ρ c.ρ) (c3 : HEq c'.nW c.nW) (c4 : HEq c'.iW c.iW) (hc : c.Is)
    {β : GL (Fin V.rank) (Lev.EAf a.D)} {β' : GL (Fin V'.rank) (Lev.EAf a'.D)} (hβ : HEq β' β)
    (hr : a.D.R.r ≤ V.rank) (hr' : a'.D.R.r ≤ V'.rank)
    {Pg Q : Finset (Pl a.D.host.E)} {Pg' Q' : Finset (Pl a'.D.host.E)} (hPg : HEq Pg' Pg) (hQ : Q = ∅) (hQ' : Q' = ∅)
    {chi xi : ∀ PP : Pl a.D.host.E, (kP PP)ˣ →* ℂˣ} {chi' xi' : ∀ PP : Pl a'.D.host.E, (kP PP)ˣ →* ℂˣ}
    (hchi : ∀ PP' PP, HEq PP' PP → PP ∈ Pg → HEq (chi' PP') (chi PP))
    {I I' : Type} [Fintype I] [Fintype I'] {y : I → Bridge.Gf V} {y' : I' → Bridge.Gf V'}
    (hy : RP V β (datC V hr Pg Q chi xi) y) (hy' : RP V' β' (datC V' hr' Pg' Q' chi' xi') y')
    {H H'} (hH : HEq H' H) {ν ν'} (hν : HEq ν' ν) {fd fd'} (hfd : HEq fd' fd)
    (h0 : MV V c β (datC V hr Pg Q chi xi) y H ν fd) : MV V' c' β' (datC V' hr' Pg' Q' chi' xi') y' H' ν' fd' := by
  subst hQ hQ'
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (V')) ((by with_unfolding_all exact ((V) :))) (V') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (V')) (V') (((V))) (((hV)))).symm : _))
  clear (hV)
  subst e))
  obtain ⟨W₁, ρ₁⟩ := c'
  rename_i nW' iW' _
  dsimp only at c1 c2 c3 c4
  ( (
  have e : @Eq (type_of% (W₁)) ((by with_unfolding_all exact ((c.W) :))) (W₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (W₁)) (W₁) (((c.W))) (((c1)))).symm : _))
  clear (c1)
  subst e))
  ( (
  have e : @Eq (type_of% (nW')) ((by with_unfolding_all exact ((c.nW) :))) (nW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (nW')) (nW') (((c.nW))) (((c3)))).symm : _))
  clear (c3)
  subst e))
  ( (
  have e : @Eq (type_of% (iW')) ((by with_unfolding_all exact ((c.iW) :))) (iW') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (iW')) (iW') (((c.iW))) (((c4)))).symm : _))
  clear (c4)
  subst e))
  ( (
  have e : @Eq (type_of% (ρ₁)) ((by with_unfolding_all exact ((c.ρ) :))) (ρ₁) := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ρ₁)) (ρ₁) (((c.ρ))) (((c2)))).symm : _))
  clear (c2)
  subst e))
  ( (
  have e : @Eq (type_of% (β')) ((by with_unfolding_all exact ((β) :))) (β') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (β')) (β') (((β))) (((hβ)))).symm : _))
  clear (hβ)
  subst e))
  ( (
  have e : @Eq (type_of% (Pg')) ((by with_unfolding_all exact ((Pg) :))) (Pg') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (Pg')) (Pg') (((Pg))) (((hPg)))).symm : _))
  clear (hPg)
  subst e))
  ( (
  have e : @Eq (type_of% (H')) ((by with_unfolding_all exact ((H) :))) (H') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (H')) (H') (((H))) (((hH)))).symm : _))
  clear (hH)
  subst e))
  ( (
  have e : @Eq (type_of% (ν')) ((by with_unfolding_all exact ((ν) :))) (ν') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (ν')) (ν') (((ν))) (((hν)))).symm : _))
  clear (hν)
  subst e))
  ( (
  have e : @Eq (type_of% (fd')) ((by with_unfolding_all exact ((fd) :))) (fd') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (fd')) (fd') (((fd))) (((hfd)))).symm : _))
  clear (hfd)
  subst e))
  have e : ∀ PP : Pl a.D.host.E, PP ∈ Pg → HEq (chi' ((by with_unfolding_all exact (PP :)))) (chi PP) :=
    fun PP hm => hchi ((by with_unfolding_all exact (PP :))) PP ((by with_unfolding_all exact ((HEq.refl PP) :))) hm
  exact (by with_unfolding_all exact ((mv_move V c hc β hr Pg chi xi ((by with_unfolding_all exact (chi' :))) ((by with_unfolding_all exact (xi' :))) (fun PP hm => eq_of_heq ((by with_unfolding_all exact ((e PP hm) :)))) y (I' := I') ((by with_unfolding_all exact (y' :))) hy ((by with_unfolding_all exact (hy' :))) H ν fd h0) :))

private theorem beta_heq (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i')
    {β : ∀ i, GL (Fin (Vc a.D i).rank) (Lev.EAf a.D)} {β' : ∀ i, GL (Fin (Vc a'.D i).rank) (Lev.EAf a'.D)} (hβ : HEq β' β) :
    HEq (β' i') (β i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((Fin.ext h : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i') :))
  clear h
  subst e
  ( (
  have e : @Eq (type_of% (β')) ((by with_unfolding_all exact ((β) :))) (β') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (β')) (β') (((β))) (((hβ)))).symm : _))
  clear (hβ)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl (β i)) :))

variable {G G' : Type} [iG : Group G] [Fintype G] [iG' : Group G'] [Fintype G'] {Pl0 T0 Pl0' T0' : Type}
  {A : FamIn a.D.what₂.LL G Pl0 T0 a.D.R.m} {A' : FamIn a'.D.what₂.LL G' Pl0' T0' a'.D.R.m}
  {Ks Ks' : Type} [Field Ks] [NumberField Ks] [Algebra Ks a.D.what₂.LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' a'.D.what₂.LL]
  {R : RealDat a.D A Ks} {R' : RealDat a'.D A' Ks'}

private theorem modV_of (hP : B'.toPre = B.toPre) {i : Fin a.D.R.m} {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') {t : T0} {t' : T0'}
    (hβ : HEq R'.βV R.βV) (hPg : HEq R'.Pg R.Pg) (hQ : R.Q t = ∅) (hQ' : R'.Q t' = ∅)
    (c1 : HEq (R'.cV i').W (R.cV i).W) (c2 : HEq (R'.cV i').ρ (R.cV i).ρ) (c3 : HEq (R'.cV i').nW (R.cV i).nW)
    (c4 : HEq (R'.cV i').iW (R.cV i).iW)
    (hchi : ∀ PP' PP, HEq PP' PP → PP ∈ R.Pg → HEq (R'.chi ((i' : ℕ) + 1) PP') (R.chi ((i : ℕ) + 1) PP))
    (hHV : HEq (R'.HV i' t') (R.HV i t)) (hν : HEq (R'.νV i' t') (R.νV i t)) (hfd : HEq (R'.fdV i' t') (R.fdV i t))
    (hm : R.IsModels) :
    (R'.HV i' t').Is (Bridge.AdForms (Bridge.ratF (Vc a'.D i')) (R'.cV i').coef.ρ (levEnv _ (R'.βV i') (R'.datVt i' t')).J
      (levEnv _ (R'.βV i') (R'.datVt i' t')).χ)
    (Bridge.adInner (Bridge.ratF (Vc a'.D i')) (levEnv _ (R'.βV i') (R'.datVt i' t')).J (R'.B.L i' t').pres.y) ∧
  IsMeasDef (Vc a'.D i') (lev a'.D.sp.cm (Vc a'.D i').gram (R'.βV i') (R'.datVt i' t')) (R'.νV i' t') (R'.fdV i' t') :=
  mv_of hP (LiftExt.vc_heq hP h) c1 c2 c3 c4 (hm.cV i) (beta_heq hP h hβ) (r_le_V i) (r_le_V i') hPg hQ hQ' hchi
    (xi := R.xiR t) (xi' := R'.xiR t') (y := (R.B.L i t).pres.y) (y' := (R'.B.L i' t').pres.y)
    (R.B.L i t).pres.reps (R'.B.L i' t').pres.reps hHV hν hfd ⟨hm.HV i t, hm.νV i t⟩

end Comparison₂

end GlobalTheory.Mem.R3.Rw.ModVExt

end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.referenceTuple_hilbertModel_definiteForms_enlarged : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → R'.toRealDat.Pre0 (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).lv2 → RSide z Wt' R' → LevSame z Wt' R' → ModVAt R'.toRealDat (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' Wt'))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE _ hS hL i'
  letI := z.alg
  have hP : B'.toPre = B.toPre := hE.1
  have hm := LiftExt.m_eq (a := Z) (a' := Z') hP
  let i : Fin (w.st Z).toD7.R.m := Fin.cast hm i'
  have h : (i : ℕ) = i' := rfl
  obtain ⟨⟨-, -, -, -, -, -, hβ, -, -, hPg, -, -, h1, -⟩, h2⟩ := hS
  obtain ⟨c1, c2, c3, c4, -⟩ := h1 i i' h
  obtain ⟨-, -, hHV, -, -, hν, hfd⟩ := h2 i i' h
  exact ModVExt.modV_of (a := Z) (a' := Z') (R := z.R.toRealDat) (R' := R'.toRealDat) hP h hβ hPg hL.2.2.2 hL.2.2.1 c1 c2 c3 c4
    (hL.1 i i' h).2 hHV hν hfd z.pins.char.base.models
end
