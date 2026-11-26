module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSide

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHeckeFamilyOnRationalDatumForms
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHeckeFamilyOnRationalDatumForms
namespace RationalFamilyExistence
section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Member.RatFamily

theorem exists_family : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S), R.toLevCh.Is A3.A.μ0 → R.AllPlaces → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) → ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ GlobalTheory.ExportPin.Reads R cG S Y hL := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R cG S Y hLev hAll hRat
  have hA' : R.Sb = R.Pg := hAll
  obtain ⟨f, hs, hf⟩ := GlobalTheory.ExportPin.Model.exists_reads R cG S Y (fun i P ho k hk => by
    have ho' : Formalism.IndefR.Bridge.SplitOff P (R.Pg : Set (Formalism.L2.DIV.Pl D.host.E)) := by
      rw [← hA']; exact ho
    have hg := (GlobalTheory.splitOff_places R.C.P R.Pg ∅ P hLev.Pg
      (fun v hv => absurd hv (Finset.notMem_empty v)) ho').1
    exact hRat i P ⟨ho, hg⟩ k hk)
  exact ⟨f, hs, hf⟩

end GlobalTheory.CompanionTheory.Member.RatFamily

end
end

end RationalFamilyExistence
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.Adopt.exists_rational_hecke_family_on_rational_datum_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S), R.toLevCh.Is A3.A.μ0 → R.AllPlaces → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) → ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ GlobalTheory.ExportPin.Reads R cG S Y hL := by
  first | exact @RationalFamilyExistence.GlobalTheory.CompanionTheory.Member.RatFamily.exists_family | exact RationalFamilyExistence.GlobalTheory.CompanionTheory.Member.RatFamily.exists_family | (intros; apply RationalFamilyExistence.GlobalTheory.CompanionTheory.Member.RatFamily.exists_family <;> assumption)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalHeckeFamilyOnRationalDatumFormsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_hecke_family_on_rational_datum_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S), R.toLevCh.Is A3.A.μ0 → R.AllPlaces → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R.toRealDat i) → ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ GlobalTheory.ExportPin.Reads R cG S Y hL := by
  first | exact @GlobalTheory.Adopt.exists_rational_hecke_family_on_rational_datum_forms | exact GlobalTheory.Adopt.exists_rational_hecke_family_on_rational_datum_forms | (intros; apply GlobalTheory.Adopt.exists_rational_hecke_family_on_rational_datum_forms <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeReadAsCosetSums
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeReadAsCosetSums
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeReadRational

section SlopeTestRemainingChoices

open Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem hkC_eq_heckeScalar {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : hkC R i P k = heckeScalar R i P k := by
  rw [hkC, heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]

theorem heckeOn_mem_wall_of_hkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb) (hHW : R.models_HW)
    (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hd : IsHkData R i P k α Rc) (z : (R.HW i σ).H) :
    heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) ∈ R.Wall i σ := by
  obtain ⟨hso, -, -, ⟨e, ϖ, he, -, -, hα⟩, hR⟩ := hd
  obtain ⟨c, hβ⟩ := hβ'
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hq := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).2.2.1 P e _ hp
  obtain ⟨large₂, hLg⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).1 _ hq.1 hq.2.1).1
  have hK : ∀ g, g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ⊓ large₂ ↔ g ∈ locPart (Wc D i) (KsphC (Wc D i) ∅) e := by
    intro g
    have h1 := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places (Wc D i) (R.βW i) _ _ (R.datWp i R.triv) hβ).2 P e _ hp hN hoff).1 g
    exact ⟨fun h => ⟨(h1 ((hLg g).1 h.2)).1 h.1, (hLg g).1 h.2⟩, fun h => ⟨(h1 h.2).2 h.1, (hLg g).2 h.2⟩⟩
  have hoL := GlobalTheory.HeckeModel.offAt_of_place hβ he hN hoff hLg hK
  have hαL : α ∈ large₂ := (hLg α).2 hα.2.1
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.HeckeSup.exists_local_isDC hoL.splits hαL hR
  have key : heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) = heckeOn (R.MW i σ) A₀ ((R.HW i σ).e z) := by
    ext v : 1
    show heckeLin (Wc D i) Rc ((R.HW i σ).e z v) = heckeLin (Wc D i) A₀ ((R.HW i σ).e z v)
    exact funext fun h => GlobalTheory.HeckeModel.sum_eq_of_isDC hR (hoL.splits.isDC hαL hA₀) ⟨1, 1, by simp⟩
      (GlobalTheory.HeckeSup.model_inv_cl hHW i σ z v) h
  rw [key]
  exact GlobalTheory.HeckeModel.heckeOn_mem_mult hoL (fun g hg => hq.2.2.1 g ((hLg g).1 hg)) hαL hA₀
    (show (R.HW i σ).e z ∈ R.Wall i σ from (hHW i σ).2.1 ▸ LinearMap.mem_range_self _ z)

end SlopeTestRemainingChoices

section Main

open Formalism.IndefR.Mult


set_option maxHeartbeats 1600000 in
theorem rationalHecke_of_readsCusp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i hT hlev hfam hmod hex _ hR P hP k hk
  have hHW : R.models_HW := hmod.HW
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i :=
    fw.laws.spaceW _ (inR i) _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  obtain ⟨p, m, hp, hpP, -⟩ := GlobalTheory.HeckeSup.exists_prime_under P
  have hoff := GlobalTheory.HeckeSup.not_dvd_level fw.laws hpP hP.2
  have hsp := GlobalTheory.HeckeSup.split_of_ne (H := T.Q.H) hP.1.1
  have hn : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have htr : ∀ f : Cu T κ i, ∃ g ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
        (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g := by
    intro f
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hT GlobalTheory.ThetaTransport.heckePointLaws fw.laws i
      ⟨P.isMaximal, hsp, hp, hpP, hoff⟩ hk ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) (dom_wtA (κ i)) f f.2
    rw [show hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k (κ i).n =
      hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose g hg hfg using htr
  have hEI := GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW fw.hv₀ i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  have hread : ∀ f : Cu T κ i, ∀ Rc, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.IsCosetSys R i P k Rc →
      (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK)) =
        GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc
          ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
    rintro f Rc ⟨α, hα, hRc⟩
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData R i P k α Rc := ⟨hP.1, hP.2, hk, hα, hRc⟩
    have h1 := hR hV P p k α Rc hd ⟨hP.1, hp, hpP, hoff, hk, hα, hRc⟩ f f.2 (g f) (hg f) (hfg f)
    rw [hkC_eq_heckeScalar] at h1
    obtain ⟨z', hz'⟩ : ∃ z', (R.HW i (sg0 D A)).e z' = heckeOn (R.MW i (sg0 D A)) Rc
        ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
      rw [← LinearMap.mem_range, (hHW i _).2.1]
      exact heckeOn_mem_wall_of_hkData (hlev.βW i) hfam.Sb hHW _ hd _
    have e1 : (R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK) = GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • z' := by
      apply hEI
      refine (GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) ⟨g f, hg f⟩).trans ?_
      funext h
      rw [h1 h, ← GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) f]
      unfold evAt
      rw [map_smul, hz']
      simp [heckeOn, postOn, heckeLin]
      exact Or.inl rfl
    rw [e1, map_smul, hz']
  obtain ⟨n, b, hbK, -, hKspan, hLind, hLspan⟩ := fw.ks i
  let B : Module.Basis (Fin n) D.what₂.LL (Fin (R.nW i) → D.what₂.LL) := Module.Basis.mk hLind hLspan.ge
  have hB : ∀ l, B l = b l := fun l => Module.Basis.mk_apply hLind hLspan.ge l
  let f0 : Fin n → Cu T κ i := fun l => (fw.e i).symm ⟨b l, hbK l⟩
  let yv : Fin n → Fin (R.nW i) → D.what₂.LL := fun l => (fw.e i ⟨g (f0 l), hg (f0 l)⟩ : (R.FW i).WK)
  let hL := B.constr D.what₂.LL yv
  have hLb : ∀ l, hL (b l) = yv l := fun l => by rw [← hB l]; exact B.constr_basis _ _ _
  have hb0 : ∀ l, (fw.e i (f0 l) : Fin (R.nW i) → D.what₂.LL) = b l := fun l => by simp [f0]
  refine ⟨hL, fun Rc hRc => ?_, fun x hx => ?_⟩
  · have hext := B.ext (f₁ := ((R.HW i (sg0 D A)).e.comp ((R.FW i).j (sg0 D A))).comp hL)
      (f₂ := ((GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc).comp (R.HW i (sg0 D A)).e).comp
        ((R.FW i).j (sg0 D A))) fun l => by
      rw [hB l]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hLb l, ← hb0 l]
      exact hread (f0 l) Rc hRc
    intro x
    have := LinearMap.congr_fun hext x
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using this
  · rw [← hKspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [hLb]
      exact (fw.e i _).2
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ a hx

end Main

end GlobalTheory.HeckeReadRational
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeReadAsCosetSumsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalHecke_read_as_cosetSums : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i := by
  first | exact @GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp | exact GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp | (intros; apply GlobalTheory.HeckeReadRational.rationalHecke_of_readsCusp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReading
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFamRead

set_option autoImplicit false

open Formalism.BasicNotions.TH Formalism.IndefR.Mult

theorem isDC_one {G : Type} [Group G] (J : Subgroup G) : Formalism.IndefR.Bridge.IsDC J 1 {1} := by
  refine ⟨fun a ha => ⟨1, 1, by simpa using ha⟩, ?_⟩
  rintro g ⟨k, k', rfl⟩
  exact ⟨1, ⟨Finset.mem_singleton_self _, by simpa using J.mul_mem k.2 k'.2⟩, fun a ha => Finset.mem_singleton.1 ha.1⟩

theorem isHeckeAt_zero_one {D : D7} (V : HSp D) {P : PlE D.host} (hP : Formalism.BasicNotions.IsSplitPl D.host P) :
    IsHeckeAt V P 0 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P ((GlobalTheory.HeckeTieCompare.isSplitPl_iff P).1 hP)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  exact ⟨e, ϖ, he, h1, h2, GlobalTheory.HeckeParts.isHeckeElt_one V he.1 ϖ⟩

theorem rat_side (hT : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform) (hS : ∀ (D : D7) (X : GlobalTheory.TwInputs.RealSide D) (i : Fin D.R.m) (hV : X.core.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) = Wc D i), GlobalTheory.HeckeSup.ReadsCusp X.core X.R.toRealDat X.geo.κ i (Formalism.IndefR.FWT.res X.core (sg0 D X.A3.A)) hV)
    (hA : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i) (D : D7) (X : RealSide D) (i : Fin D.R.m) : GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke X.R.toRealDat i := by
  refine hA D X.Γ X.Pl0 X.T X.A3.A X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.fw i hT X.char.lev X.char.fam X.char.models
    (fun hV => X.inGeo.jEvExists i _ (Formalism.IndefR.FWT.base_embedding_good X.core X.R.toRealDat X.geo.fw.alg_eq X.geo.fw.laws.pins.2.2.1) hV)
    ?_ (hS D X i)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  by_contra h
  have h1 := (X.unif i (sg0 D X.A3.A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h)
  exact h1.ne_zero 0 hx

theorem exists_family_one (hrat : ∀ (D : D7) (X : RealSide D) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke X.R.toRealDat i)
    (D : D7) (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S) :
    ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧
      (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL := by
  obtain ⟨hL, hs, hr⟩ := GlobalTheory.T.exists_rational_hecke_family_on_rational_datum_forms D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG S YS X.char.lev X.char.allPl (hrat D X)
  refine ⟨fun j k P => if k = 0 then 1 else hL j k P, fun j h1 h2 k P x hx => ?_, fun j P => if_pos rfl, ?_⟩
  · by_cases hk : k = 0
    · simp only [hk, if_true, Module.End.one_apply]
      exact hx
    · simp only [hk, if_false]
      exact hs j h1 h2 k P x hx
  · intro i k P hsp hso hk α Rc hα hdc x
    by_cases h0 : k = 0
    · subst h0
      have e1 := hr i 0 P hsp hso hk α Rc hα hdc x
      have e2 := hr i 0 P hsp hso hk 1 {1} (isHeckeAt_zero_one _ hsp) (isDC_one _) x
      have e3 : ∀ F, heckeOn (X.R.MW i (sg0 D X.A3.A)) {1} F = F := by
        intro F
        ext v g
        simp [heckeOn, postOn, heckeLin]
      rw [e3] at e2
      simp only [pow_zero, zero_mul, inv_one, mul_one, one_smul] at e1 e2 ⊢
      exact e2.symm.trans e1
    · simp only [h0, if_false]
      exact hr i k P hsp hso hk α Rc hα hdc x

theorem exists_family_reads : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D), ∀ (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S), ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL :=
  fun hD hT hR D X S YS => exists_family_one (rat_side hT (GlobalTheory.T.heckeTransform_cuspForms_reads_cosetSum hD hR) GlobalTheory.T.exists_rationalHecke_read_as_cosetSums) D X S YS

end GlobalTheory.HeckeFamRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReadingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rationalHeckeOperators_adelicReading : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D), ∀ (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S), ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧ (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL := by
  first | exact @GlobalTheory.HeckeFamRead.exists_family_reads | exact GlobalTheory.HeckeFamRead.exists_family_reads | (intros; apply GlobalTheory.HeckeFamRead.exists_family_reads <;> assumption)
end
