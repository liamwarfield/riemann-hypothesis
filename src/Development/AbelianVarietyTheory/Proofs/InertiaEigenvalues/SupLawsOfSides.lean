module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KeepSideBMtVPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeCommuteOfTwistSeriesSideData
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteAllLifts
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.NX
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SupLaw

section Coset

open GlobalTheory.HeckeParts

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem offPrincipalLevel (hSb : R.fam_Sb) (i : Fin D.R.m) {P : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) (c : ℕ) :
    OffLevel (R.datWp i R.triv) (1 ^ c) P := by
  refine ⟨hso.1, ?_, fun PP hPP => ?_⟩
  · rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  · have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]

theorem cosetSum_comm (hL : R.toLevCh.Is A.μ0) (hSb : R.fam_Sb) (i : Fin D.R.m) {P P' : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)))
    (hso' : Bridge.SplitOff P' (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k k' : ℕ} {α α' : GA D (Wc D i)}
    {Rc Rc' : Finset (GA D (Wc D i))} (ha : IsHeckeAt (Wc D i) P k α) (ha' : IsHeckeAt (Wc D i) P' k' α')
    (hR : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc)
    (hR' : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α' Rc') {F : GA D (Wc D i) → ℂ}
    (hF : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F) :
    heckeLin (Wc D i) Rc (heckeLin (Wc D i) Rc' F) = heckeLin (Wc D i) Rc' (heckeLin (Wc D i) Rc F) := by
  obtain ⟨c, hβ⟩ := hL.βW i
  have hP := offPrincipalLevel hSb i hso c
  have hP' := offPrincipalLevel hSb i hso' c
  obtain ⟨e, ϖ, he, -, -, hα⟩ := ha
  obtain ⟨e', ϖ', he', -, -, hα'⟩ := ha'
  obtain ⟨⟨A₀, hA⟩, -⟩ := exists_locRep hβ hP he hα.2.1
  obtain ⟨⟨B₀, hB⟩, -⟩ := exists_locRep hβ hP' he' hα'.2.1
  have e1 : ∀ {F : GA D (Wc D i) → ℂ}, RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F →
      heckeLin (Wc D i) Rc F = heckeLin (Wc D i) A₀ F := fun hF =>
    (dcOp_eq_rInv hR hA.2 ⟨1, 1, by simp⟩ hF).1
  have e2 : ∀ {F : GA D (Wc D i) → ℂ}, RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) F →
      heckeLin (Wc D i) Rc' F = heckeLin (Wc D i) B₀ F := fun hF =>
    (dcOp_eq_rInv hR' hB.2 ⟨1, 1, by simp⟩ hF).1
  have i1 : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) (heckeLin (Wc D i) A₀ F) := dcOp_rInv hA.2 hF
  have i2 : RInv (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) (heckeLin (Wc D i) B₀ F) := dcOp_rInv hB.2 hF
  rw [e2 hF, e1 hF, e1 i2, e2 i1]
  exact hA.comm hβ hP hB hF

end Coset

section Tied

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S)

theorem commute_of_read (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hSb : Rl.toRealDat.fam_Sb) (hW : Rl.toRealDat.models_HW)
    (i : Fin D.R.m) (hinj : Function.Injective ((Rl.FW i).j (sg0 D A3.A))) {P P' : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)))
    (hso' : Bridge.SplitOff P' (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k k' : ℕ} {α α' : GA D (Wc D i)}
    {Rc Rc' : Finset (GA D (Wc D i))} (ha : IsHeckeAt (Wc D i) P k α) (ha' : IsHeckeAt (Wc D i) P' k' α')
    (hR : Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α Rc)
    (hR' : Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α' Rc')
    {t t' : Module.End D.what₂.LL (S.WL ((i : ℕ) + 1))} {c c' : ℂ}
    (ht : ∀ x, (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t x))) =
      c • heckeOn (Rl.MW i (sg0 D A3.A)) Rc ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e x))))
    (ht' : ∀ x, (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t' x))) =
      c' • heckeOn (Rl.MW i (sg0 D A3.A)) Rc' ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e x)))) :
    Commute t t' := by
  refine LinearMap.ext fun x => (Y.fi i).e.injective (hinj ((hW i _).1 ?_))
  change (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t (t' x)))) =
    (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) ((Y.fi i).e (t' (t x))))
  rw [ht, ht', ht', ht, map_smul, map_smul, smul_comm]
  refine congrArg (fun z : MMap (Rl.MW i (sg0 D A3.A)) => c' • c • z) ?_
  exact MultilinearMap.ext fun v => cosetSum_comm hL hSb i hso hso' ha ha' hR hR'
    (fun k hk h => GlobalTheory.HeckeSup.model_inv_cl hW i _ _ v k hk h)


set_option synthInstance.maxHeartbeats 400000 in
theorem baseChange_comm (i : D.ntw.Tw) (j : ℕ) (b : Bool) {f : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)}
    (hs : HeckeStabR S j f) (k k' : ℕ) (P P' : PlE D.host) (h : Commute (f k P) (f k' P')) :
    Commute (hkFR S i j b f hs k P) (hkFR S i j b f hs k' P') := by
  let r : ℕ → PlE D.host → Module.End S.Ks (FmK S j) := fun k P =>
    ((f k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx
  have hr : r k P * r k' P' = r k' P' * r k P := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun h.eq x.1)
  unfold hkFR Commute SemiconjBy
  change (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k P)) * (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k' P')) =
    (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k' P')) * (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (r k P))
  rw [← map_mul, ← map_mul, hr]


set_option synthInstance.maxHeartbeats 400000 in
theorem hkComm_of_family (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (f j))
    (c : ∀ i : D.ntw.Tw, Bool → ℕ → PlE D.host → FractionRing (D.ntw.O i))
    (hEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (x : D.nexp.Fm i j b), P ∉ D.ntw.S0 i →
      Formalism.BasicNotions.IsSplitPl D.host P → k ≤ D.R.r →
      Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) = c i b k P • hkFR S i j b (f j) (hs j h1 h2) k P (Y.eF i j b h1 h2 x))
    (hc : ∀ (i : D.ntw.Tw) j, 1 ≤ j → j ≤ D.R.m → ∀ k P k' P', Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P → Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P' →
      Commute (f j k P) (f j k' P')) : HkComm D := by
  intro i _ j hj b k P k' P' hk hk'
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have hF := baseChange_comm S i j b (hs j h1 h2) k k' P P' (hc i j h1 h2 k P k' P' hk hk')
  refine LinearMap.ext fun x => (Y.eF i j b h1 h2).injective ?_
  change Y.eF i j b h1 h2 (D.nexp.hkF i j b k P (D.nexp.hkF i j b k' P' x)) =
    Y.eF i j b h1 h2 (D.nexp.hkF i j b k' P' (D.nexp.hkF i j b k P x))
  rw [hEq i j b h1 h2 k P _ hk.2.2.2 hk.2.2.1 hk.2.1, hEq i j b h1 h2 k' P' _ hk'.2.2.2 hk'.2.2.1 hk'.2.1,
    hEq i j b h1 h2 k' P' _ hk'.2.2.2 hk'.2.2.1 hk'.2.1, hEq i j b h1 h2 k P _ hk.2.2.2 hk.2.2.1 hk.2.1, map_smul, map_smul,
    smul_comm]
  exact congrArg (fun z => c i b k' P' • c i b k P • z) (LinearMap.congr_fun hF.eq (Y.eF i j b h1 h2 x))

theorem family_comm (hL : Rl.toRealDat.toLevCh.Is A3.A.μ0) (hF : Rl.toRealDat.IsFam) (hW : Rl.toRealDat.models_HW)
    (hinj : ∀ i, Function.Injective ((Rl.FW i).j (sg0 D A3.A))) (hC : GlobalTheory.ExportPin.Model.Covered Rl)
    (f : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hr : ∀ (i : D.ntw.Tw) (n : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P →
      ∀ (α : GA D (Wc D n)) (R : Finset (GA D (Wc D n))), IsHeckeAt (Wc D n) P k α →
        Bridge.IsDC (levG (Wc D n) (Rl.βW n) (Rl.datWp n Rl.triv)) α R → ∃ c : ℂ, ∀ x : S.WL ((n : ℕ) + 1),
          (Rl.HW n (sg0 D A3.A)).e ((Rl.FW n).j (sg0 D A3.A) ((Y.fi n).e (f ((n : ℕ) + 1) k P x))) =
            c • heckeOn (Rl.MW n (sg0 D A3.A)) R ((Rl.HW n (sg0 D A3.A)).e ((Rl.FW n).j (sg0 D A3.A) ((Y.fi n).e x))))
    (i : D.ntw.Tw) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (k' : ℕ) (P' : PlE D.host)
    (hk : Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P) (hk' : Formalism.MainNotions.IntegralHeckeForms.HkIdx i k' P') : Commute (f j k P) (f j k' P') := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  let m : Fin D.R.m := ⟨n, h2⟩
  have so := hC i P hk.2.2.2 hk.2.2.1
  have so' := hC i P' hk'.2.2.2 hk'.2.2.1
  obtain ⟨α, Rc, ha, hR⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hL hF m so hk.2.1
  obtain ⟨α', Rc', ha', hR'⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hL hF m so' hk'.2.1
  obtain ⟨c, hc⟩ := hr i m k P hk α Rc ha hR
  obtain ⟨c', hc'⟩ := hr i m k' P' hk' α' Rc' ha' hR'
  exact commute_of_read Rl cG S Y hL hF.Sb hW m (hinj m) so so' ha ha' hR hR' hc hc'



end Tied

end GlobalTheory.SupLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeCommuteOfTwistSeriesSideData
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.SupLaw

theorem hkComm_of_ties : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), HkComm D := by
  intro D X E Y
  have hC : GlobalTheory.ExportPin.Model.Covered X.R := GlobalTheory.ExportPin.Model.covered_of_allPlaces X.R X.char.lev X.char.allPl
  exact hkComm_of_family X.R X.cG Y.S Y.YS Y.H.hL Y.H.hs Y.H.cHk Y.H.hkEq fun i j a b k P k' P' hk hk' =>
    family_comm X.R X.cG Y.S Y.YS X.char.lev X.char.fam X.char.models.HW
      (fun n => GlobalTheory.ExportPin.Model.j_injective X.R X.unif n _) hC Y.H.hL
      (fun i n k P hk α R ha hR => ⟨_, fun x => Y.reads n k P hk.2.2.1 (hC i P hk.2.2.2 hk.2.2.1) hk.2.1 α R ha hR x⟩)
      i j a b k P k' P' hk hk'

end GlobalTheory.SupLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeCommuteOfTwistSeriesSideDataStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceHeckeCommute_of_twistSeriesSideData : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), HkComm D := by
  first | exact @GlobalTheory.SupLaw.hkComm_of_ties | exact GlobalTheory.SupLaw.hkComm_of_ties | (intros; apply GlobalTheory.SupLaw.hkComm_of_ties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesSupLatticeAndCommutesTypeGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeckeEltAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HkSupComm

section Keep

open Formalism.L2.NTheta GlobalTheory.HeckeParts GlobalTheory.HeckeSupSt

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem exists_heckeElt_all {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (hL : R.toLevCh.Is A.μ0) (hA : R.Sb = R.Pg) (i : Fin D.R.m) {P : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k : ℕ} (hk : k ≤ D.R.r) :
    ∃ α Rc, IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc := by
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := by rw [hA]; exact hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hso.1
  obtain ⟨ϖ, h1, h2⟩ := IsConcreteLE.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨-, hrep, hel⟩ := GlobalTheory.SplitPlace.split_local (Wc D i) P e he
  obtain ⟨α, hα⟩ := (hel ϖ h1 h2).1 k (hk.trans (r_le_rank_Wc i))
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨Rc, hA, h3, h4⟩ := hrep α hα.2.1
  exact ⟨α, Rc, ⟨e, ϖ, he, h1, h2, hα⟩, isDC_of_splits hs levG_le_flag ((hLp α).2 hα.2.1) (fun a ha => (hLp a).2 (hA a ha)) hK
    (fun γ hγ => (h3 γ hγ).2) h4⟩

end Keep

theorem keeps_transport : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y), R.toLevCh.Is A3.A.μ0 → R.AllPlaces → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R.toRealDat i) → GlobalTheory.ExportPin.Reads R cG S Y H.hL → ∀ (i : D.ntw.Tw) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P → P ∉ D.ntw.S0 i → k ≤ D.R.r → ∀ (la : HeightOneSpectrum (𝓞 T.Q.c.F)), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal → ∀ (hW : ∀ x ∈ (R.FW i').WK, ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) x ∈ (R.FW i').WK), GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) hW := by
  intro D G _ _ Pl0 I0 T0 A3 T _ R cG S Y H hLev hAll hSup hRd i i' k P hsp hS0 hkr la hl hW
  have hso : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) :=
    GlobalTheory.ExportPin.Model.covered_of_allPlaces R hLev hAll i P hS0 hsp
  obtain ⟨α, Rc, ha, hR⟩ := exists_heckeElt_all hLev hAll i' hso hkr
  have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro h
    rw [Nat.cast_mul] at h
    rcases P.isPrime.mem_or_mem h with h | h
    · exact hS0 (D.ntw.placesOver_subset_exceptional i 0 h)
    · exact hS0 (D.ntw.placesOver_subset_exceptional i 1 h)
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData R.toRealDat i' P k α Rc := ⟨hso, hg, hkr, ha, hR⟩
  refine hSup i' P k α Rc hd _ ?_ hW la ?_
  · intro x
    have h := hRd i' k P hsp hso hkr α Rc ha hR ((Y.fi i').e.symm x)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
    rw [h]
    congr 1
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.hkC
    rw [inv_pow]
  · intro p hp hpP hpla
    have hpl : p ≠ D.ntw.l i := by
      rintro rfl
      exact hS0 (D.ntw.twistExcludedPlaces_contains_residueChar i hpP)
    have hcop : IsCoprime (p : 𝓞 T.Q.c.F) ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) :=
      Nat.Coprime.cast ((Nat.coprime_primes hp (D.ntw.lPrime i).out).2 hpl)
    obtain ⟨u, v, huv⟩ := hcop
    exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hpla) (la.asIdeal.mul_mem_left _ hl)))

end GlobalTheory.HkSupComm

namespace GlobalTheory.HkSupComm

section Alg
variable {D : D7} (S : RatDat D.ntw)

def toF (j : ℕ) (x : ↥(S.A j).WK) : FmK S j := x

def tm (i : D.ntw.Tw) (j : ℕ) (b : Bool) (x : ↥(S.A j).WK) : Fm S i j b := (1 : KB S i b) ⊗ₜ[S.Ks] toF S j x

theorem hkFR_bsup (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host)
    (h : ∀ x ∈ (S.A j).MK, ∃ s : S.Ks, (∃ u : (D.ntw.O i)ˣ, ιK S i b s = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u) ∧
      s • hL k P x ∈ (S.A j).MK) :
    ∀ z ∈ Bsup S i j b, hkFR S i j b hL hs k P z ∈ Bsup S i j b := by
  intro z hz
  refine Submodule.span_induction (p := fun z _ => hkFR S i j b hL hs k P z ∈ Bsup S i j b) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨x0, hx, rfl⟩
    obtain ⟨s, ⟨u, hu⟩, hsm⟩ := h _ hx
    have hs0 : s ≠ 0 := by
      rintro rfl
      have hinj := IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
      rw [map_zero] at hu
      exact u.ne_zero (hinj (by rw [map_zero]; exact hu.symm))
    have hwk : s • hL k P (x0 : ↥(S.A j).WK).1 ∈ (S.A j).WK := (S.A j).WK.smul_mem s (hs k P _ (x0 : ↥(S.A j).WK).2)
    have e : toF S j ⟨hL k P (x0 : ↥(S.A j).WK).1, hs k P _ (x0 : ↥(S.A j).WK).2⟩ = s⁻¹ • toF S j ⟨_, hwk⟩ := by
      change (⟨_, _⟩ : ↥(S.A j).WK) = s⁻¹ • (⟨_, hwk⟩ : ↥(S.A j).WK)
      apply Subtype.ext
      change hL k P (x0 : ↥(S.A j).WK).1 = s⁻¹ • (s • hL k P (x0 : ↥(S.A j).WK).1)
      rw [inv_smul_smul₀ hs0]
    have key : tm S i j b ⟨hL k P (x0 : ↥(S.A j).WK).1, hs k P _ (x0 : ↥(S.A j).WK).2⟩ =
        ιK S i b s⁻¹ • tm S i j b ⟨_, hwk⟩ := by
      unfold tm
      rw [e, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      erw [TensorProduct.smul_tmul']
      congr 1
    have e3 : ιK S i b s⁻¹ = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) := by
      rw [map_inv₀, hu]
      have h5 : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) *
          algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u : D.ntw.O i) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      exact (eq_inv_of_mul_eq_one_left h5).symm
    have hgen : tm S i j b ⟨_, hwk⟩ ∈ Bsup S i j b := Submodule.subset_span ⟨_, hsm, rfl⟩
    have := Submodule.smul_mem _ ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) hgen
    have e4 : ιK S i b s⁻¹ • tm S i j b ⟨_, hwk⟩ = ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i) • tm S i j b ⟨_, hwk⟩ := by
      rw [e3]; rfl
    rw [← e4, ← key] at this
    exact this
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro a x _ hx
    change hkFR S i j b hL hs k P (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) a • x) ∈ Bsup S i j b
    rw [map_smul]
    exact Submodule.smul_mem _ a hx
end Alg

section Act
variable {D : D7} (S : RatDat D.ntw)

def hLr (j : ℕ) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) :
    Module.End S.Ks (FmK S j) :=
  ((hL k P).restrictScalars S.Ks).restrict (p := (S.A j).WK) (q := (S.A j).WK) fun x hx => hs k P x hx

theorem hkFR_act (i : D.ntw.Tw) (j : ℕ) (b : Bool) (hL : ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j))
    (hs : HeckeStabR S j hL) (k : ℕ) (P : PlE D.host) (hst : RhoStab S j) (hχ : ChiInLL0 S j)
    (hc : ∀ g x, hL k P ((S.A j).ρ g x) = (S.A j).ρ g (hL k P x)) (g : G0g D.nd) (z : Fm S i j b) :
    hkFR S i j b hL hs k P (actG S i j b hst hχ g z) = actG S i j b hst hχ g (hkFR S i j b hL hs k P z) := by
  have hcomm : hLr S j hL hs k P * rhoKG S j hst (S.eG.symm g) = rhoKG S j hst (S.eG.symm g) * hLr S j hL hs k P := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    exact hc (S.eG.symm g) (show ↥(S.A j).WK from x).1
  have h2 := LinearMap.congr_fun (congrArg (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j)) hcomm) z
  rw [map_mul, map_mul] at h2
  change Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) ((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g)) z) =
    (readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
      Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g))
        (Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (hLr S j hL hs k P) z)
  rw [map_smul]
  congr 1
end Act

section
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat3 D A3 T.Q.c.F} {cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd}
  {S : RatDat D.ntw} (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y)

theorem hW_of (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host) :
    ∀ x ∈ (R.FW i').WK, ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) x ∈ (R.FW i').WK := by
  intro x hx
  have h1 : (Y.fi i').e.symm x ∈ (S.A ((i' : ℕ) + 1)).WK := by
    rw [(Y.fi i').wk, LinearEquiv.apply_symm_apply]; exact hx
  have h2 := H.hs ((i' : ℕ) + 1) (by omega) (by have := i'.2; omega) k P _ h1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact ((Y.fi i').wk _).1 h2

theorem rho_comm (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host) (la : HeightOneSpectrum (𝓞 T.Q.c.F))
    (hK : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap)
      (hW_of Y H i' k P)) (g : S.G) (x : S.WL ((i' : ℕ) + 1)) :
    H.hL ((i' : ℕ) + 1) k P ((S.A ((i' : ℕ) + 1)).ρ g x) = (S.A ((i' : ℕ) + 1)).ρ g (H.hL ((i' : ℕ) + 1) k P x) := by
  apply (Y.fi i').e.injective
  have h := LinearMap.congr_fun (hK.rho ((Y.fi i').eG g)) ((Y.fi i').e x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  rw [(Y.fi i').rho, ← h, ← (Y.fi i').rho, LinearEquiv.symm_apply_apply]

theorem mk_smul (i : D.ntw.Tw) (b : Bool) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host)
    (hMK : (R.FW i').MKFull)
    (hK : ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal →
      GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap)
      (hW_of Y H i' k P))
    (x : S.WL ((i' : ℕ) + 1)) (hx : x ∈ (S.A ((i' : ℕ) + 1)).MK) :
    ∃ s : S.Ks, (∃ u : (D.ntw.O i)ˣ, ιK S i b s = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u) ∧
      s • H.hL ((i' : ℕ) + 1) k P x ∈ (S.A ((i' : ℕ) + 1)).MK := by
  have hx' : (Y.fi i').e x ∈ (R.FW i').MK := ((Y.fi i').mkK x).1 hx
  obtain ⟨hwk, hn⟩ : ∃ h : (Y.fi i').e x ∈ (R.FW i').WK, ∀ lp y, (R.FW i').nrm lp y ⟨_, h⟩ ≤ 1 := hx'
  obtain ⟨la, hl, hla⟩ := GlobalTheory.EmbeddingPlace.exists_place D T.Q.c.F i ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom)
  have hb := (hK la hl).sup ⟨_, hwk⟩ (fun y => hn la y)
  obtain ⟨s', hs'la, hs'mk⟩ := GlobalTheory.supLattice_localisation_of_unitBall _ _ _ _ _ (R.FW i') hMK.2 la _ hb
  have e1 : ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap) ((Y.fi i').e x) =
      (Y.fi i').e (H.hL ((i' : ℕ) + 1) k P x) := by
    simp
  refine ⟨(Y.fi i').eK.symm (s' : T.Q.c.F), ?_, ?_⟩
  · have n1 : FinitePlace.mk la (s' : T.Q.c.F) = 1 := by
      rw [FinitePlace.mk_apply]; exact (FinitePlace.norm_eq_one_iff_notMem _ la s').2 hs'la
    have hs0 : (s' : T.Q.c.F) ≠ 0 := by
      intro h0
      have : s' = 0 := by exact_mod_cast h0
      exact hs'la (this ▸ la.asIdeal.zero_mem)
    obtain ⟨a, ha⟩ := (hla s').2 n1.le
    obtain ⟨a', ha'⟩ := (hla (s' : T.Q.c.F)⁻¹).2 (by rw [map_inv₀, n1, inv_one])
    have hmul : a * a' = 1 := by
      apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
      have h1 : ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom) ((s' : T.Q.c.F) * (s' : T.Q.c.F)⁻¹) = 1 := by
        rw [mul_inv_cancel₀ hs0, map_one]
      rw [map_mul] at h1
      rw [map_mul, ha, ha', map_one]
      exact h1
    refine ⟨⟨a, a', hmul, by rw [mul_comm]; exact hmul⟩, ?_⟩
    exact ha.symm
  · rw [(Y.fi i').mkK]
    have e2 : (Y.fi i').e ((Y.fi i').eK.symm (s' : T.Q.c.F) • H.hL ((i' : ℕ) + 1) k P x) =
        s' • (Y.fi i').e (H.hL ((i' : ℕ) + 1) k P x) := by
      rw [← algebraMap_smul D.what₂.LL, map_smul, ← (Y.fi i').eK_LL, RingEquiv.apply_symm_apply, algebraMap_smul,
        algebraMap_smul]
    rw [e2, ← e1]
    exact hs'mk

end

theorem commG (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y)
    (hLev : R.toLevCh.Is A3.A.μ0) (hAll : R.AllPlaces)
    (hSup : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R.toRealDat i) (hRd : GlobalTheory.ExportPin.Reads R cG S Y H.hL) :
    GlobalTheory.LiftLeaf.CommG D := by
  have hK : ∀ (i : D.ntw.Tw) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      k ≤ D.R.r → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal →
      GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap)
        (hW_of Y H i' k P) :=
    fun i i' k P h1 h2 h3 la hl => keeps_transport D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd i i' k P h1 h2 h3 la hl _
  have hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j := fun j h1 h2 =>
    ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  intro i _ b j hj g k P hk
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨i', rfl⟩ := hidx j h1 h2
  obtain ⟨_, hkr, hsp, hS0⟩ := hk
  obtain ⟨la, hl, -⟩ := GlobalTheory.EmbeddingPlace.exists_place D T.Q.c.F i ((ιK S i b).comp (Y.fi i').eK.symm.toRingHom)
  have hc := rho_comm Y H i' k P la (hK i i' k P hsp hS0 hkr la hl)
  refine LinearMap.ext fun x => (Y.eF i _ b h1 h2).injective ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [Y.act, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, Y.act, map_smul,
    hkFR_act S i _ b (H.hL _) (H.hs _ h1 h2) k P (Y.rho _ h1 h2) (Y.chi _ h1 h2) hc]

theorem eF_hkF_mem_bsup (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y)
    (hLev : R.toLevCh.Is A3.A.μ0) (hAll : R.AllPlaces) (hMK : ∀ i, (R.FW i).MKFull)
    (hSup : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R.toRealDat i) (hRd : GlobalTheory.ExportPin.Reads R cG S Y H.hL)
    (hU : ∀ i b P, P ∉ D.ntw.S0 i → Formalism.BasicNotions.IsSplitPl D.host P →
      ∃ u : (D.ntw.O i)ˣ, H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u)
    (i : D.ntw.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (k : ℕ) (P : PlE D.host) (hS0 : P ∉ D.ntw.S0 i)
    (hsp : Formalism.BasicNotions.IsSplitPl D.host P) (hkr : k ≤ D.R.r) (f : D.nexp.Fm i j b) (hf : Y.eF i j b h1 h2 f ∈ Bsup S i j b) :
    Y.eF i j b h1 h2 (D.nexp.hkF i j b k P f) ∈ Bsup S i j b := by
  have hK : ∀ (i : D.ntw.Tw) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host), Formalism.BasicNotions.IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      k ≤ D.R.r → ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), ((D.ntw.l i : ℕ) : 𝓞 T.Q.c.F) ∈ la.asIdeal →
      GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.Keeps (R.FW i') la ((Y.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (Y.fi i').e.symm.toLinearMap)
        (hW_of Y H i' k P) :=
    fun i i' k P h1 h2 h3 la hl => keeps_transport D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd i i' k P h1 h2 h3 la hl _
  have hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j := fun j h1 h2 =>
    ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨i', rfl⟩ := hidx j h1 h2
  obtain ⟨u, hu1⟩ := hU i b P hS0 hsp
  have hu : H.cHk i b k P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) ((u ^ k : (D.ntw.O i)ˣ) : D.ntw.O i) := by
    rw [H.cHk_pow, hu1, Units.val_pow_eq_pow_val, map_pow]
  rw [H.hkEq i _ b h1 h2 k P f hS0 hsp hkr, hu, algebraMap_smul]
  exact Submodule.smul_mem _ _ (hkFR_bsup S i _ b (H.hL _) (H.hs _ h1 h2) k P
    (fun x hx => mk_smul Y H i b i' k P (hMK i') (hK i i' k P hsp hS0 hkr) x hx) _ hf)

theorem supHk_commG (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F)
    (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS R cG S) (H : NExpRealH R cG S Y)
    (hB : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b),
      x ∈ D.nexp.Bsup i j b ↔ Y.eF i j b h1 h2 x ∈ Bsup S i j b)
    (hLev : R.toLevCh.Is A3.A.μ0) (hAll : R.AllPlaces) (hMK : ∀ i, (R.FW i).MKFull)
    (hSup : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R.toRealDat i) (hRd : GlobalTheory.ExportPin.Reads R cG S Y H.hL)
    (hU : ∀ i b P, P ∉ D.ntw.S0 i → Formalism.BasicNotions.IsSplitPl D.host P →
      ∃ u : (D.ntw.O i)ˣ, H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) u) :
    GlobalTheory.SupLaw.SupHk D ∧ GlobalTheory.LiftLeaf.CommG D := by
  refine ⟨?_, commG D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hSup hRd⟩
  intro i _ j hj b k P hk f hf
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  obtain ⟨_, hkr, hsp, hS0⟩ := hk
  exact (hB i j b h1 h2 _).2 (eF_hkF_mem_bsup D G Pl0 I0 T0 A3 T R cG S Y H hLev hAll hMK hSup hRd hU i j b h1 h2 k P hS0 hsp hkr f
    ((hB i j b h1 h2 f).1 hf))

end GlobalTheory.HkSupComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesSupLatticeAndCommutesTypeGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem supHk_commG : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → SupHk D ∧ CommG D := by
  intro D X E Y hSup
  exact GlobalTheory.HkSupComm.supHk_commG D X.Γ X.Pl0 X.I0 X.T X.A3 X.core X.R X.cG Y.S Y.YS Y.H Y.sup X.char.lev X.char.allPl
    (fun i => (X.integral i).2.1) hSup Y.reads (fun i b P h _ => (GlobalTheory.T.rational_datum_small_field_form_hecke_scalar_unit D X E Y).2 i b P h)

end GlobalTheory.TwInputs
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePreservesSupLatticeAndCommutesTypeGroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_preserves_supLattice_and_commutes_typeGroup : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → SupHk D ∧ CommG D := by
  first | exact @GlobalTheory.TwInputs.supHk_commG | exact GlobalTheory.TwInputs.supHk_commG | (intros; apply GlobalTheory.TwInputs.supHk_commG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRational
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SupEq

section Iso

variable {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  [Field Ks'] [NumberField Ks'] [Algebra Ks' LL]
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL]
  [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
  [AddCommGroup WL'] [Module LL WL'] [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 LL) WL']
  [IsScalarTower (𝓞 LL) LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
  {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL Ks' WL' W' G'}

theorem iso_smul (Y : NX.FormsIso A A') (c : Ks) (w : WL) : Y.e (c • w) = Y.eK c • Y.e w := by
  rw [← algebraMap_smul LL c w, map_smul, ← Y.eK_LL, algebraMap_smul]

theorem iso_symm_smul (Y : NX.FormsIso A A') (c : Ks') (y : WL') : Y.e.symm (c • y) = Y.eK.symm c • Y.e.symm y := by
  apply Y.e.injective
  rw [iso_smul]
  simp

theorem iso_symm_smul_int (Y : NX.FormsIso A A') (c : 𝓞 Ks') (y : WL') :
    Y.e.symm (c • y) = RingOfIntegers.mapRingEquiv Y.eK.symm c • Y.e.symm y := by
  rw [← algebraMap_smul Ks' c y, ← algebraMap_smul Ks _ (Y.e.symm y), iso_symm_smul]
  rfl

theorem iso_MKFull (Y : NX.FormsIso A A') (h : A'.MKFull) : A.MKFull := by
  classical
  obtain ⟨⟨T, hT⟩, hS⟩ := h
  refine ⟨⟨T.image Y.e.symm, ?_⟩, ?_⟩
  · apply le_antisymm
    · refine Submodule.span_le.2 ?_
      intro x hx
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      have : t ∈ A'.MK := hT ▸ Submodule.subset_span ht
      exact (Y.mkK _).2 (by simpa using this)
    · intro x hx
      have h1 : Y.e x ∈ Submodule.span (𝓞 Ks') (T : Set WL') := hT ▸ (Y.mkK x).1 hx
      have h2 : ∀ y ∈ Submodule.span (𝓞 Ks') (T : Set WL'),
          Y.e.symm y ∈ Submodule.span (𝓞 Ks) ((T.image Y.e.symm : Finset WL) : Set WL) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span (by rw [Finset.coe_image]; exact Set.mem_image_of_mem _ hy)
        | zero => simp
        | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [iso_symm_smul_int]; exact Submodule.smul_mem _ _ ha
      simpa using h2 _ h1
  · apply le_antisymm
    · exact Submodule.span_le.2 fun x hx => by obtain ⟨h, -⟩ := hx; exact h
    · intro x hx
      have h1 : Y.e x ∈ Submodule.span Ks' (A'.MK : Set WL') := hS ▸ (Y.wk x).1 hx
      have h2 : ∀ y ∈ Submodule.span Ks' (A'.MK : Set WL'),
          Y.e.symm y ∈ Submodule.span Ks (A.MK : Set WL) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy => exact Submodule.subset_span ((Y.mkK _).2 (by simpa using hy))
        | zero => simp
        | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
        | smul c a _ ha => rw [iso_symm_smul]; exact Submodule.smul_mem _ _ ha
      simpa using h2 _ h1

theorem iso_MKStable (Y : NX.FormsIso A A') (h : A'.MKStable) : A.MKStable := by
  intro g f
  refine ⟨fun hf => (Y.wk _).2 ?_, fun hf => (Y.mkK _).2 ?_⟩
  · rw [Y.rho]; exact (h _ _).1 ((Y.wk _).1 hf)
  · rw [Y.rho]; exact (h _ _).2 ((Y.mkK _).1 hf)

end Iso

section Base

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} {tw : NTw R H what₂ LL0 N} (S : NX.RatDat tw)

open NX

theorem exists_int_read (i : tw.Tw) (b : Bool) (a : 𝓞 S.Ks) :
    ∃ o : tw.O i, algebraMap (tw.O i) (FractionRing (tw.O i)) o = (ιK S i b (a : S.Ks) : KB S i b) := by
  let f : S.Ks →+* FractionRing (tw.O i) := ιK S i b
  have h : IsIntegral (tw.O i) (f (a : S.Ks)) :=
    (RingOfIntegers.isIntegral_coe a).map_of_comp_eq (Int.castRingHom (tw.O i)) f (RingHom.ext_int _ _)
  exact IsIntegrallyClosed.isIntegral_iff.1 h

theorem exists_chi_read [Finite S.G] (i : tw.Tw) (b : Bool) (j : ℕ) (hχ : ChiInLL0 S j) (g : S.G) :
    ∃ o : tw.O i, algebraMap (tw.O i) (FractionRing (tw.O i)) o = ((readLL0 S i b (chiL S j hχ g))⁻¹ : KB S i b) := by
  have hn : 0 < orderOf g := orderOf_pos g
  have h1 : chiL S j hχ g ^ orderOf g = 1 := by
    apply Subtype.ext
    change (((S.A j).chi g : what₂.LLˣ) : what₂.LL) ^ orderOf g = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  let x : FractionRing (tw.O i) := ((readLL0 S i b (chiL S j hχ g))⁻¹ : KB S i b)
  have h2 : x ^ orderOf g = 1 := by
    change ((readLL0 S i b (chiL S j hχ g))⁻¹ : KB S i b) ^ orderOf g = 1
    rw [inv_pow, ← map_pow, h1, map_one, inv_one]
  have h3 : IsIntegral (tw.O i) x := IsIntegral.of_pow hn (by rw [h2]; exact isIntegral_one)
  exact IsIntegrallyClosed.isIntegral_iff.1 h3

variable (i : tw.Tw) (j : ℕ) (b : Bool)

def mkF (y : S.WL j) (h : y ∈ (S.A j).WK) : FmK S j := ⟨y, h⟩

def rdF (c : S.Ks) : FractionRing (tw.O i) := ιK S i b c

def rdK (a : KB S i b) : FractionRing (tw.O i) := a

def oneT (x : FmK S j) : Fm S i j b := ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j)

theorem oneT_zero : oneT S i j b 0 = 0 := TensorProduct.tmul_zero _ _

theorem oneT_add (x y : FmK S j) : oneT S i j b (x + y) = oneT S i j b x + oneT S i j b y :=
  TensorProduct.tmul_add _ _ _

theorem oneT_smul (c : S.Ks) (x : FmK S j) :
    oneT S i j b (c • x) = (rdF S i b c) • oneT S i j b x := by
  change (1 : KB S i b) ⊗ₜ[S.Ks] (c • x) = (ιK S i b c : KB S i b) • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  congr 1

theorem oneT_smul_int (c : 𝓞 S.Ks) (y : S.WL j) (h : y ∈ (S.A j).WK) (h' : c • y ∈ (S.A j).WK) (o : tw.O i)
    (ho : algebraMap (tw.O i) (FractionRing (tw.O i)) o = (ιK S i b (c : S.Ks) : KB S i b)) :
    oneT S i j b (mkF S j (c • y) h') = o • oneT S i j b (mkF S j y h) := by
  have h1 : (mkF S j (c • y) h') = (c : S.Ks) • (mkF S j y h) :=
    Subtype.ext (algebraMap_smul S.Ks c y).symm
  have ho' : algebraMap (tw.O i) (FractionRing (tw.O i)) o = rdF S i b (c : S.Ks) := ho
  rw [h1, oneT_smul, ← ho', algebraMap_smul]

theorem Bsup_fg (hF : (S.A j).MKFull) : (Bsup S i j b).FG := by
  obtain ⟨⟨T, hT⟩, -⟩ := hF
  have hTW : ∀ t ∈ (T : Set (S.WL j)), t ∈ (S.A j).MK := fun t ht => hT ▸ Submodule.subset_span ht
  let val : FmK S j → S.WL j := fun x => (show ↥(S.A j).WK from x).1
  have hval : Function.Injective val := Subtype.val_injective
  let gens : Set (Fm S i j b) := oneT S i j b '' (val ⁻¹' (T : Set (S.WL j)))
  have hfin : gens.Finite := ((T.finite_toSet).preimage hval.injOn).image _
  have aux : ∀ y ∈ Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK,
      oneT S i j b (mkF S j y h) ∈ Submodule.span (tw.O i) gens := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, -⟩ := hTW y hy
      exact ⟨h, Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩⟩
    | zero =>
      refine ⟨(S.A j).WK.zero_mem, ?_⟩
      have : oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0 := oneT_zero S i j b
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      refine ⟨(S.A j).WK.add_mem h1 h3, ?_⟩
      have : oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) =
          oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3) :=
        oneT_add S i j b (mkF S j x h1) (mkF S j y h3)
      rw [this]
      exact Submodule.add_mem _ h2 h4
    | smul c x _ hx =>
      obtain ⟨h1, h2⟩ := hx
      have h3 : c • x ∈ (S.A j).WK := by
        rw [← algebraMap_smul S.Ks c x]
        exact (S.A j).WK.smul_mem _ h1
      obtain ⟨o, ho⟩ := exists_int_read S i b c
      refine ⟨h3, ?_⟩
      rw [oneT_smul_int S i j b c x h1 h3 o ho]
      exact Submodule.smul_mem _ _ h2
  refine Submodule.fg_def.2 ⟨gens, hfin, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨t, ht, rfl⟩
    exact Submodule.subset_span ⟨t, hTW _ ht, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [show (S.A j).MK = Submodule.span (𝓞 S.Ks) (T : Set (S.WL j)) from hT.symm] at hx
    obtain ⟨h, h'⟩ := aux _ hx
    exact h'

theorem Bsup_span (hF : (S.A j).MKFull) :
    Submodule.span (FractionRing (tw.O i)) (Bsup S i j b : Set (Fm S i j b)) = ⊤ := by
  obtain ⟨-, hS⟩ := hF
  let B := Submodule.span (FractionRing (tw.O i)) (Bsup S i j b : Set (Fm S i j b))
  have aux : ∀ y ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)), ∃ h : y ∈ (S.A j).WK,
      oneT S i j b (mkF S j y h) ∈ B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, h'⟩ := id hy
      exact ⟨h, Submodule.subset_span (Submodule.subset_span ⟨mkF S j y h, hy, rfl⟩)⟩
    | zero =>
      refine ⟨(S.A j).WK.zero_mem, ?_⟩
      have : oneT S i j b (mkF S j 0 (S.A j).WK.zero_mem) = 0 := oneT_zero S i j b
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      obtain ⟨h1, h2⟩ := hx
      obtain ⟨h3, h4⟩ := hy
      refine ⟨(S.A j).WK.add_mem h1 h3, ?_⟩
      have : oneT S i j b (mkF S j (x + y) ((S.A j).WK.add_mem h1 h3)) =
          oneT S i j b (mkF S j x h1) + oneT S i j b (mkF S j y h3) :=
        oneT_add S i j b (mkF S j x h1) (mkF S j y h3)
      rw [this]
      exact Submodule.add_mem _ h2 h4
    | smul c x _ hx =>
      obtain ⟨h1, h2⟩ := hx
      refine ⟨(S.A j).WK.smul_mem c h1, ?_⟩
      have : oneT S i j b (mkF S j (c • x) ((S.A j).WK.smul_mem c h1)) =
          (rdF S i b c) • oneT S i j b (mkF S j x h1) :=
        oneT_smul S i j b c (mkF S j x h1)
      rw [this]
      exact Submodule.smul_mem _ _ h2
  have hall : ∀ (a : KB S i b) (x : FmK S j),
      ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) ∈ B := by
    intro a x
    have hx : (show ↥(S.A j).WK from x).1 ∈ Submodule.span S.Ks ((S.A j).MK : Set (S.WL j)) := by
      rw [hS]; exact (show ↥(S.A j).WK from x).2
    obtain ⟨h, h'⟩ := aux _ hx
    have e : ((a ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) : Fm S i j b) =
        (rdK S i b a) • oneT S i j b x := by
      change a ⊗ₜ[S.Ks] x = a • ((1 : KB S i b) ⊗ₜ[S.Ks] x)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e]
    exact Submodule.smul_mem _ _ h'
  refine eq_top_iff.2 fun t _ => ?_
  change t ∈ B
  induction (show KB S i b ⊗[S.Ks] FmK S j from t) using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul a x => exact hall a x
  | add x y hx hy => exact Submodule.add_mem _ hx hy

theorem actG_Bsup [Finite S.G] (hst : RhoStab S j) (hχ : ChiInLL0 S j)
    (hM : ∀ g x, x ∈ (S.A j).MK → (S.A j).ρ g x ∈ (S.A j).MK) (g : G0g N) (f : Fm S i j b)
    (hf : f ∈ Bsup S i j b) : actG S i j b hst hχ g f ∈ Bsup S i j b := by
  obtain ⟨o, ho⟩ := exists_chi_read S i b j hχ (S.eG.symm g)
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨x, hx, rfl⟩ := hf
    have e : actG S i j b hst hχ g ((1 : KB S i b) ⊗ₜ[S.Ks] x : KB S i b ⊗[S.Ks] FmK S j) =
        o • oneT S i j b (rhoKG S j hst (S.eG.symm g) x) := by
      rw [← algebraMap_smul (FractionRing (tw.O i)) o, ho]
      change ((readLL0 S i b (chiL S j hχ (S.eG.symm g)))⁻¹ •
        Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j hst (S.eG.symm g)))
          ((1 : KB S i b) ⊗ₜ[S.Ks] x) = _
      rw [LinearMap.smul_apply]
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hM _ _ hx, rfl⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [← algebraMap_smul (FractionRing (tw.O i)) c x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

end Base

section Tied

open Formalism.IndefR.Links NX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option synthInstance.maxHeartbeats 400000 in
theorem sup_of_tied (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw)
    (Y : NExpRealS Rl cG S)
    (hEq : ∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ Y.eF i j b h1 h2 x ∈ Bsup S i j b)
    (hI : RealDat.LIntegral Rl.toRealDat) : SupG D ∧ SupFull D := by
  have key : ∀ j, j ∈ Finset.Icc 1 D.R.m → ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    exact ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine ⟨?_, ?_⟩
  · intro i _ j hj b g f hf
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ := key j hj
    haveI : Finite S.G := Finite.of_equiv G (Y.fi k).eG.symm.toEquiv
    have hst := iso_MKStable (Y.fi k) (hI k).2.2
    rw [hEq i _ b h1 h2, Y.act]
    exact actG_Bsup S i _ b (Y.rho _ h1 h2) (Y.chi _ h1 h2) (fun g x hx => (hst g x).2 hx) g _
      ((hEq i _ b h1 h2 f).1 hf)
  · intro i _ j hj b
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨k, rfl⟩ := key j hj
    have hF := iso_MKFull (Y.fi k) (hI k).2.1
    let e := Y.eF i _ b h1 h2
    let eO := e.restrictScalars (D.ntw.O i)
    have hB : D.nexp.Bsup i _ b = (Bsup S i _ b).map eO.symm.toLinearMap := by
      ext x
      rw [Submodule.mem_map_equiv]
      exact hEq i _ b h1 h2 x
    refine ⟨hB ▸ (Bsup_fg S i _ b hF).map _, ?_⟩
    have hC : (D.nexp.Bsup i ((k : ℕ) + 1) b : Set (D.nexp.Fm i ((k : ℕ) + 1) b)) = e.symm.toLinearMap '' (Bsup S i ((k : ℕ) + 1) b : Set (Fm S i ((k : ℕ) + 1) b)) := by
      rw [hB]
      rfl
    rw [hC, ← Submodule.map_span, Bsup_span S i _ b hF, Submodule.map_top]
    exact LinearEquiv.range e.symm

end Tied

theorem supG_supFull_of_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS R cG S), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) → R.toRealDat.LIntegral → SupG D ∧ SupFull D := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R cG S YS hEq hI
  exact sup_of_tied R cG S YS hEq hI

end GlobalTheory.SupEq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRationalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedFormSupLattice_full_groupStable_of_eq_rational : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS R cG S), (∀ i j b (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (x : D.nexp.Fm i j b), x ∈ D.nexp.Bsup i j b ↔ YS.eF i j b h1 h2 x ∈ NX.Bsup S i j b) → R.toRealDat.LIntegral → SupG D ∧ SupFull D := by
  first | exact @GlobalTheory.SupEq.supG_supFull_of_eq | exact GlobalTheory.SupEq.supG_supFull_of_eq | (intros; apply GlobalTheory.SupEq.supG_supFull_of_eq <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem supLaws_of_sides (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E)
    (h : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) :
    SupG D ∧ SupFull D ∧ SupHk D ∧ CommG D ∧ HkComm D := by
  obtain ⟨h1, h2⟩ := GlobalTheory.T.twistedFormSupLattice_full_groupStable_of_eq_rational D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS Y.sup X.integral
  obtain ⟨h3, h4⟩ := GlobalTheory.T.hecke_preserves_supLattice_and_commutes_typeGroup D X E Y h
  exact ⟨h1, h2, h3, h4, GlobalTheory.T.splitPlaceHeckeCommute_of_twistSeriesSideData D X E Y⟩

end GlobalTheory.TwInputs
