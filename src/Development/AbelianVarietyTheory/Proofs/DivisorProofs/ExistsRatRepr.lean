module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelChangeActionOnCuspForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergLawApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitaryOnWeilDatumTransportAdelicSchwartz

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatRepr
open GlobalTheory.SqTop

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.CMVal
open Formalism.L2.Host (HChar)

namespace GlobalTheory.ToricExist

theorem exists_rat_repr (D : D7) {w : D.host.E} (hw : w ^ 2 = -(D.host.d : D.host.E)) (hd : 0 < D.host.d)
    (σ : D.host.E →+* ℂ) (hσ : σ w = Complex.I * (Real.sqrt D.host.d : ℝ)) :
    w ∈ D.host.K ∧ ∀ y : D.host.K, ∃ a b : ℚ, (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w := by
  set bb : D.host.E := D.host.sqd with hbb
  have hb : bb ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hbK : bb ∈ D.host.K := IntermediateField.mem_adjoin_simple_self ℚ _
  have hwb : w = bb ∨ w = -bb := by
    have h0 : (w - bb) * (w + bb) = 0 := by
      have : (w - bb) * (w + bb) = w ^ 2 - bb ^ 2 := by ring
      rw [this, hw, hb, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hwK : w ∈ D.host.K := by
    rcases hwb with h | h
    · rw [h]; exact hbK
    · rw [h]; exact neg_mem hbK
  refine ⟨hwK, fun y => ?_⟩
  let wK : D.host.K := ⟨w, hwK⟩
  have hli : LinearIndependent ℚ ![(1 : D.host.K), wK] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 : (s : D.host.E) + (t : D.host.E) * w = 0 := by
      have := congrArg Subtype.val hst
      simpa [Rat.smul_def, wK] using this
    have h1 := congrArg σ h0
    simp only [map_add (f := _), map_mul, map_ratCast, map_zero, hσ] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp at hre him
    refine ⟨by exact_mod_cast hre, ?_⟩
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h hd.ne'
  have hcard : Fintype.card (Fin 2) = Module.finrank ℚ D.host.K := by
    rw [GlobalTheory.CurveLattice.finrank_hostK]; rfl
  let B := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hB : ∀ i, B i = ![(1 : D.host.K), wK] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨B.repr y 0, B.repr y 1, ?_⟩
  have e := B.sum_repr y
  rw [Fin.sum_univ_two, hB, hB] at e
  have e2 := congrArg (fun z : D.host.K => (z : D.host.E)) e
  simp only [IntermediateField.coe_add, IntermediateField.coe_smul, Matrix.cons_val_zero, Matrix.cons_val_one,
    IntermediateField.coe_one, Rat.smul_def, mul_one] at e2
  rw [← e2]
  rfl

theorem exists_phiK (D : D7) (hFD : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) :
    ∃ φK : D.host.K →+* ℂ, (∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK) ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf φK 1 Λ := by
  obtain ⟨-, hd4, -, -, -, hcard, -, w, hw, hwφ⟩ := hFD
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨τ₀⟩ := hne
  obtain ⟨hwK, hrep⟩ := exists_rat_repr D hw (by omega) (cmPhi D τ₀) (hwφ τ₀)
  let φK : D.host.K →+* ℂ := (cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)
  have hval : ∀ (τ : D.what₂.Tau) (y : D.host.K) (a b : ℚ), (y : D.host.E) = (a : D.host.E) + (b : D.host.E) * w →
      cmPhi D τ (y : D.host.E) = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ)) := by
    intro τ y a b h
    rw [h, map_add (f := _), map_mul, map_ratCast, map_ratCast, hwφ τ]
  have hcomp : ∀ τ, (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = φK := fun τ => by
    ext y
    obtain ⟨a, b, h⟩ := hrep y
    show cmPhi D τ (y : D.host.E) = cmPhi D τ₀ (y : D.host.E)
    rw [hval τ y a b h, hval τ₀ y a b h]
  refine ⟨φK, hcomp, fun Λ hΛ => ?_⟩
  have hinj : Function.Injective φK := φK.injective
  ext x
  simp only [Set.mem_image, SetLike.mem_coe]
  constructor
  · intro hx
    obtain ⟨hint, a, b, rfl⟩ := (hΛ x).1 hx
    let y : D.host.K := (a : D.host.K) + (b : D.host.K) * ⟨w, hwK⟩
    have hy : φK y = (a : ℂ) + (b : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℝ)) := by
      show cmPhi D τ₀ (y : D.host.E) = _
      exact hval τ₀ y a b (by simp [y])
    refine ⟨y, ?_, hy⟩
    have hyi : IsIntegral ℤ y := (isIntegral_algHom_iff φK.toIntAlgHom hinj).1 (by rw [← hy] at hint; exact hint)
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨y, hyi⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨y', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
    obtain ⟨a, b, h⟩ := hrep (algebraMap (𝓞 D.host.K) D.host.K y')
    refine (hΛ _).2 ⟨?_, a, b, hval τ₀ _ a b h⟩
    exact (RingOfIntegers.isIntegral_coe y').map φK.toIntAlgHom

theorem gBig_of {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem gBig_and {P Q : GP} (hP : GBig P) (hQ : GBig Q) :
    GBig fun {_ _ _ _} G μ₀ C x b => P G μ₀ C x b ∧ Q G μ₀ C x b := by
  obtain ⟨CF1, h1⟩ := hP
  obtain ⟨CF2, h2⟩ := hQ
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, k1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, k2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => ⟨?_, ?_⟩⟩
  · exact k1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hr T Lc μ₀ hμ G
  · exact k2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hr T Lc μ₀ hμ G

theorem exists_prime {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h : IsBaseCond 𝔣) :
    Nonempty (HeightOneSpectrum (𝓞 E)) := by
  obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal 𝔣 h.2.1
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, fun e => h.1 (eq_bot_iff.2 (e ▸ hfM))⟩
  obtain ⟨P, -⟩ := (h.2.2 v (Ideal.dvd_iff_le.2 hfM)).1
  exact ⟨P⟩

theorem torEx : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LNe → TorEx := by
  intro hT hF hL
  refine gBig_of (gBig_and hF hL) ?_
  intro D T Lc sc G μ₀ C x b hμ ⟨hf, hl⟩ i j s hs1 hs2 c
  obtain ⟨hCM, hAb, hFD, hBC, -⟩ := hf
  have hFD' := hFD
  obtain ⟨-, hd4, hU, -, -, hcard, hφ, -⟩ := hFD
  have hV : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) := by
    cases c with
    | none => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).1
    | some c => exact (GlobalTheory.FunObj.SqNum.Model.isValChar_nu hμ G i j hs2).2 c
  obtain ⟨P⟩ := exists_prime hBC
  have hAux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) ∅ := fun q hq => absurd hq (Finset.notMem_empty q)
  have hTS : ∀ Λ, IsHeckeL (fam G μ₀ i j c) Λ →
      IsToricSum (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) (fam G μ₀ i j c) (Λ s) := fun Λ hΛ => by
    have := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
      (kap D sc.cGap i j s) (condF G.pl) ∅ (fam G μ₀ i j c) (fun _ => P) Λ hU hs1 hBC hAux hV
      (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ
    simpa [condQ] using this
  obtain ⟨Λ, hΛ, hne⟩ := (hl i j).2 c
  refine ⟨Λ s, ⟨hV, hTS Λ hΛ⟩, hne s hs1, fun Λ' h => by rw [hΛ.unique h], fun Λ₁ hΛ₁ => ?_⟩
  obtain ⟨φK, hcomp, hlat⟩ := exists_phiK D hFD'
  haveI := hCM
  haveI := hAb
  obtain ⟨t, 𝔞, Λσ, -, -, hTr⟩ := hT D.host.K D.host.d hd4 (GlobalTheory.CurveLattice.finrank_hostK D)
    (GlobalTheory.CurveLattice.discr_hostK D) φK Λ₁ (hlat Λ₁ hΛ₁)
  have hk := hTr D.host.E hU D.what₂.Tau (cmPhi D) hcard hφ hcomp s (kap D sc.cGap i j s) (condF G.pl) hs1
    (fun τ => (GlobalTheory.FunObj.SqNum.Model.kap_add D sc.cGap i j τ hs2).2) hBC
  exact (hk.1 ∅ _ _ ⟨hAux, hV, by simpa [condQ] using hTS Λ hΛ⟩).1

end GlobalTheory.ToricExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRuns
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRuns
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelActionOnto

def quotMap {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
  (I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R M)) f
    (Submodule.map_le_iff_le_comap.1 (by rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top))

theorem quotMap_mk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) (a : M) :
    quotMap I f ((I • (⊤ : Submodule R M)).mkQ a) = (I • (⊤ : Submodule R M)).mkQ (f a) := rfl


open Classical in
def quotEquiv {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M) :
    (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] (M ⧸ I • (⊤ : Submodule R M)) :=
  if hb : Function.Bijective (quotMap I f) then LinearEquiv.ofBijective _ hb else LinearEquiv.refl R _

theorem quotEquiv_mk {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f : M →ₗ[R] M)
    (hb : Function.Bijective (quotMap I f)) (a : M) :
    quotEquiv I f ((I • (⊤ : Submodule R M)).mkQ a) = (I • (⊤ : Submodule R M)).mkQ (f a) := by
  unfold quotEquiv
  rw [dite_eq_left hb]
  rfl

theorem quotMap_bijective {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (f f' : M →ₗ[R] M)
    (h1 : ∀ a, f (f' a) - a ∈ I • (⊤ : Submodule R M)) (h2 : ∀ a, f' (f a) - a ∈ I • (⊤ : Submodule R M)) :
    Function.Bijective (quotMap I f) := by
  have k1 : ∀ q, quotMap I f (quotMap I f' q) = q := fun q => by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [quotMap_mk, quotMap_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h1 a
  have k2 : ∀ q, quotMap I f' (quotMap I f q) = q := fun q => by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [quotMap_mk, quotMap_mk, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact h2 a
  exact ⟨Function.LeftInverse.injective k2, Function.RightInverse.surjective k1⟩

end GlobalTheory.LevelActionOnto

namespace GlobalTheory.LevelActionOnto

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem levelPin_actionPin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → (∀ i, OMPins J R κ v₀ O i) → RhoGeo fw O → (∀ i, OneMapRow0 J R κ v₀ O i) → J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∃ ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l), ∀ (r : RunData J) (h : LawsFull r.full) (i : Fin D.R.m), letI : Algebra r.full.J.Q.c.F D.what₂.LL := ‹Algebra J.Q.c.F D.what₂.LL›; LevelPin (T := r.full) R i (ℓ i) ∧ ActionPin (T := r.full) (R := R) h.p fw i (ℓ i) := by
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw O hc hpins hrho hrow hMb
  classical
  refine ⟨fun i g => quotEquiv J.Q.l.Mb ((O i).lev g), fun r h i => ?_⟩
  have hlev : LevIs R i (iotaW J i) J.Q.l.M (Mfr J.Q.l) (O i).lev := (hpins i).2.lift.lev
  have hι : LatEmb (Wc D i) (iotaW J i) := GlobalTheory.TraceLattice.latEmb_iotaW h i
  have hβ : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1 := hc.lev.βW i
  obtain ⟨h1, hm⟩ := GlobalTheory.LevelActionPinned.congr_of_levIs R i hι hβ hMb hlev
  have hbij : ∀ g, Function.Bijective (quotMap J.Q.l.Mb ((O i).lev g)) := fun g => by
    refine quotMap_bijective _ _ ((O i).lev g⁻¹) (fun a => ?_) (fun a => ?_)
    · have e1 := hm g g⁻¹ a
      have e2 := h1 a
      rw [mul_inv_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
    · have e1 := hm g⁻¹ g a
      have e2 := h1 a
      rw [inv_mul_cancel] at e1
      have := Submodule.sub_mem _ e2 e1
      rwa [sub_sub_sub_cancel_left] at this
  have hspec : ∀ g a, liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a - (O i).lev g a ∈
      J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := fun g a => by
    rw [← Submodule.Quotient.eq]
    have := liftLa_spec (quotEquiv J.Q.l.Mb ((O i).lev g)) a
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at this
    rw [this]
    exact quotEquiv_mk _ _ (hbij g) a
  have hA : J.Q.l.A = 1 := h.j.pins.2.1.2
  refine ⟨?_, ?_⟩

  · change LevIs R i (iotaW J i) J.Q.l.M (Mfr J.Q.l) (fun g => liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)))
    intro g
    obtain ⟨k, hk, hw⟩ := hlev g
    refine ⟨k, hk, fun a ha => ?_⟩
    obtain ⟨w, hwm, e⟩ := hw a ha
    have hd : liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a - (O i).lev g a ∈
        (Ideal.span {(J.Q.l.M : 𝓞 D.host.E)}) • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := by
      rw [← J.Q.l.prod, mul_comm, Submodule.mul_smul]
      have key : ∀ f : (J.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (J.Q.Dw ((i : ℕ) + 1)).La,
          (∀ x, f x ∈ J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La)) →
          f a ∈ Mfr J.Q.l • J.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (J.Q.Dw ((i : ℕ) + 1)).La) := fun f hf => by
        refine Submodule.smul_induction_on ha (fun b hb x _ => ?_) (fun x y hx hy => ?_)
        · rw [map_smul]
          exact Submodule.smul_mem_smul hb (hf x)
        · rw [map_add (f := _)]
          exact add_mem hx hy
      exact key (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) - (O i).lev g) (hspec g)
    rw [Submodule.ideal_span_singleton_smul] at hd
    obtain ⟨y, -, hy⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hd
    have hy' : liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a = (O i).lev g a + J.Q.l.M • y := by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), hy, add_sub_cancel]
    have hmem : finVec (Wc D i) (iotaW J i y) ∈ latGHat (Wc D i) 1 :=
      ((GlobalTheory.MarkCoset.latG_spec D (Wc D i) 1).1 _).1 (hι.2 ▸ LinearMap.mem_range_self (iotaW J i) y)
    refine ⟨w + finVec (Wc D i) (iotaW J i y), add_mem hwm hmem, ?_⟩
    have e2 : GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a) =
        GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) ((O i).lev g a) +
          J.Q.l.M • GlobalTheory.LevelActionPinned.fvec (Wc D i) (iotaW J i) y := by
      rw [hy', map_add (f := _), map_nsmul]
    have e3 : finVec (Wc D i) (iotaW J i (liftLa (quotEquiv J.Q.l.Mb ((O i).lev g)) a)) =
        finVec (Wc D i) (iotaW J i ((O i).lev g a)) + J.Q.l.M • finVec (Wc D i) (iotaW J i y) := e2
    rw [e3, nsmul_add, ← e]
    abel

  · obtain ⟨cc, ph, hone⟩ := hrow i
    have hkeep : ActKeeps (κ := κ) O i := fun g f hf => by
      obtain ⟨k, hk, -⟩ := hlev g
      exact (hone.1 g k hk f hf).1
    have hrho' := (hrho i).1 hkeep
    have hact_eq : ∀ g, actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)
        (quotEquiv J.Q.l.Mb ((O i).lev g)) = actLev J.Q.c (O i).lev2 g := fun g => by
      have e1 : actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)
          (quotEquiv J.Q.l.Mb ((O i).lev g)) = actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c
          (fun _ : Unit => levFull (J.Q.Dw ((i : ℕ) + 1)) J.Q.l (quotEquiv J.Q.l.Mb ((O i).lev g))) () := rfl
      have e2 : actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (O i).lev2 g =
          actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (fun _ : Unit => (O i).lev2 g) () := rfl
      rw [e1, e2, GlobalTheory.OneMapAllCompare.actLev_congr (lev' := fun _ : Unit => (O i).lev2 g) J.Q.c hA (fun _ a => hspec g a)]
    obtain ⟨act, hact⟩ := GlobalTheory.FormTies.exists_isLevAct D r.full.toTop h.p ((i : ℕ) + 1) (inR_succ i) (κ i) G
      (fun g => quotEquiv J.Q.l.Mb ((O i).lev g))
    refine ⟨act, hact, fun g F => ?_⟩
    obtain ⟨hf, he⟩ := hrho' g ⟨F.1, cutR_le J.toCore.C ((i : ℕ) + 1) (κ i) F.2⟩
    have e : (act g F).1 = actLev (Xo := J.Q.Xo ((i : ℕ) + 1)) J.Q.c (O i).lev2 g F.1 := (hact g F).trans (LinearMap.congr_fun (hact_eq g) F.1)
    change ((fw.e i ⟨(act g F).1, _⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (R.FW i).ρ g ((fw.e i ⟨F.1, _⟩ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)
    rw [← he]
    congr 3

end GlobalTheory.LevelActionOnto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupLevelStructureActionFixedRunsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteGroup_levelStructure_action_fixedRuns : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (O : ∀ i, OMDat J.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → (∀ i, OMPins J R κ v₀ O i) → RhoGeo fw O → (∀ i, OneMapRow0 J R κ v₀ O i) → J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → ∃ ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l), ∀ (r : RunData J) (h : LawsFull r.full) (i : Fin D.R.m), letI : Algebra r.full.J.Q.c.F D.what₂.LL := ‹Algebra J.Q.c.F D.what₂.LL›; LevelPin (T := r.full) R i (ℓ i) ∧ ActionPin (T := r.full) (R := R) h.p fw i (ℓ i) := by
  first | exact @GlobalTheory.LevelActionOnto.levelPin_actionPin | exact GlobalTheory.LevelActionOnto.levelPin_actionPin | (intros; apply GlobalTheory.LevelActionOnto.levelPin_actionPin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitIdelesOpen
noncomputable section

namespace GlobalTheory.ThK.ConeEuler.UnitsOpen

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

section Lemmas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isOpen_integral_everywhere : IsOpen {z : AE F E | ∀ v : Pl F, compFin F E v z ∈ intLoc F E v} := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := GlobalTheory.Doubling.isTopologicalRing_tens
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  let S : AddSubgroup (AE F E) :=
    { carrier := {z | ∀ v : Pl F, compFin F E v z ∈ intLoc F E v}
      zero_mem' := fun v => by rw [map_zero]; exact zero_mem _
      add_mem' := fun ha hb v => by rw [map_add]; exact add_mem (ha v) (hb v)
      neg_mem' := fun ha v => by rw [map_neg]; exact neg_mem (ha v) }
  let b := integralBasis E
  let φ : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → AF F) →ₗ[AF F] AE F E :=
    Fintype.linearCombination (AF F) fun i => (1 : AF F) ⊗ₜ[F] b i
  have hφ : ∀ a, φ a = ∑ i, a i ⊗ₜ[F] b i := fun a => by
    simp only [φ, Fintype.linearCombination_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hq : ∀ (c : ℚ) (a : AF F) (x : E), a ⊗ₜ[F] (c • x) = (algebraMap F (AF F) (c : F) * a) ⊗ₜ[F] x := fun c a x => by
    rw [show c • x = (c : F) • x by rw [Rat.cast_smul_eq_qsmul], ← TensorProduct.smul_tmul, Algebra.smul_def]
  have hsurj : Function.Surjective φ := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a x =>
      refine ⟨fun i => algebraMap F (AF F) (b.repr x i : F) * a, ?_⟩
      rw [hφ]
      conv_rhs => rw [← b.sum_repr x, TensorProduct.tmul_sum]
      exact Finset.sum_congr rfl fun i _ => (hq _ _ _).symm
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨c, rfl⟩ := hy
      exact ⟨a + c, map_add _ _ _⟩
  let W : Set (AF F) := {a | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  have ho : IsOpen W :=
    (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) =>
      Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd
  have hopen : IsOpen (φ '' Set.univ.pi fun _ => W) :=
    (IsModuleTopology.isOpenQuotientMap_of_surjective hsurj).isOpenMap _
      (isOpen_set_pi Set.finite_univ fun _ _ => ho)
  have hsub : φ '' (Set.univ.pi fun _ => W) ⊆ (S : Set (AE F E)) := by
    rintro _ ⟨a, ha, rfl⟩ v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ, map_sum]
    refine sum_mem fun i _ => ?_
    rw [show b i = ((RingOfIntegers.basis E i : 𝓞 E) : E) from integralBasis_apply E i]
    exact tmul_mem_intLoc (ha i (Set.mem_univ i) v) _
  have h0 : (0 : AE F E) ∈ φ '' (Set.univ.pi fun _ => W) :=
    ⟨0, fun i _ v => by simp, map_zero φ⟩
  exact (AddSubgroup.isOpen_of_mem_nhds S (g := 0) (Filter.mem_of_superset (hopen.mem_nhds h0) hsub) :
    IsOpen (S : Set (AE F E)))

end Lemmas

end GlobalTheory.ThK.ConeEuler.UnitsOpen

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

end GlobalTheory.ThK.ConeEuler
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVPairVW
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVPairVW
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.WeilLocalityV

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (hTr : IsTriple B G X om om') (v : Pl (F := F)) (g : UA σ G.V.J) (hg : g ∈ UAt σ G.V (evFin F v))
    (u : AF F) (hu : evFin F v u = 0) (p q : Fin a × Fin (a + a') → AF F)
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))) :
      om (g, 1) (GlobalTheory.WeilM.schr B.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr B.ψ (u • p, u • q) (om (g, 1) Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set w := G.M.co.e.symm (p, q) with hw
  have he : G.M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat g - 1) = 0 := hg u hu
  have hact : GlobalTheory.WeilM.actAB (cA σ) ((g, 1) : UA σ G.V.J × UA σ G.W.J) (u • w) = u • w := by
    have h1 : mat g * (u • w) - u • w = (u • (mat g - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h0, Matrix.zero_mul, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [mat] using h1
  have h2 := hW.impl (g, 1) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem locality : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v g hg φ hφ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set T := om (g, 1) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (g, 1) Φ hΦ
  have hcomm := comm_off B G X om om' hTr v g hg
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v B.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace B.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (g, 1) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h' := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h'
    exact h'
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  refine ⟨fun t => (R 0)⁻¹ * T (tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := tens (evFin F v) φ R with hΦ₀
    set Φ₁ := tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [tens, hpdef]
    field_simp

end GlobalTheory.WeilLocalityV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVPairVWStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentationLocality_unitaryGroupV_pairVW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)), ∀ g ∈ UAt σ G.V (evFin F v), ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (g, 1)) φ φ₁ := by
  first | exact @GlobalTheory.WeilLocalityV.locality | exact GlobalTheory.WeilLocalityV.locality | (intros; apply GlobalTheory.WeilLocalityV.locality <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEq
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.AbsHalfConj

theorem ordL_congr {L L' : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] [Field L']
    [Valued L' (WithZero (Multiplicative ℤ))] {a : L} {b : L'} (h : Valued.v a = Valued.v b) : ordL a = ordL b := by
  unfold ordL
  by_cases ha : Valued.v a = 0
  · rw [dite_eq_left ha, dite_eq_left (h ▸ ha)]
  · rw [dite_eq_right ha, dite_eq_right (h ▸ ha)]
    congr 2
    exact WithZero.coe_inj.1 (by rw [WithZero.coe_unzero, WithZero.coe_unzero, h])

theorem absHalf_conjPl : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ x : E, absHalf u (algebraMap E (u.adicCompletion E) x) = absHalf w (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
  intro E _ _ _ w u hne hund x
  have hcu : GlobalTheory.Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w u :=
    ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w u).1 hund).resolve_left hne
  have hv : Valued.v (algebraMap E (u.adicCompletion E) x) =
      Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
    have h1 : Valued.v (algebraMap E (u.adicCompletion E) x) = u.valuation E x :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u x
    have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) =
        w.valuation E (IsCMField.complexConj E x) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
    rw [h1, h2]
    have := hcu (IsCMField.complexConj E x)
    simp only [AlgEquiv.coe_ringEquiv, IsCMField.complexConj_apply_apply] at this
    exact this
  have hq : qV E u = qV E w := by
    unfold qV
    rw [eq_conjSrc hcu, GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc]
  unfold absHalf
  rw [ordL_congr hv, hq]

end GlobalTheory.BCT.AbsHalfConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfConjugatePlaceEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absHalf_conjugatePlace_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w u : Pl E), u ≠ w → u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) → ∀ x : E, absHalf u (algebraMap E (u.adicCompletion E) x) = absHalf w (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x)) := by
  first | exact @GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl | exact GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl | (intros; apply GlobalTheory.BCT.AbsHalfConj.absHalf_conjPl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqClassSumThetaKernelsLowestKType
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqClassSumThetaKernelsLowestKType
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftUnfoldCore


set_option maxHeartbeats 1000000 in
theorem thF_eq_classSum_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'), VStd D i → RepsR R i t h bad J' Lh gam vol → ∀ (y : (R.HV i t).H) (x : Cl → VsV D i K'), Place R i t h c0' y x → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ∑ k, σ' (vol * ((gam k : K'))⁻¹) * thetaKO (R.ωP i t) (h k) g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (c0' (x k)))) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t K' _ σ' c0' Cl _ h bad J' Lh gam vol hV hrep y x hpl u g
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  have hle := hrep.2.2.1
  have hN := hrep.2.2.2.1
  have hvol := hrep.2.2.2.2.1
  have hy := hrep.2.2.2.2.2.1
  have hk := hrep.2.2.2.2.2.2
  have hx : (R.HV i t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.models.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hx
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) J' Cl h hle hN hy (fun k => (hk k).1.1) g
  have h1 := congrFun (hPF.2 y u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict y) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans (Finset.sum_congr rfl fun k _ => ?_))))
  · rfl
  have h3 : σ' (vol * ((gam k : K'))⁻¹) = ((J'.relIndex (levJ R i t) : ℕ) : ℂ)⁻¹ *
      ((Nat.card (Bridge.stab (Bridge.ratF (Vc D i)) J' (fin (Vc D i) (h k))) : ℕ) : ℂ)⁻¹ := by
    rw [map_mul σ', hvol, map_inv₀ σ', map_inv₀ σ', map_natCast σ', map_natCast σ', (hk k).2.2]
  rw [h3, ← hpl k]
  rfl

end GlobalTheory.LiftUnfoldCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEqClassSumThetaKernelsLowestKTypeStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_eq_classSum_thetaKernels_lowestKType : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (K' : Type) [Field K'] (σ' : K' →+* ℂ) (c0' : VsV D i K' →ₛₗ[σ'] (R.cV i).W) (Cl : Type) [Fintype Cl] (h : Cl → GA D (Vc D i)) (bad : ℕ) (J' : Subgroup (Bridge.Gf (Vc D i))) (Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)) (gam : Cl → ℕ) (vol : K'), VStd D i → RepsR R i t h bad J' Lh gam vol → ∀ (y : (R.HV i t).H) (x : Cl → VsV D i K'), Place R i t h c0' y x → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ∑ k, σ' (vol * ((gam k : K'))⁻¹) * thetaKO (R.ωP i t) (h k) g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) (c0' (x k)))) := by
  first | exact @GlobalTheory.LiftUnfoldCore.thF_eq_classSum_core | exact GlobalTheory.LiftUnfoldCore.thF_eq_classSum_core | (intros; apply GlobalTheory.LiftUnfoldCore.thF_eq_classSum_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseKernel
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnCmp


open Classical in
theorem exists_baseKernel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → ∃ ω φ, IsBaseKernel R i v (ownAt D v) ω φ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC i v hv hmu
  obtain ⟨ψw, Qw, hψ, hxi⟩ := hmu v hv
  have hL := hC.lev
  have hδ : R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v) = R.xiH (R.mu v) * ψw⁻¹ := by rw [hxi, mul_inv_cancel_right]
  have htame : ∀ P, (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TameAt P := by
    intro P
    unfold Formalism.L2.Host.HChar.TameAt Formalism.L2.Host.HChar.LevelLe
    intro x hx hle
    have loc_mul (a b : Formalism.L2.Host.HChar D.host.E) :
        (a * b).loc P x = a.loc P x * b.loc P x := rfl
    have loc_inv (a : Formalism.L2.Host.HChar D.host.E) :
        (a⁻¹).loc P x = (a.loc P x)⁻¹ := rfl
    rw [hδ, loc_mul, loc_inv, hL.xi_tame (R.mu v) P x hx hle, hψ.tame P x hx hle,
      inv_one, mul_one]
  have htriv : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).TrivOn D.host.F := by
    rw [hδ]; exact (hL.xi_triv (R.mu v)).mul hψ.triv.inv
  have hunit : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).IsUnitary := by
    obtain ⟨n, hn, hno⟩ := hL.xi_fin (R.mu v)
    obtain ⟨a, ha⟩ := hψ.ord
    refine Formalism.L2.Host.HChar.isUnitary_of_order (n := n * Formalism.EigenvalueLevelCeiling.plc v ^ a)
      (Nat.mul_pos hn (pow_pos (Formalism.EigenvalueLevelCeiling.plc_prime v).pos a)) ?_
    show _ ^ (n * _) = 1
    rw [hδ, mul_pow, inv_pow, pow_mul, hno, one_pow, one_mul, mul_comm n, pow_mul, ha, one_pow, inv_one]
  obtain ⟨χ, hχ⟩ := GlobalTheory.CharTransport.exists_chrEq D _ hunit
  have hF : ∀ a, χ (idF D a) = 1 := GlobalTheory.GridWeil.triv_base hχ htriv
  have hr0 : ResEta D χ 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ a => by rw [hF a, pow_zero]⟩
  have h0 := hC.thP.ωP i A.μ0
  obtain ⟨ω, hω, -⟩ := GlobalTheory.WeilChange.exists_weilDatum_twist D R.ψ h0.std _ _ _ _ χ χ _ h0 hχ.1 hχ.1 hr0 hr0
  have hx0 : R.xi A.μ0 = 1 :=
    MonoidHom.ext fun x => GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0) x
  have hω' : IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
      (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω := by
    convert hω using 2
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
    · simp only [Lift.chrTh, Lift.tup, LevCh.mu, hx0, mul_one]
      exact mul_right_comm _ _ _
  choose ξR hξR using fun PP => GlobalTheory.exists_isRes_of_tameAt D _ PP (htame PP)
  have hsub : placesOver R (R.mu v) (ownAt D v) ⊆ R.Q (R.mu v) := Finset.filter_subset _ _
  obtain ⟨e0, he0, -⟩ := (hC.thP.vP i (R.mu v)).2
  have hsub' : R.Pg ∪ placesOver R (R.mu v) (ownAt D v) ⊆ R.Pg ∪ R.Q (R.mu v) := Finset.union_subset_union le_rfl hsub
  have hnc : ∀ P ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v), ∀ P' ∈ R.Pg ∪ placesOver R (R.mu v) (ownAt D v),
      ¬ Lev.IsConjPl P P' := fun P hP P' hP' =>
    GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he0 P (hsub' hP) P' (hsub' hP')
  obtain ⟨cV, hcV⟩ := hL.βV i
  obtain ⟨cW, hcW⟩ := hL.βW i
  obtain ⟨φ, hφ⟩ := GlobalTheory.PlaceVec.thPVecExists D R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i)
    (R.ΛW i) (R.βV i) (R.βW i) R.Pg (placesOver R (R.mu v) (ownAt D v)) ξR (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcV)
    (GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hcW) hcV.1 hcW.1 ((Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hL (R.mu v)).mono_right hsub)
    (Formalism.IndefR.Fin.idemSum_of_noConj _ hnc) (R.vacP i) (hC.thP.vP i (R.mu v)).1
  refine ⟨ω, φ, ?_⟩
  unfold IsBaseKernel IsKernel
  exact ⟨χ, ξR, hχ, fun PP _ => hξR PP, hω', hφ⟩

end GlobalTheory.OnCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIntertwinesFockDerivati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIntertwinesFockDerivati
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.KInfComm

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ a b : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin n × Fin d), A (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) = GlobalTheory.ThK.EvAt0.PolD.dOp a' b' (A f) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk A hA a b
  have hB := hP.base
  have hw := hP.weil
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  have hpres : ∀ x, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d), om x Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun x Φ hΦ => hW.pres x Φ hΦ
  have h1 : (1 : UA σ X.J) ∈ UAt σ X (evI F) := by
    intro u _
    simp [mat]
  have hk1 : k ∈ UAt σ W (evI F) := hk.1
  obtain ⟨T₂, hT₂⟩ := GlobalTheory.ArchLocalAct.exists_op_of_UAt hB.std hw ((1 : UA σ X.J)⁻¹, k⁻¹)
    (GlobalTheory.RealConjFac.inv_mem_UAt h1) (GlobalTheory.RealConjFac.inv_mem_UAt hk1)
  have hid : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (1 : Module.End ℂ _) (⇑f) (⇑f) := fun f r _ => rfl
  have e21 : ∀ f, T₂ (A f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hA f) (hT₂ (A f))
    rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (T₂ (A f)) f).2.2.2.1 _ hc (hid f))
  have e12 : ∀ f, A (T₂ f) = f := by
    intro f
    have hc := GlobalTheory.RealConjFac.acts_comp (hpres _) (hT₂ f) (hA (T₂ f))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one] at hc
    exact ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) f (A (T₂ f)) f).2.2.2.1 _ hc (hid f))
  let T : SInf F (Fin n × Fin d) ≃ₗ[ℂ] SInf F (Fin n × Fin d) :=
    LinearEquiv.ofLinear A T₂ (LinearMap.ext e12) (LinearMap.ext e21)
  set u := M.co.e.symm (fun i => GlobalTheory.ThK.EvAt0.PolD.liftA (a i), fun i => GlobalTheory.ThK.EvAt0.PolD.liftA (b i)) with hu_def
  have hu := GlobalTheory.ThK.EvAt0.PolEv.at_symm M a b
  set u' := mat (1 : UA σ X.J) * u * (mat k).transpose with hu'_def
  have hu' : At (evI F) u' := by
    intro c hc
    rw [hu'_def, ← Matrix.smul_mul, ← Matrix.mul_smul, hu c hc, Matrix.mul_zero, Matrix.zero_mul]
  refine ⟨GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u').1, GlobalTheory.ThK.EvAt0.PolD.arc (M.co.e u').2, fun f => ?_⟩
  have hf : ActsD (evI F) (M.heisLine B.ψ u) f (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) := by
    refine (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std M u hu _ _).2 ?_
    rw [hu_def, LinearEquiv.apply_symm_apply, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA, GlobalTheory.ThK.EvAt0.PolEv.arc_liftA]
  have ht := GlobalTheory.HeisTransport.actsD_heisLine_transport F E σ B n d X W M χX χW om r s r' s' hB hP.herm hP.skew hP.good hw
    1 h1 k hk1 T (fun f => hA f) (fun f => hT₂ f) u hu f _ hf
  exact (GlobalTheory.ThK.EvAt0.PolEv.actsD_iff_dOp hB.std M u' hu' _ _).1 ht

end GlobalTheory.KInfComm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanMaximalCompactIntertwinesFockDerivatiStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanMaximalCompact_intertwines_fockDerivativeOps : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ W B.emb,
    ∀ A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d), (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) ⇑f ⇑(A f)) →
    ∀ a b : Fin n × Fin d → mixedEmbedding.mixedSpace F, ∃ a' b' : Fin n × Fin d → mixedEmbedding.mixedSpace F,
      ∀ f : SInf F (Fin n × Fin d), A (GlobalTheory.ThK.EvAt0.PolD.dOp a b f) = GlobalTheory.ThK.EvAt0.PolD.dOp a' b' (A f) := by
  first | exact @GlobalTheory.KInfComm.main | exact GlobalTheory.KInfComm.main | (intros; apply GlobalTheory.KInfComm.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

namespace GlobalTheory.WeylFour.SchrKeep

theorem schr_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ := by
  intro F _ _ ψ hψ κ _ w Φ hΦ
  exact GlobalTheory.ConeMeasV.schr_mem_schA hψ w hΦ

end GlobalTheory.WeylFour.SchrKeep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_preserves_schwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ := by
  first | exact @GlobalTheory.WeylFour.SchrKeep.schr_mem_schA | exact GlobalTheory.WeylFour.SchrKeep.schr_mem_schA | (intros; apply GlobalTheory.WeylFour.SchrKeep.schr_mem_schA <;> assumption)
end
end
