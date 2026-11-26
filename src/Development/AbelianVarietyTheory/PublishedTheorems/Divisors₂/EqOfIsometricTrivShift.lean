module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k}

def Isometric (L M : HermLB p) : Prop :=
  ∃ w : LB.Iso L.B M.B, w.IsGen ∧ ∀ (σ : k →+* ℂ) (a : M.B.ι) (b : L.B.ι) (y : CxPts p σ),
    y ∈ ptsIn p σ (M.B.U a) → y ∈ ptsIn p σ (L.B.U b) →
      (M.φ σ).φ a y = (L.φ σ).φ b y + Real.log (‖ev p σ _ (w.s (a, b)).val y‖ ^ 2)
private theorem res_res_lemma {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  ext
  change (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a.val) =
    (X.presheaf.map (homOfLE (h'.trans h)).op).hom a.val
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
private theorem isGen_iso_self_of_isLB (B : LB X) (hB : B.IsLB) :
    (⟨fun c => B.g c.1 c.2⟩ : LB.Iso B B).IsGen := by
  obtain ⟨-, -, hc⟩ := hB
  rintro ⟨a, b⟩ ⟨a', b'⟩
  have e1 := congrArg (res (fun x hx => by simp only [Opens.mem_inf] at hx ⊢; tauto :
    (B.U a ⊓ B.U b) ⊓ (B.U a' ⊓ B.U b') ≤ _)) (hc a a' b')
  have e2 := congrArg (res (fun x hx => by simp only [Opens.mem_inf] at hx ⊢; tauto :
    (B.U a ⊓ B.U b) ⊓ (B.U a' ⊓ B.U b') ≤ _)) (hc a b b')
  simp only [map_mul, res_res_lemma] at e1 e2
  dsimp only [LB.div]
  refine (eq_mul_inv_of_mul_eq e2).trans ?_
  rw [← e1]
  exact mul_right_comm _ _ _
private theorem iso_phi_eq_add_log_normSq_transition {B : LB X} (hB : B.IsLB) (φ ψ : ∀ σ : k →+* ℂ, Weight p σ B)
    (h : ∀ σ a, ∀ y ∈ ptsIn p σ (B.U a), (ψ σ).φ a y = (φ σ).φ a y) (σ : k →+* ℂ) (a b : B.ι)
    (y : CxPts p σ) (ha : y ∈ ptsIn p σ (B.U a)) (hb : y ∈ ptsIn p σ (B.U b)) :
    (ψ σ).φ a y = (φ σ).φ b y + Real.log (‖ev p σ (B.U a ⊓ B.U b) (B.g a b).val y‖ ^ 2) := by
  rw [h σ a y ha, (φ σ).trans a b y ha hb]
  exact (sub_add_cancel _ _).symm

theorem isometric_of_eqOn {B : LB X} {hB : B.IsLB} {φ ψ : ∀ σ : k →+* ℂ, Weight p σ B} {h₁ h₂ h₃ h₄}
    (h : ∀ σ a, ∀ y ∈ ptsIn p σ (B.U a), (ψ σ).φ a y = (φ σ).φ a y) :
    Isometric (p := p) ⟨B, hB, φ, h₁, h₂⟩ ⟨B, hB, ψ, h₃, h₄⟩ :=
  ⟨⟨fun c => B.g c.1 c.2⟩, isGen_iso_self_of_isLB B hB, fun σ a b y ha hb => iso_phi_eq_add_log_normSq_transition hB φ ψ h σ a b y ha hb⟩

theorem Isometric.refl (L : HermLB p) : L.Isometric L := by
  obtain ⟨B, hB, φ, h₁, h₂⟩ := L
  exact isometric_of_eqOn fun _ _ _ _ => rfl

def raise (M : HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) : HermLB p where
  B := M.B
  isLB := M.isLB
  φ σ := (M.φ σ).addFn (u σ)
  cInf σ := (M.cInf σ).addFn (hu σ)
  conj σ σ' c y y' h hy := congrArg₂ (· + ·) (M.conj σ σ' c y y' h hy)
    (hc σ σ' PUnit.unit y y' h mem_ptsIn_top)

end GlobalTheory.HermLB

namespace GlobalTheory.Published

def ArExists : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  (∀ L : HermLB p, ∃ h, L.IsArithHeight h) ∧
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p), (∃ Φ, IsArFun L D Φ) ∧ ∃ Ψ, IsGeoFun L D Ψ

def ArChange : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CxPts.CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
    IsArFun (fun o : Option ι => o.elim (fnB u hu hc) L) D Φ → ∀ n : ι → ℤ,
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u

def ArShift : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L : HermLB p) (a t : ℝ), L.IsSelfInter a →
    (L.shift (fun _ => t) fun _ => rfl).IsSelfInter (a + ((D : ℝ) + 1) * t * gdeg L D)

def ArMix : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ),
  IsArithVar p D → ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
    IsArFun (fun o : Option ι => o.elim M L) D Φ → ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h →
    ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr

def ArProj : Prop := ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
  (D : ℕ), IsArithVar p D → IsArithVar q D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X →
    π.residueDegree (genericPoint Y) ≠ 0 →
    (∀ (L : HermLB p) (a : ℝ), L.IsSelfInter a →
      (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * a)) ∧
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun L D Φ →
      IsArFun (fun i => (L i).pull π hπ) D ((π.residueDegree (genericPoint Y) : ℝ) • Φ)

def ArIso : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  (∀ (L M : HermLB p) (h : X → ℝ), L.Isometric M → L.IsArithHeight h → M.IsArithHeight h) ∧
  ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun L D Φ →
    (∀ i, (L i).IsSelfInter (Φ (MvPolynomial.X i ^ (D + 1)))) ∧
    (∀ M : ι → HermLB p, (∀ i, (L i).Isometric (M i)) → IsArFun M D Φ) ∧
    ∀ (κ : Type) [Fintype κ] (M : κ → HermLB p) (A : κ → ι → ℤ), (∀ j, (comb L (A j)).Isometric (M j)) →
      IsArFun M D (Φ ∘ₗ (aeval fun j => lin fun i => (A j i : ℝ) : MvPolynomial κ ℝ →ₐ[ℝ] MvPolynomial ι ℝ).toLinearMap)

def ArMetric : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (ι : Type) [Fintype ι] (M : HermLB p) (L : ι → HermLB p) (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ)
    (hu : ∀ σ y, CxPts.CInfAt (u σ) y) (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ')))
    (Φ Φ' : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ →
    IsArFun (fun o : Option ι => o.elim (M.raise u hu hc) L) D Φ' → ∀ n : ι → ℤ,
      (∀ σ, ((comb L n).φ σ).ChernIntegrableOn D Set.univ (u σ)) ∧
      Φ' (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) + 1 / 2 * chInt (comb L n) D u

def ArCalc : Prop := ArExists ∧ ArChange ∧ ArShift ∧ ArMix ∧ ArProj ∧ ArIso ∧ ArMetric

theorem ArCalc.arExists (h : ArCalc) : ArExists := h.1

theorem ArCalc.arChange (h : ArCalc) : ArChange := h.2.1

theorem ArCalc.arShift (h : ArCalc) : ArShift := h.2.2.1

theorem ArCalc.arMix (h : ArCalc) : ArMix := h.2.2.2.1

theorem ArCalc.arProj (h : ArCalc) : ArProj := h.2.2.2.2.1

theorem ArCalc.arIso (h : ArCalc) : ArIso := h.2.2.2.2.2.1

section Consequences

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} {ι : Type} [Fintype ι]

theorem ArMix.fnB (H : ArMix) (HE : ArExists) (hX : IsArithVar p D) {L : ι → HermLB p}
    {u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ} {hu : ∀ σ y, CInfAt (u σ) y}
    {hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))} {Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ}
    (hΦ : IsArFun (fun o : Option ι => o.elim (fnB u hu hc) L) D Φ) (n : ι → ℤ) :
    (∀ σ, ((comb L n).φ σ).ChernIntegrableOn D Set.univ (u σ)) ∧
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) = 1 / 2 * chInt (comb L n) D u := by
  haveI : IsLocallyNoetherian X := hX.isLocallyNoetherian
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  obtain ⟨h, hh⟩ := (HE k X p D hX).1 (comb L n)
  have hr1 : IsRatSec (LB.triv X) (fun _ => 1) := by
    intro i j hij
    change (1 : X.functionField) = fnOf _ hij ((1 : Γ(X, ⊤ ⊓ ⊤)ˣ) : Γ(X, ⊤ ⊓ ⊤)) * 1
    simp
  obtain ⟨hI, he⟩ := H k X p D hX ι (ArInt.fnB u hu hc) L Φ hΦ n h hh _ hr1
  have hE : ∀ x, ((ArInt.fnB u hu hc).div hr1).IsEqn x 1 := fun x =>
    (presents_divOfRatSec (LB.isLB_triv X) hr1).isEqn PUnit.unit x trivial
  have hmult : ∀ z, ((ArInt.fnB u hu hc).div hr1).mult z = 0 := fun z => by
    rw [(hE z).mult_eq]
    first
      | exact UnitAt.ord_eq_zero (unitAt_one z)
      | simpa using UnitAt.ord_eq_zero (unitAt_one z)
  have hoff : ∀ σ, offSupp p σ ((ArInt.fnB u hu hc).div hr1) = Set.univ := fun σ =>
    Set.eq_univ_of_forall fun y => mem_offSupp.2 fun hy => hy (hE _)
  have hlog : ∀ σ, logNorm ((ArInt.fnB u hu hc).φ σ) (fun _ : (LB.triv X).ι => 1) =
      fun y => (-1 / 2 : ℝ) * u σ y := by
    intro σ
    funext y
    have hv : ratVal (1 : X.functionField) y = 1 := by
      have e := ratVal_fnOf (mem_ptsIn_top : y ∈ ptsIn p σ ⊤) trivial (1 : Γ(X, ⊤))
      rwa [map_one, ev_one (mem_ptsIn_top : y ∈ ptsIn p σ ⊤)] at e
    simp only [logNorm, Units.val_one, hv, norm_one, Real.log_one, zero_sub]
    change -(u σ y / 2) = (-1 / 2 : ℝ) * u σ y
    ring
  refine ⟨fun σ => ?_, ?_⟩
  · have hi := hI σ
    rw [hoff σ, hlog σ] at hi
    exact ⟨(MeasureTheory.Integrable.const_mul hi.1 (-2)).congr
        (Filter.Eventually.of_forall fun y => by dsimp only; ring),
      (MeasureTheory.Integrable.const_mul hi.2 (-2)).congr
        (Filter.Eventually.of_forall fun y => by dsimp only; ring)⟩
  · rw [he]
    simp only [hmult, Int.cast_zero, zero_mul, finsum_zero, zero_sub]
    unfold HermLB.archInt chInt
    simp only [hoff, hlog, Weight.chernInt_const_mul]
    rw [← mul_finsum]
    ring

end Consequences

theorem arChange_of_arMix (HE : ArExists) (H : ArMix) : ArChange := by
  intro k _ X _ p D hX ι _ L u hu hc Φ hΦ n
  exact (ArMix.fnB H HE hX hΦ n).2

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt

namespace GlobalTheory.Published

def VolGe : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L : HermLB p) (a : ℝ), NefFib L → L.SemiPos D → L.IsSelfInter a → (a : EReal) ≤ arVol L D

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolHomog
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt

namespace GlobalTheory.Published

def VolNef : Prop := ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
  ∀ (L : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a → arVol L D = (a : EReal)

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsCMTypeEmbedding
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.Published.HeckeFEModel

section
variable {E : Type} [Field E] [NumberField E]

theorem exists_exponents (χ : HChar E) : ∃ a : HeightOneSpectrum (𝓞 E) →₀ ℕ, ∀ v, ExpAt χ v (a v) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ
  have hE : ∀ v, ExpAt χ v (Nat.find (h2 v)) := fun v m => by
    refine ⟨fun h => Nat.find_min' _ h, fun h x hx hx' => Nat.find_spec (h2 v) x hx (hx'.trans ?_)⟩
    rw [WithZero.exp_le_exp]
    omega
  refine ⟨Finsupp.ofSupportFinite (fun v => Nat.find (h2 v)) (h1.subset fun v hv hu => hv ?_), fun v => hE v⟩
  exact (hE v).unique ((expAt_zero_iff χ v).2 hu)

theorem hasInf_inv {I : Type} [Fintype I] {φ : I → E →+* ℂ} {χ : HChar E} {n : I → ℤ}
    (h : Formalism.L2.Host.HChar.HasInf χ φ n) : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -n i) := fun k => by
  rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp only [zpow_neg]

theorem isUnitary_inv {χ : HChar E} (h : IsUnitary χ) : IsUnitary χ⁻¹ := fun x => by
  show ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]

theorem zero_iff (h : HeckeFunctionalEquationAbs) [_root_.NumberField.IsTotallyComplex E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} {Λ Λ' : ℂ → ℂ} (hu : IsUnitary χ)
    (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0) (h1 : IsCompletedL χ n Λ)
    (h2 : IsCompletedL χ⁻¹ (fun i => -n i) Λ') (s : ℂ) : Λ s = 0 ↔ Λ' (1 - s) = 0 := by
  obtain ⟨a, ha⟩ := exists_exponents χ
  obtain ⟨ε, hε, hs⟩ := h E I φ hφ χ n a Λ Λ' hu hi hn ha h1 h2
  have h0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hA : ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ)) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    refine mul_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero E)) ?_
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  rw [hs s, mul_eq_zero, mul_eq_zero, Complex.cpow_eq_zero_iff]
  tauto

end

section
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.DefU.NonTriv

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

end

end GlobalTheory.Published.HeckeFEModel

end
end
