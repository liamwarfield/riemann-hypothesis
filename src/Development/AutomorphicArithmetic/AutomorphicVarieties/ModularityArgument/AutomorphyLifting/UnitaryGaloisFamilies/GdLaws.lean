module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.SpehSingleFactorEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PstExact

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.GdLaws
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu UpperTheory.Zero.LLC

open scoped commutatorElement

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem pow_iff (x : WD h) (σ : Weil h) :
    x.charPol σ = (X - 1) ^ x.lpDim ↔ ∀ α ∈ x.eig σ, α = 1 := by
  constructor
  · intro hx α hα
    rw [WD.eig, hx, ← C_1, roots_pow, roots_X_sub_C] at hα
    simpa using Multiset.mem_of_mem_nsmul hα
  · intro hx
    rw [WD.charPol_eq_prod, Multiset.eq_replicate_of_mem hx, Multiset.map_replicate,
      Multiset.prod_replicate, WD.card_eig, C_1]

private theorem eig_sum (x y : WD h) (σ : Weil h) : (x.lpSum y).eig σ = x.eig σ + y.eig σ := by
  rw [WD.eig, WD.eig, WD.eig, WD.charPol_lpSum, roots_mul]
  exact mul_ne_zero (WD.charPol_monic x σ).ne_zero (WD.charPol_monic y σ).ne_zero

private theorem tor_iff (x : WD h) :
    UpperTheory.GalStar.Tor x ↔ ∀ s t : ↥(Weil h), ∀ α ∈ x.eig ⁅s, t⁆, α = 1 :=
  forall_congr' fun s => forall_congr' fun t => pow_iff x ⁅s, t⁆

private theorem gd_sum (x y : WD h) : Gd (x.lpSum y) ↔ Gd x ∧ Gd y := by
  have ht : UpperTheory.GalStar.Tor (x.lpSum y) ↔ UpperTheory.GalStar.Tor x ∧ UpperTheory.GalStar.Tor y := by
    simp only [tor_iff, eig_sum, Multiset.mem_add]
    exact ⟨fun H => ⟨fun s t α hα => H s t α (Or.inl hα), fun s t α hα => H s t α (Or.inr hα)⟩,
      fun H s t α hα => hα.elim (H.1 s t α) (H.2 s t α)⟩
  unfold Gd
  rw [ht, WD.monomial_sum_iff]
  tauto

private theorem gd_tw (x : WD h) (t : ℝ) : Gd (x.lpTw t) ↔ Gd x := by
  have ht : UpperTheory.GalStar.Tor (x.lpTw t) ↔ UpperTheory.GalStar.Tor x := by
    simp only [tor_iff]
    refine forall_congr' fun s => forall_congr' fun u => ?_
    have hc : (unrChar h (qPow w t)) ⁅s, u⁆ = 1 := by
      rw [map_commutatorElement]
      exact (Commute.all _ _).commutator_eq
    have he : (x.lpTw t).charPol ⁅s, u⁆ = x.charPol ⁅s, u⁆ := by
      rw [GlobalTheory.GalCut.AwayMono.charPol_lpTw, hc]
      simp
    rw [WD.eig, WD.eig, he]
  unfold Gd
  rw [ht, WD.monomial_twist_iff]

private theorem gd_zero : Gd (WD.lpZero (h := h)) := by
  refine ⟨(tor_iff _).2 fun s t α hα => ?_, ?_⟩
  · rw [WD.eig, GlobalTheory.LocLanglands.CuspExt.charPol_lpZero] at hα
    simp at hα
  · rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    rfl

private theorem gd_list (L : List (WD h)) : Gd (sumList L) ↔ ∀ x ∈ L, Gd x := by
  induction L with
  | nil => exact ⟨fun _ x hx => absurd hx (by simp), fun _ => gd_zero⟩
  | cons b L ih =>
    show Gd (WD.lpSum b (sumList L)) ↔ _
    rw [gd_sum, ih, List.forall_mem_cons]

private theorem deg_comm (s t : ↥(Weil h)) : deg ⁅s, t⁆ = 0 := by
  rw [commutatorElement_def]
  simp only [deg_mul, deg_inv]
  ring

private theorem gd_unr {x : WD h} (hx : x.unr) : Gd x := by
  refine ⟨fun s t => ?_, WD.unr_mono0 _ hx⟩
  have hi : ((⁅s, t⁆ : ↥(Weil h)) : G E Ω) ∈ Ine (F := E) A :=
    actsAs_zero_iff.mp (actsAs_of_deg (a := 0) (b := 0) (by simpa using deg_comm s t))
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  have h1 : a.ρ ⁅s, t⁆ = 1 := ((WD.unr_mk a).mp hx).2 ⟨_, hi⟩
  show WD.charPol _ _ = _
  rw [WD.charPol_mk, h1, LinearMap.charpoly_one, WD.lpDim_mk]

end UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist

open UpperTheory.V.Z.Win.Gu.ClosureUnderSumAndTwist in
theorem UpperTheory.V.Z.Win.Gu.gdLaws :
    GdLaws := by
  intro E Ω _ _ _ _ _ A w h
  exact ⟨gd_sum, gd_tw, gd_list, fun _ => gd_unr⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseTAlt
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Imports
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open UpperTheory.V.Af.Gu

open UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.RecTotT
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tw_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (s : ℝ) (L : List (WD h)) :
    (sumList L).lpTw s = sumList (L.map fun x => x.lpTw s) := by
  induction L with
  | nil =>
    change (WD.lpZero (h := h)).lpTw s = WD.lpZero (h := h)
    rw [WD.lpZero, WD.lpTw_mk]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | cons x L ih =>
    change (x.lpSum (sumList L)).lpTw s = (x.lpTw s).lpSum (sumList (L.map fun x => x.lpTw s))
    rw [WD.lpTw_sum, ih]

theorem UpperTheory.V.Z.Win.Gu.recTotT :
    ProdT → SpehT → RecTotT := by
  intro hProd hSpeh E Ω _ _ _ _ _ _ n c a d hn P w ρ σ hpos hP hS τ e A h rc hrc
  have h1 := hProd E Ω n c (fun i => d i * a i) hn w σ (fun i => (hS i).2.1) τ e A h rc hrc
  have h2 : ∀ i, rc (cl (σ i)) = sumList ((List.range (d i)).map fun k : ℕ =>
      (rc (cl (ρ i))).lpTw (((d i : ℝ) - 1) / 2 - k)) := fun i =>
    hSpeh E Ω (a i) (d i) (P i) w (ρ i) (σ i) (hpos i).1 (hpos i).2 (hP i) (hS i).1 (hS i).2.2 A h rc hrc
  have h3 : rc (algNorm τ) = (rc (cl τ)).lpTw ((1 - (n : ℝ)) / 2) := by
    obtain ⟨_, _, L⟩ := hrc
    exact L.nu _ _
  rw [h3, h1, tw_sumList, List.map_ofFn]
  refine congrArg sumList (congrArg List.ofFn (funext fun i => ?_))
  rw [Function.comp_apply, h2, tw_sumList, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  refine congrArg sumList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, WD.lpTw_add]
  refine congrArg₂ WD.lpTw rfl ?_
  simp only [ex]
  push_cast
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.LocProdSum
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.RecSpehQuotT
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.DefiniteBC UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.HalfG
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Win.Gu.halfG :
    TwistLoc → PolG → HalfG := by
  intro hTw hC E Ω _ _ _ _ _ _ l _ ι a ha P hP ρ hρ m hm e he
  set s : ℝ := ((e + a - 1 : ℤ) : ℝ) / 2 with hs
  have hsC : (s : ℂ) = (e : ℂ) / 2 + ((a : ℂ) - 1) / 2 := by
    rw [hs]; push_cast; ring
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s
  have hinf : ∀ τ, (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).infChar τ = (m τ).map (· + (s : ℂ)) := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.HeckeGal.Model.absPow E s)
    rw [(InfType.expo_of_infType E _).2.1 s hν τ] at h1
    exact CG.HasInfChar.infChar_eq (π := CG.mk _) h1
  have hreg : (CG.mk (P.twist (GlobalTheory.HeckeGal.Model.absPow E s))).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    rw [hinf]
    refine ⟨(he τ).1.map (add_left_injective _), fun z hz => ?_⟩
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨j, hj⟩ := (he τ).2 y hy
    exact ⟨j, by rw [hsC, ← hj]; ring⟩
  choose σ hσ hcl using fun w => hTw E a P s w (ρ w) (hρ w)
  obtain ⟨r, HT, hr, hHT⟩ := hC E Ω l ι a ha _ _ hreg (GlobalTheory.HeightCounting.Blocks.isPolarized_twist_absPow hP s) σ hσ
  have key : ∀ w (A : ValuationSubring Ω) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRecT h rc →
      rc (algNorm (σ w)) = (rc (cl (ρ w))).lpTw ((e : ℝ) / 2) := by
    intro w A h rc hrc
    obtain ⟨_, _, L⟩ := hrc
    rw [← L.nu]
    refine congrArg rc ?_
    change (cl (σ w)).nu _ = _
    rw [hcl, IrrGL.nu_nu]
    congr 1
    rw [hsC]; push_cast; ring
  refine ⟨r, HT, ⟨hr.cont, hr.ss, fun w hg => hr.ht w fun A h rc hrc => ?_,
    fun w A h rc hrc => key w A h rc hrc ▸ hr.par w A h rc hrc⟩, fun τ => ?_⟩
  · have := hg A h rc hrc
    simp only [key w A h rc hrc]
    exact this
  · rw [hHT, hinf, Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply, hsC]; ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumFamG
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Win.Gu.sumFamG :
    SumTwoG → SumRed → SumFamG := by
  intro h2 hred E Ω _ _ _ _ _ l _ ι c hc
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  clear hc
  induction c with
  | zero =>
    intro N hN n hn r p HT H
    have hn' : N 0 = n := by simpa using hn
    subst hn'
    have e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) = p 0 w A h rc := by
      intro w A h rc
      simp [sumList, WD.lpSum_zero]
    have e' : (fun τ => ∑ i, HT i τ) = HT 0 := by
      funext τ
      simp
    refine ⟨r 0, ⟨(H 0).cont, (H 0).ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ⟨rfl, fun i => ?_⟩⟩
    · rw [e']
      exact (H 0).ht w fun A h rc hrc => by
        have := hg A h rc hrc
        rwa [e] at this
    · rw [e]
      exact (H 0).par w A h rc hrc
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hi
  | succ c ih =>
    intro N hN n hn r p HT H
    rw [Fin.sum_univ_succ] at hn
    subst hn
    obtain ⟨R, hR, -⟩ := ih (fun i => N i.succ) (fun i => hN i.succ) _ rfl (fun i => r i.succ) (fun i => p i.succ)
      (fun i => HT i.succ) (fun i => H i.succ)
    have hS := h2 E Ω l ι _ _ (r 0) R _ _ _ _ (H 0) hR
    have e : ∀ w A h rc, sumList (List.ofFn fun i => p i w A h rc) =
        (p 0 w A h rc).lpSum (sumList (List.ofFn fun i : Fin (c + 1) => p i.succ w A h rc)) := by
      intro w A h rc
      rw [List.ofFn_succ (f := fun i => p i w A h rc)]
      rfl
    have e' : (fun τ => ∑ i, HT i τ) = fun τ => HT 0 τ + ∑ i : Fin (c + 1), HT i.succ τ := by
      funext τ
      rw [Fin.sum_univ_succ]
    refine ⟨Formalism.MainNotions.SumRepresentations.At.sumRep (r 0) R, ⟨hS.cont, hS.ss, fun w hg => ?_, fun w A h rc hrc => ?_⟩, fun hi => ?_⟩
    · rw [e']
      exact hS.ht w fun A h rc hrc => by
        have := hg A h rc hrc
        rwa [e] at this
    · rw [e]
      exact hS.par w A h rc hrc
    · refine absurd hi (hred _ _ _ _ _ _ (hN 0) ?_)
      exact le_trans (hN (Fin.succ 0)) (Finset.single_le_sum (f := fun i : Fin (c + 1) => N i.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumHTAt
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.Pst

private theorem map_sum' {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k'] {a b : ℕ}
    (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) = Formalism.MainNotions.SumRepresentations.At.sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {r' : ↥Gw →* GL (Fin b) (Om l)}

private theorem model_sum {L : FinExt l} {r₁ : ↥Gw →* GL (Fin a) ↥L.1} {r₂ : ↥Gw →* GL (Fin b) ↥L.1}
    (h₁ : IsModel Bw r L r₁) (h₂ : IsModel Bw r' L r₂) :
    IsModel Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') L (Formalism.MainNotions.SumRepresentations.At.sumRep r₁ r₂) :=
  ⟨h₁.1, by rw [map_sum', h₁.2, h₂.2]⟩

private theorem dR_sum (h : IsdRAt (UpperTheory.V.Loc.PP l) Bw r) (h' : IsdRAt (UpperTheory.V.Loc.PP l) Bw r') :
    IsdRAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
  obtain ⟨L₁, r₁, m₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  exact ⟨_, _, model_sum n₁ n₂, (GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b _ _).1.2
    ⟨(n₁.isdRAt_iff _).1 h, (n₂.isdRAt_iff _).1 h'⟩⟩

private theorem jumps_sum {τ : E →+* Om l} {J J' : Multiset ℤ}
    (h : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r τ J) (h' : IsJumpsAt (UpperTheory.V.Loc.PP l) Bw r' τ J') :
    IsJumpsAt (UpperTheory.V.Loc.PP l) Bw (Formalism.MainNotions.SumRepresentations.At.sumRep r r') τ (J + J') := by
  obtain ⟨L₁, r₁, m₁, d₁, τ₁, t₁, -⟩ := id h
  obtain ⟨L₂, r₂, m₂, d₂, -⟩ := id h'
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have n₁ := m₁.enlarge l₁
  have n₂ := m₂.enlarge l₂
  have t : IsInduced Bw τ (LL' := supExt L₁ L₂) ((IntermediateField.inclusion l₁).comp τ₁) := t₁
  have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l _ _ (UpperTheory.V.Loc.tiedP l) E Ω Gw O Bw _ a b
    (mapRep (IntermediateField.inclusion l₁).toRingHom r₁) (mapRep (IntermediateField.inclusion l₂).toRingHom r₂)
  refine ⟨_, _, model_sum n₁ n₂, S.1.2 ⟨(n₁.isdRAt_iff _).1 ⟨_, _, m₁, d₁⟩, (n₂.isdRAt_iff _).1 ⟨_, _, m₂, d₂⟩⟩,
    _, t, fun c => ?_⟩
  rw [S.2, ← h.count_eq _ n₁ t, ← h'.count_eq _ n₂ t, Multiset.count_add, Nat.cast_add]

end

theorem UpperTheory.V.Z.Win.Gu.sumHTAt :
    SumHTAt := by
  intro E Ω _ _ _ _ _ l _ a b r r' _ _ HT HT' w H H' A hA O _ _ _ Bw hj
  obtain ⟨d, J⟩ := H A hA O Bw hj
  obtain ⟨d', J'⟩ := H' A hA O Bw hj
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) (r'.comp (ReciprocityTheory.Gal.Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e]
  exact ⟨dR_sum d d', fun τ L τ' t => jumps_sum (J τ L τ' t) (J' τ L τ' t)⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.SumTwoG
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open Module TensorProduct GlobalTheory.Pst.DpstMap

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Split

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K LL : FinExt l}
  {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module ↥LL.1 V₀] [Module ℚ_[l] V₀] [IsScalarTower ℚ_[l] ↥LL.1 V₀]
  [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁]
  [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂]
  {ρ₀ : Representation ↥LL.1 ↥(GK K) V₀} {ρ₁ : Representation ↥LL.1 ↥(GK K) V₁}
  {ρ₂ : Representation ↥LL.1 ↥(GK K) V₂}

variable [FiniteDimensional ↥LL.1 V₀] [FiniteDimensional ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₂]

end Split

section Sum

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) {a b : ℕ}

end Sum
end
