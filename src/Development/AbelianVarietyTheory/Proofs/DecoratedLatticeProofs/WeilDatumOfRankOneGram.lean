module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualStabilizerWithPrescribedSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotients
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeRationalCosetSameOrbitIffLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.WeilTup

variable {D : D7}

theorem hecke_mul {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') : IsHeckeChar D (χ * χ') :=
  ⟨by show Continuous (fun x => χ x * χ' x); exact h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem hecke_inv {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨by rw [show ⇑χ⁻¹ = fun x => (χ x)⁻¹ from funext fun x => MonoidHom.inv_apply χ x]; exact h.1.inv,
    fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem resEta_of_diff {μ χ : (AE D)ˣ →* Circle} {n : ℕ} (hA : ResEta D μ (n + 1)) (hB : ResEta D (μ * χ⁻¹) n) :
    ResEta D χ 1 := by
  refine ⟨hA.1, fun e he a => ?_⟩
  have h1 := hA.2 e he a
  have h2 := hB.2 e he a
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, pow_succ] at h2
  rw [pow_one]
  exact (mul_left_cancel (mul_inv_eq_iff_eq_mul.1 h2)).symm

end GlobalTheory.Fam.WeilTup

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHomCompletionStableSplitIdempoten
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHomCompletionStableSplitIdempoten
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.AdForm

def intVecSub (D : D7) (n : ℕ) : Submodule (NumberField.RingOfIntegers D.host.E) (Fin n → D.host.E) where
  carrier := intVec D n
  add_mem' := fun {x y} hx hy k => (hx k).add (hy k)
  zero_mem' := fun _ => isIntegral_zero
  smul_mem' := fun c {x} hx k => by
    show IsIntegral ℤ ((c : D.host.E) * x k)
    exact c.2.mul (hx k)

theorem coe_intVecSub (D : D7) (n : ℕ) : ((intVecSub D n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := rfl

theorem stdHom_map_splitIdem : ∀ (D : D7) (S T : HSp D) (a : AE D), IsSplitIdem D a → ∀ u ∈ stdHom S T, u.map (fun x => a * x) ∈ stdHom S T := by
  intro D S T a ha u hu
  have h := Formalism.IndefR.Fin.latO_map_splitIdem S T (intVecSub D S.rank) (intVecSub D T.rank) ha
    (u := u) (by rw [coe_intVecSub, coe_intVecSub]; exact hu)
  rw [coe_intVecSub, coe_intVecSub] at h
  exact h

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHomCompletionStableSplitIdempotenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardLatticeHomCompletion_stable_splitIdempotent : ∀ (D : D7) (S T : HSp D) (a : AE D), IsSplitIdem D a → ∀ u ∈ stdHom S T, u.map (fun x => a * x) ∈ stdHom S T := by
  first | exact @GlobalTheory.AdForm.stdHom_map_splitIdem | exact GlobalTheory.AdForm.stdHom_map_splitIdem | (intros; apply GlobalTheory.AdForm.stdHom_map_splitIdem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.Fam.OffLevel

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem mem_latV_at_iff_all (S : HSp D) (L : Lat S) (p : Pl D) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· = p)) : z ∈ latV S L (· = p) ↔ z ∈ latV S L (fun _ => True) := by
  constructor
  · exact fun h => latV_mono S L (fun _ _ => trivial) h
  · intro h
    have h1 := ((mem_latV_iff_parts S L (fun _ => True) {p}
      (fun i => idAt_mono (fun _ _ => trivial) (hz i))).1 h).1
    have e : eQ {p} • z = z := funext fun i =>
      eQ_mul_of_in (P := fun _ => True) {p}
        (idAt_mono (fun w hw => ⟨trivial, Finset.mem_singleton.2 hw⟩) (hz i))
    rw [e] at h1
    exact latV_mono S L (fun w hw => Finset.mem_singleton.1 hw.2) h1

theorem latV_eq_of_moves (S : HSp D) (g : GA D S) (Λ N M : Lat S) (p : Pl D)
    (hN : Moves S g Λ N (· = p)) (hM : Moves S g Λ M (fun _ => True)) :
    latV S N (· = p) = latV S M (· = p) := by
  have key : ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = p)) →
      (z ∈ latV S N (· = p) ↔ z ∈ latV S M (· = p)) := by
    intro z hz
    set y := mt S g⁻¹ *ᵥ z with hy
    have hys : ∀ i, y i ∈ idAt D (· = p) := mulVec_mem S _ hz
    have hgy : mt S g *ᵥ y = z := by
      rw [hy, Matrix.mulVec_mulVec, ← KSplit.mt_mul, mul_inv_cancel]
      exact Matrix.one_mulVec z
    rw [← hgy, ← hN y hys, mem_latV_at_iff_all S M p (by rw [hgy]; exact hz),
      ← hM y (fun i => idAt_mono (fun _ _ => trivial) (hys i)), mem_latV_at_iff_all S Λ p hys]
  ext z
  constructor
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).1 h
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).2 h

end GlobalTheory.Fam.OffLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LatIndSB

theorem indicator_latO_mem_SB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M'), Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} (fun _ => (1 : ℂ)) ∈ SB (Matrix P.Y P.Y' P.k) := by
  intro D ψ S T M M' hM hM' P
  classical
  have hset : {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} =
      (((latO S T (M : Set _) (M' : Set _) fun _ => True).comap (GlobalTheory.LocMod.Witness.upH (ofSplit P.q) P.FS P.FT) : AddSubgroup _) : Set (Matrix P.Y P.Y' P.k)) := by
    obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem P.q
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε P.q.split.1 heε h).1
    have hh : (ofSplit P.q).up P.FS P.FT x ∈ GlobalTheory.PlaceModel.half S T P.q.e :=
      (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.LocMod.Witness.up_half (ofSplit P.q) P.FS P.FT x)
    have h3 : P.q.e • (ofSplit P.q).up P.FS P.FT x = (ofSplit P.q).up P.FS P.FT x := (GlobalTheory.PlaceModel.mem_half S T).1 hh
    change P.q.e • (ofSplit P.q).up P.FS P.FT x ∈ (latO S T (M : Set _) (M' : Set _) fun w => w = P.q.v) at h2
    rw [h3] at h2
    exact h2
  rw [hset]
  have ho := GlobalTheory.LocMod.Witness.lat_open (ofSplit P.q) P.FS P.FT hM hM'
  have hc := GlobalTheory.LocMod.Witness.lat_compact (ofSplit P.q) P.FS P.FT hM hM'
  have hcl := AddSubgroup.isClosed_of_isOpen _ ho
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ (((latO S T (M : Set _) (M' : Set _) fun _ => True).comap
        (GlobalTheory.LocMod.Witness.upH (ofSplit P.q) P.FS P.FT) : AddSubgroup _) : Set (Matrix P.Y P.Y' P.k))
    · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.LatIndSB

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IndicatorLocalHomLatticeMemSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indicator_localHomLattice_mem_schwartzBruhat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M'), Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} (fun _ => (1 : ℂ)) ∈ SB (Matrix P.Y P.Y' P.k) := by
  first | exact @GlobalTheory.LatIndSB.indicator_latO_mem_SB | exact GlobalTheory.LatIndSB.indicator_latO_mem_SB | (intros; apply GlobalTheory.LatIndSB.indicator_latO_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIffUpMemStdHom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdHomAt
open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latO_mono (S T : HSp D) (LS LT) {P Q : Pl D → Prop} (h : ∀ v, P v → Q v) :
    latO S T LS LT P ≤ latO S T LS LT Q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

theorem mem_latO_at (q : SplitPt D k) {S T : HSp D} {LS LT} {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True)
    (hh : IsHalf q.e u) : u ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, ⟨β, rfl, h1, h0⟩, hsum⟩ := q.above
  have hβ : β ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have main : (latO S T LS LT fun _ => True) ≤ (latO S T LS LT (· = q.v)).comap
      (DistribSMul.toAddMonoidHom (WO S T) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, h0 v hv, zero_mul]
    · ext i j
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Matrix.of_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  have h := main hu
  rw [AddSubgroup.mem_comap] at h
  convert h using 1
  ext i j
  change _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * u i j
  rw [← hsum, ← hh i j, ← mul_assoc, add_mul, q.split.1, mul_comm (cA D q.e), q.split.2.1, add_zero]

theorem int_iff_up_mem_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) → (∀ z, z ∈ LT ↔ z ∈ intVec D T.rank) → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) ↔ (GlobalTheory.LocMod.ofSplit q).up FS FT x ∈ stdHom S T := by
  intro D k _ _ _ _ q hq Y Y' _ _ _ _ S T FS FT LS LT hS hT eS eT hFS hFT x
  have eS' : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank := Set.ext eS
  have eT' : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank := Set.ext eT
  rw [stdHom, ← eS', ← eT']
  refine ⟨fun hx => latO_mono S T _ _ (fun _ _ => trivial)
    (GlobalTheory.UpMem.up_mem_latO D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT x hx), fun hx => ?_⟩
  have hh := Witness.up_half (ofSplit q) FS FT x
  obtain ⟨x', hx', e⟩ := GlobalTheory.HalfIntUp.exists_int_up D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT _ (mem_latO_at q hx hh) hh
  have := congrArg ((ofSplit q).down FS FT) e
  rw [Witness.down_up, Witness.down_up] at this
  rwa [this]

end GlobalTheory.StdHomAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.TwDat

theorem int_eq_sub_half (R : Ranks) (j : ℕ) (s z : ℤ) (h : (s : ℚ) = z - (R.N j : ℚ) / 2) : s = z - (R.N j : ℤ) / 2 := by
  obtain ⟨b, hb⟩ := N_even R j
  have e : (s : ℚ) = ((z - b : ℤ) : ℚ) := by rw [h, hb]; push_cast; ring
  have e' : s = z - b := by exact_mod_cast e
  rw [e', hb]
  omega


set_option maxHeartbeats 800000 in
theorem chr_exp_shifts : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ e : (I.rec7 l Z).what₂.Tau → ℤ, (∀ τ, HasInfExp (I.rec7 l Z) (A.chr (i + 1)) τ (e τ)) ∧ ∀ τ, (I.chain l u a).sSharp i τ = -e τ - ((I.rec7 l Z).sp.X (i + 1)).rank / 2 ∧ -(I.chain l u a).sDiv i τ = e τ + ((I.rec7 l Z).sp.X i).rank / 2 ∧ 0 ≤ shiftOf (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i) τ + (I.chain l u a).sSharp i τ := by
  intro B X I hI _ l Z u a Ch A hA i hi
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  obtain ⟨n, hn, hord⟩ := htw.1
  choose e he using fun τ => (B.hc τ).e_int ⟨i, hi⟩
  have hinf := Formalism.L2.Host.HChar.HasInfQ.mul_triv (I.C.isMu0 ⟨i, hi⟩).inf
    (Formalism.L2.Host.HChar.inf_eq_one_of_order hn hord)
  have hexp := (GlobalTheory.HeckeInfExp.hasInfExp_iff_hasInfQ (I.rec7 l Z) _ _ _ (hA.chr ⟨i, hi⟩)).2 hinf
  refine ⟨fun τ => -e τ, fun τ => ?_, fun τ => ?_⟩
  · have e1 : ((-e τ : ℤ) : ℚ) = -(B.hc τ).e ⟨i, hi⟩ := by rw [Int.cast_neg, ← he τ]
    exact e1 ▸ hexp τ
  · have hw : (B.hcW u τ).e ⟨i, hi⟩ = e τ := by
      have h : (B.hcW u τ).e = (B.hc τ).e := (I.rec7 l Z).hcW_e u τ
      rw [h, he τ]
    have h1 : (I.chain l u a).sSharp i τ = e τ - (B.R.N (i + 1) : ℤ) / 2 := by
      apply int_eq_sub_half
      rw [(I.chain l u a).sSharp_eq i hi τ, ← hw]
      rfl
    have h2 : (I.chain l u a).sDiv i τ = e τ - (B.R.N i : ℤ) / 2 := by
      apply int_eq_sub_half
      rw [(I.chain l u a).sDiv_eq i hi τ, ← hw]
      rfl
    have r1 : ((I.rec7 l Z).sp.X (i + 1)).rank = B.R.N (i + 1) := rankN (I.rec7 l Z) (i + 1) hi
    have r0 : ((I.rec7 l Z).sp.X i).rank = B.R.N i := rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)
    refine ⟨?_, ?_, ?_⟩
    · rw [r1, h1, neg_neg]
    · rw [r0, h2]; ring
    · obtain ⟨k, -, hk, -⟩ := GlobalTheory.KerWtStep.trueWt_step (I.rec7 l Z) u _ _ _ (I.fm l u a) i hi
      exact (Int.natCast_nonneg (k τ)).trans_eq (hk τ).symm

end GlobalTheory.AdForm.TwDat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charExponent_infinity_kernel_shift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ e : (I.rec7 l Z).what₂.Tau → ℤ, (∀ τ, HasInfExp (I.rec7 l Z) (A.chr (i + 1)) τ (e τ)) ∧ ∀ τ, (I.chain l u a).sSharp i τ = -e τ - ((I.rec7 l Z).sp.X (i + 1)).rank / 2 ∧ -(I.chain l u a).sDiv i τ = e τ + ((I.rec7 l Z).sp.X i).rank / 2 ∧ 0 ≤ shiftOf (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i) τ + (I.chain l u a).sSharp i τ := by
  first | exact @GlobalTheory.AdForm.TwDat.chr_exp_shifts | exact GlobalTheory.AdForm.TwDat.chr_exp_shifts | (intros; apply GlobalTheory.AdForm.TwDat.chr_exp_shifts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateStandardLatticeIsSelfDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateStandardLatticeIsSelfDual
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdMove
variable {D : D7}

theorem moves_exists (V : HSp D) (g : GA D V) : ∃ N, Moves V rfl g N := by
  obtain ⟨Λ, hΛ, -, -, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (GlobalTheory.SplitMove.intSub D V.rank)
    (finHom V g) (GlobalTheory.SplitMove.intSub_fg _) (GlobalTheory.SplitMove.intSub_span _)
  have inv : ∀ y, (finHom V g⁻¹).1 *ᵥ ((finHom V g).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]
  have inv' : ∀ y, (finHom V g).1 *ᵥ ((finHom V g⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec]
  have ent : ∀ (x : Fin V.rank → D.host.E) i,
      Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E
        (((finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x) i) =
      (finM V rfl g⁻¹ *ᵥ fun j => eToEAf D (x j)) i := by
    intro x i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.AdForm.finM, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.reindex_apply,
      finCongr_refl, Equiv.refl_symm, Equiv.coe_refl, Matrix.submatrix_id_id]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
  refine ⟨Λ, fun x => ?_⟩
  rw [← SetLike.mem_coe, hΛ, GlobalTheory.SplitMove.coe_intSub]
  change GlobalTheory.AdLat.fv D.host.F x ∈ (finHom V g).1.mulVec '' _ ↔ _
  constructor
  · rintro ⟨y, hy, hxy⟩ i
    rw [← ent, ← hxy, inv]
    exact (GlobalTheory.SplitMove.hat_intVec_iff D V.rank y).1 hy i
  · intro hx
    refine ⟨(finHom V g⁻¹).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x, (GlobalTheory.SplitMove.hat_intVec_iff D V.rank _).2 fun i => ?_, inv' _⟩
    rw [ent]; exact hx i

theorem isSdLat_of (V : HSp D) (hV : V.gram = 1) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : IsSelfDualC V N) : Formalism.L2.Col.IsSdLat N := by
  refine ⟨h.1, ?_⟩
  ext x
  rw [h.2 x]
  simp only [Formalism.HermitianLatticesTheory.IsUnimodular, Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  refine forall_congr' fun y => imp_congr_right fun _ => ?_
  have e : Formalism.L2.Col.hStd D.host.E V.rank y x = ∑ i, ∑ j, star (y i) * V.gram i j * x j := by
    rw [hV]
    simp [Formalism.L2.Col.hStd, Matrix.one_apply]
  rw [e]

theorem std_moved_lattice : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), V.gram = 1 → (∀ g : GA D V, ∃ N, Moves V hn g N) ∧ ∀ (g : GA D V) N, Moves V hn g N → Formalism.L2.Col.IsSdLat N ∧ ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N ∧ IsSelfDualC V Λ := by
  intro D V n hn hV
  subst hn
  refine ⟨fun g => moves_exists V g, fun g N hN => ?_⟩
  have hsd := GlobalTheory.SplitMove.selfDual_move V hV g N hN
  refine ⟨isSdLat_of V hV N hsd, N, ?_, hsd⟩
  ext x
  first | exact Iff.rfl | simp [GlobalTheory.AdForm.latFr]

end GlobalTheory.StdMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicTranslateStandardLatticeIsSelfDualStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicTranslate_standardLattice_isSelfDual : ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), V.gram = 1 → (∀ g : GA D V, ∃ N, Moves V hn g N) ∧ ∀ (g : GA D V) N, Moves V hn g N → Formalism.L2.Col.IsSdLat N ∧ ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N ∧ IsSelfDualC V Λ := by
  first | exact @GlobalTheory.StdMove.std_moved_lattice | exact GlobalTheory.StdMove.std_moved_lattice | (intros; apply GlobalTheory.StdMove.std_moved_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm.RdLaw
variable {D : D7}

theorem PM_map {r : ℕ} {B : Type} [CommRing B] (f : AE D →+* B) (M : Matrix (Fin r) (Fin r) (AE D)) :
    (PM M).map f = f (eps D) • M.map f + f (1 - eps D) • (1 : Matrix (Fin r) (Fin r) B) := by
  ext i j
  simp only [PM, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul]
  split_ifs <;> simp

theorem cT_PM {r : ℕ} (M : Matrix (Fin r) (Fin r) (AE D)) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) =
      eps D • cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M + (1 - eps D) • (1 : Matrix (Fin r) (Fin r) (AE D)) := by
  unfold cT
  rw [PM_map, RingHom.map_sub, RingHom.map_one, sig_eps, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_one]

theorem PM_unit {r : ℕ} (J M : Matrix (Fin r) (Fin r) (AE D))
    (hM : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) M * J * M = J) :
    cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) (PM M) * J * PM M = J := by
  rw [cT_PM, PM]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one,
    eps_mul_self, one_sub_mul_self, eps_mul_one_sub, mul_comm (1 - eps D) (eps D), zero_smul, add_zero, zero_add, hM]
  rw [← add_smul, add_sub_cancel, one_smul]

def PGL (D : D7) (r : ℕ) : GL (Fin r) (AE D) →* GL (Fin r) (AE D) where
  toFun g := ⟨PM g.1, PM (g⁻¹).1, by rw [← PM_mul, Units.mul_inv, PM_one], by rw [← PM_mul, Units.inv_mul, PM_one]⟩
  map_one' := Units.ext PM_one
  map_mul' a b := Units.ext (PM_mul a.1 b.1)

theorem PGL_mem (V : HSp D) (g : GL (Fin V.rank) (AE D)) (hg : g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram) :
    PGL D V.rank g ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
  PM_unit _ g.1 hg

def pf (V : HSp D) (h : GA D V) : GA D V :=
  (⟨PGL D V.rank (matHom V h), PGL_mem V (matHom V h) (Subtype.property (h : ↥(HR (AF D.host.F) D.sp.cm.sig V.gram)))⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)

theorem mt_pf (V : HSp D) (h : GA D V) : Formalism.L2.Theta.mt V (pf V h) = PM (Formalism.L2.Theta.mt V h) := rfl

theorem pf_one (V : HSp D) : pf V 1 = 1 := by
  apply Subtype.ext
  show PGL D V.rank (matHom V 1) = 1
  rw [map_one, map_one]

theorem pf_fin (V : HSp D) (h : GA D V) : pf V h ∈ GfC V := by
  show infHom V (pf V h) = 1
  apply Units.ext
  show (Formalism.L2.Theta.mt V (pf V h)).map (infPart D) = 1
  rw [mt_pf, PM_map, infPart_eps, RingHom.map_sub, RingHom.map_one, infPart_eps, sub_zero, zero_smul, zero_add, one_smul]

theorem finM_pf (V : HSp D) (h : GA D V) : finM V rfl (pf V h) = finM V rfl h := by
  rw [finM_rfl, finM_rfl, mt_pf, PM_map, toEAf_eps, RingHom.map_sub, RingHom.map_one, toEAf_eps, sub_self, zero_smul, add_zero, one_smul]

theorem continuous_pf (V : HSp D) : Continuous (pf V) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hm : Continuous fun h : GA D V => Formalism.L2.Theta.mt V h :=
    Units.continuous_val.comp continuous_subtype_val
  have hP : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) (AE D) => PM M :=
    (continuous_const_smul _).add continuous_const
  refine Continuous.subtype_mk (f := fun h => PGL D V.rank (matHom V h)) (Units.continuous_iff.2 ⟨hP.comp hm, ?_⟩) _
  have e : (fun h : GA D V => ((PGL D V.rank (matHom V h))⁻¹ : GL (Fin V.rank) (AE D)).val) =
      fun h => PM (Formalism.L2.Theta.mt V h⁻¹) := by
    funext h
    rw [← map_inv, ← map_inv]; rfl
  rw [e]
  exact hP.comp (hm.comp continuous_inv)

end GlobalTheory.AdForm.RdLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeUnipotentHaarIntegralPointsEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeUnipotentHaarIntegralPointsEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarR.UnitVolN
open GlobalTheory.RootEx.VolN GlobalTheory.RootEx.Model

theorem mkNel_mem_KO_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (p : ℕ) (e : Ix n c p → k) :
    ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c) ↔ ∀ i, e i ∈ 𝒪[k] := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  constructor
  · rintro ⟨h1, -⟩ i
    have := congrFun (co_mkNel (k := k) p e) i
    rw [← this]
    exact h1 _ _
  · intro he
    have hent : ∀ r s, ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k).val r s ∈ 𝒪[k] := by
      intro r s
      change mkN p e r s ∈ 𝒪[k]
      simp only [mkN, Matrix.of_apply]
      split_ifs with h
      · exact he _
      · rw [Matrix.one_apply]; split_ifs
        · exact one_mem _
        · exact zero_mem _
    refine ⟨hent, fun i j => ?_⟩
    set g : GL (n ⊕ Fin c) k := ((mkNel p e : N k n c p) : GL (n ⊕ Fin c) k) with hg
    have hdet : g.val.det = 1 := det_mkN p e
    have hinv : (g⁻¹).val = g.val.adjugate := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, hdet]; simp
    let A : Matrix (n ⊕ Fin c) (n ⊕ Fin c) 𝒪[k] := fun r s => ⟨g.val r s, hent r s⟩
    have hA : (algebraMap 𝒪[k] k).mapMatrix A = g.val := rfl
    rw [hinv, ← hA, ← RingHom.map_adjugate]
    exact (A.adjugate i j).2

end GlobalTheory.HaarR.UnitVolN
end


open GlobalTheory.RootEx.VolN in
theorem GlobalTheory.HaarR.volN_KO_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), IsUnitVol ν → volN ν n c p {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = 1 := by
  intro k _ _ _ _ _ _ n _ _ c p h1 hp ν hν
  haveI : ν.IsAddHaarMeasure := hν.1
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [volN_eq, MeasurableEquiv.map_apply]
  have : (coEquiv (k := k) (n := n) (c := c) p) ⁻¹' {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} =
      Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext e
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_univ_pi]
    exact GlobalTheory.HaarR.UnitVolN.mkNel_mem_KO_iff p e
  rw [this, Measure.pi_pi]
  simp [hν.2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeUnipotentHaarIntegralPointsEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), IsUnitVol ν → volN ν n c p {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = 1 := by
  first | exact @GlobalTheory.HaarR.volN_KO_eq_one | exact GlobalTheory.HaarR.volN_KO_eq_one | (intros; apply GlobalTheory.HaarR.volN_KO_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelTensorWithHalfFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelTensorWithHalfFunction
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.TensorModel

variable {D : D7}

theorem cA_invol (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [show cA D (cA D (a ⊗ₜ[D.host.F] x)) = a ⊗ₜ[D.host.F] star (star x) from rfl, star_star]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem symplO_add_left' (S T : HSp D) (x x' y : WO S T) :
    symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem half_sum {m n : ℕ} {e e' : AE D} (he : e * e' = 0) {u : Mx D m n} (hu : IsHalf e' u) : IsHalf (e + e') u :=
  fun i j => by
    have h0 : e * u i j = 0 := by
      calc e * u i j = e * (e' * u i j) := by rw [hu i j]
        _ = 0 := by rw [← mul_assoc, he, zero_mul]
    rw [add_mul, h0, zero_add, hu i j]

theorem half_sum_cA {m n : ℕ} {e e' : AE D} (he : e * e' = 0) {u : Mx D m n} (hu : IsHalf (cA D e') u) :
    IsHalf (cA D (e + e')) u := by
  rw [map_add (f := _)]
  refine half_sum ?_ hu
  rw [← map_mul, he, map_zero]

theorem symplO_half_zero {S T : HSp D} {e e' : AE D} (he : e * e' = 0) {s y : WO S T} (hs : IsHalf e s)
    (hy : IsHalf (cA D e') y) : symplO S T s y = 0 := by
  have h0 : hO S T s y = 0 := by
    unfold hO
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
      Finset.sum_eq_zero fun d _ => ?_
    have h1 : cA D (y c b) = e' * cA D (y c b) := by
      conv_lhs => rw [← hy c b]
      rw [map_mul, cA_invol]
    have h2 : s d a = e * s d a := (hs d a).symm
    rw [h1, h2]
    linear_combination (incA D (S.gram⁻¹ a b) * cA D (y c b) * incA D (T.gram c d) * s d a) * he
  unfold symplO
  rw [h0, mul_zero, map_zero]

theorem isModel_tensor : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf e t) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ', IsSBHalf (e + p.e) (stdHom S T) Φ' → IsThetaFunO ψ S T (T' Φ')) → (∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ Ψ)) → p.IsModel ψ FS FT (T' ∘ₗ p.tensorL FS FT Φ) := by
  intro D k _ _ _ _ p ψ S T Y Y' _ _ _ _ FS FT e he Φ hΦ f₀ T' hP hθ hSB
  have hup : ∀ x, IsHalf (e + p.e) (p.up FS FT x) := fun x => half_sum he (Witness.up_half p FS FT x)
  refine ⟨fun Ψ => ?_, fun x Ψ Ψ' h => ?_, fun y hy Ψ Ψ' h => ?_⟩
  · exact hθ _ (hSB Ψ.1 Ψ.2)
  · have key : p.tensorAt FS FT Φ Ψ'.1 = fun t => p.tensorAt FS FT Φ Ψ.1 (t + p.up FS FT x) := by
      funext t
      simp only [Place.tensorAt]
      rw [Witness.down_add, Witness.down_up, Witness.up_add, h, add_sub_add_right_eq_sub]
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [key]
    exact hP.trans _ (hSB Ψ.1 Ψ.2) _ (hup x)
  · have key : p.tensorAt FS FT Φ Ψ'.1 = fun t => ψ (symplO S T t y) * p.tensorAt FS FT Φ Ψ.1 t := by
      funext t
      simp only [Place.tensorAt]
      rw [h]
      by_cases h0 : Φ (t - p.up FS FT (p.down FS FT t)) = 0
      · rw [h0]; ring
      · have e1 : symplO S T t y = symplO S T (t - p.up FS FT (p.down FS FT t)) y +
            symplO S T (p.up FS FT (p.down FS FT t)) y := by
          rw [← symplO_add_left', sub_add_cancel]
        rw [e1, symplO_half_zero he (hΦ _ h0) hy, zero_add]
        ring
    simp only [LinearMap.comp_apply, Place.tensorL_apply]
    rw [key]
    exact hP.modul _ (hSB Ψ.1 Ψ.2) _ (half_sum_cA he hy)

end GlobalTheory.LocMod.TensorModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLocalModelTensorWithHalfFunctionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocalModel_tensorWithHalfFunction : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (e : AE D), e * p.e = 0 → ∀ Φ : WO S T → ℂ, (∀ t, Φ t ≠ 0 → IsHalf e t) → ∀ (f₀ : WO S T → ℂ) (T' : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsPlaceModel ψ (symplO S T) (heisO ψ S T) (e + p.e) (stdHom S T) 1 f₀ T' → (∀ Φ', IsSBHalf (e + p.e) (stdHom S T) Φ' → IsThetaFunO ψ S T (T' Φ')) → (∀ Ψ ∈ SB (Matrix Y Y' k), IsSBHalf (e + p.e) (stdHom S T) (p.tensorAt FS FT Φ Ψ)) → p.IsModel ψ FS FT (T' ∘ₗ p.tensorL FS FT Φ) := by
  first | exact @GlobalTheory.LocMod.TensorModel.isModel_tensor | exact GlobalTheory.LocMod.TensorModel.isModel_tensor | (intros; apply GlobalTheory.LocMod.TensorModel.isModel_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactor
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactor
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChainTw


open GlobalTheory.LFun in
theorem dv_center_of_isSplit {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) (a t : ℕ) :
    dv E a (a + t) v ((t : ℂ) / 2) =
      (∏ n ∈ Finset.Ioc t (a + t), (1 - (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ n)⁻¹))⁻¹ := by
  have hI : Finset.Icc (t + 1) (t + a) = Finset.Ioc t (a + t) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  have he : etaU E v = 1 := by unfold etaU; exact if_pos hv
  rw [dv_center, hI, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [locL, etaFam_of_unram (isUnram_of_isSplit h2 hv), he, one_pow, eulerFac_singleton, Units.val_one, one_mul,
    npow, Complex.cpow_neg, Complex.cpow_natCast]

theorem dSfun_twist_restore : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ a : ℕ, GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) ≠ 0 ∧ GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ((D.R.t : ℂ) / 2) = GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) * ((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ) := by
  intro D c w hw a
  classical
  obtain ⟨hS, hQS₀, hinj, hsplit, -⟩ := GlobalTheory.T.chainTwistPlaces_split_unramifiedQuotients D c w hw
  have ht : 0 < ((D.R.t : ℂ) / 2).re := by
    have h3 := D.R.three_m_lt_t
    have h1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast (by omega : 1 ≤ D.R.t)
    simp only [Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  set s : ℂ := (D.R.t : ℂ) / 2 with hs_def
  set f : HeightOneSpectrum (𝓞 D.host.F) → ℂ := fun v => GlobalTheory.LFun.dv D.host.E a (a + D.R.t) v s with hf
  set Qv : Finset (HeightOneSpectrum (𝓞 D.host.F)) := w.Q.image fun PP => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hQv
  have h0 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ w.S₀}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv w.S₀ a (a + D.R.t) ht).multipliable.hasProd
  have h1 := (hasProd_subtype_iff_mulIndicator (s := {v | v ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))}) (f := f)).1
    (GlobalTheory.LFun.hasProd_dv (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ht).multipliable.hasProd
  have h2 := (hasProd_subtype_iff_mulIndicator (s := (Qv : Set (HeightOneSpectrum (𝓞 D.host.F)))) (f := f)).1
    (Finset.hasProd Qv f)
  have hmem : ∀ v, v ∈ Qv ↔ ∃ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := fun v => by simp [hQv]
  have hsplitf : Set.mulIndicator {v | v ∉ w.S₀} f =
      Set.mulIndicator {v | v ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))} f * Set.mulIndicator (Qv : Set _) f := by
    funext v
    simp only [Pi.mul_apply, Set.mulIndicator_apply, Set.mem_ofPred_eq, Finset.mem_coe]
    by_cases hq : v ∈ Qv
    · obtain ⟨PP, hPP, rfl⟩ := (hmem _).1 hq
      have hc : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ c.S := (hS _).2 (Or.inr ⟨PP, hPP, rfl⟩)
      simp [hQS₀ PP hPP, hc, hq]
    · by_cases h0' : v ∈ w.S₀
      · have hc : v ∈ c.S := (hS _).2 (Or.inl h0')
        simp [h0', hc, hq]
      · have hc : v ∉ c.S := fun hc => ((hS _).1 hc).elim h0' fun hx => hq ((hmem _).2 hx)
        simp [h0', hc, hq]
  rw [hsplitf] at h0
  have key : GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) s =
      GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) s * ∏ v ∈ Qv, f v :=
    h0.unique (h1.mul h2)
  have hloc : ∀ PP ∈ w.Q, f ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) = ((zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ)⁻¹ := by
    intro PP hPP
    obtain ⟨hsp, hN, -⟩ := hsplit PP hPP
    show GlobalTheory.LFun.dv D.host.E a (a + D.R.t) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ((D.R.t : ℂ) / 2) = _
    rw [dv_center_of_isSplit D.sp.cm.deg2 hsp, hN, zinv]
    push_cast
    rfl
  have hprod : ∏ v ∈ Qv, f v = (((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ)) : ℂ)⁻¹ := by
    rw [hQv, Finset.prod_image (fun x hx y hy h => hinj hx hy h), Finset.prod_congr rfl hloc,
      Finset.prod_inv_distrib]
    push_cast
    rfl
  have hne : GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) s ≠ 0 := GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ ht
  rw [hprod] at key
  have hZ : (((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ)) : ℂ) ≠ 0 := by
    intro h0
    apply hne
    rw [key, h0, _root_.inv_zero, mul_zero]
  refine ⟨hne, ?_⟩
  rw [key, mul_assoc, inv_mul_cancel₀ hZ, mul_one]

end GlobalTheory.ChainTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistEulerFactorsRestoreNormalizingFactorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistEulerFactors_restore_normalizingFactor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ a : ℕ, GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) ≠ 0 ∧ GlobalTheory.LFun.dSfun D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) a (a + D.R.t) ((D.R.t : ℂ) / 2) = GlobalTheory.LFun.dSfun D.host.E w.S₀ a (a + D.R.t) ((D.R.t : ℂ) / 2) * ((∏ PP ∈ w.Q, zinv PP D.R.t (a + D.R.t) : ℝ) : ℂ) := by
  first | exact @GlobalTheory.ChainTw.dSfun_twist_restore | exact GlobalTheory.ChainTw.dSfun_twist_restore | (intros; apply GlobalTheory.ChainTw.dSfun_twist_restore <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBase
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.TwDat


set_option maxHeartbeats 800000 in
theorem chr_root_mul_base {B : Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) {l : I.Laws} {Z : TC.Later B (I.cols l)}
    {u : B.Word} {a : I.ι} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch} (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m)
    (β : Ch k) (c : {c // A.chOf k c = β}) (x : (AE (I.rec7 l Z))ˣ) (hx : IsDetRoot _ (A.h k β c) x) :
    (A.chr ((j : ℕ) + 1) x : ℂ) * (A.chr ((j : ℕ) + 1) (A.xr k β) : ℂ) =
      ((tildeQ B.host I.SQ (I.C.mu0 j * I.xi a) (detPt B.host I.SQ ((I.stp u a k).rep c.1).1.1) : ℂˣ) : ℂ) := by
  obtain ⟨c, rfl⟩ := c
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hpt := (hA.reads k hk).pt c
  obtain ⟨a', ha'⟩ := GlobalTheory.Mem.DetLift.exists_isDetLift B.R B.host (B.R.N k) _ hpt.uni
  obtain ⟨hkA, hkAm, hxr⟩ := hA.kA k hk (A.chOf k c)
  obtain ⟨hh, hhm⟩ := hA.h k hk (A.chOf k c) ⟨c, rfl⟩
  have hg : A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c) ∈ GfC _ := mul_mem hh hkA
  have hfin : finM _ (rankN (I.rec7 l Z) k hk) (A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c)) =
      ((((show TC.GA B (B.R.N k) from ((A.K k hk (A.chOf k c)).y ⟨c, rfl⟩).1) * A.kb k (A.chOf k c) : TC.GA B (B.R.N k))) :
        Matrix (Fin (B.R.N k)) (Fin (B.R.N k)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) := by
    rw [GlobalTheory.RepLattice.finM_mul', hhm, hkAm, Units.val_mul]
    rfl
  have hroot := GlobalTheory.TwistFinPart.isDetRoot_mul' _ _ _ _ _ hx hxr
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := GlobalTheory.DetRootRead.chr_at_detRoot (I.rec7 l Z) (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) (hA.chr j)
    (Formalism.L2.Host.HChar.TrivOn.mul (I.C.isMu0 j).triv htw.2.1) _ _ _ _ hg hfin _ hroot a' ha'
  have hm := reference_characters_factor_tame I.SQ I.C j
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  have hfac : KDq B.host I.SQ ≤ ((I.C.mu0 j * I.xi a).1.comp (Chr.finPartI B.host.E)).ker := fun b hb => by
    have e : (I.C.mu0 j).1 (Chr.finPartI B.host.E b) = 1 := hm hb
    have e' : (I.xi a).1 (Chr.finPartI B.host.E b) = 1 := hxi hb
    show (I.C.mu0 j).1 (Chr.finPartI B.host.E b) * (I.xi a).1 (Chr.finPartI B.host.E b) = 1
    rw [e, e', one_mul]
  rw [← GlobalTheory.Mem.Col2.DetSpec.mk_eq_detPt B.R B.host _ _ _ _ _ _ _ a' hlev.1 hpt ha', tildeQ_mk _ _ hfac, ← Circle.coe_mul, ← map_mul]
  exact key

theorem rho_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c : (I.stp u a i).Cl) : (I.chIn u a).rho i c =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ)⁻¹ *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) ^
          (-((B.R.N (i + 1) / 2 : ℕ) : ℤ)) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt I.SQ I.C (I.xi a) i ((I.stp u a i).rep c).1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt, muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, mul_inv]

theorem rho'_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c' : (I.stp u a (i + 1)).Cl) : (I.chIn u a).rho' i c' =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a (i + 1)).rep c').1.1) : ℂˣ) : ℂ) *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N (i + 1))) ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) ^
          ((B.R.N i / 2 : ℕ) : ℤ) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt' I.SQ I.C (I.xi a) i ((I.stp u a (i + 1)).rep c').1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt', muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

theorem moves_alg (X Y r₀ r₁ a b : ℂ) (p q : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0) (h₀ : r₀ ≠ 0) (h₁ : r₁ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    X⁻¹ * Y = r₀ * r₁⁻¹ * ((X * r₀)⁻¹ * a ^ (-p) * (Y * r₁ * b ^ q)) * (a ^ p * b ^ (-q)) := by
  have h1 : a ^ p ≠ 0 := zpow_ne_zero p ha
  have h2 : b ^ q ≠ 0 := zpow_ne_zero q hb
  rw [_root_.zpow_neg, _root_.zpow_neg]
  field_simp

theorem chr_moves_eq_rho_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  intro B X I hI _ l Z u a Ch A hA i hi α γ c c' x y hx hy
  have h0 := chr_root_mul_base hI hA ⟨i, hi⟩ i (Nat.le_of_succ_le hi) α c x hx
  have h1 := chr_root_mul_base hI hA ⟨i, hi⟩ (i + 1) hi γ c' y hy
  rw [rho_eq I hI u a i hi, rho'_eq I hI u a i hi]
  simp only [ColIn.A, Col2.AmbIn.amb, Th.chiFac, ColIn.chi]
  rw [← h0, ← h1]
  exact moves_alg _ _ _ _ _ _ _ _ (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
    (Circle.coe_ne_zero _) (chiId_ne_zero _ _) (chiId_ne_zero _ _)

end GlobalTheory.AdForm.TwDat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBaseStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainMove_characters_eq_rho_up_to_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  first | exact @GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base | exact GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base | (intros; apply GlobalTheory.AdForm.TwDat.chr_moves_eq_rho_base <;> assumption)
end
end
