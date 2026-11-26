module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetsOfOrthogonalSum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PairingOfPointsExpansion
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstRowInvariantUnderTwist
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.VertexPairPointsTransformationLaw
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstCoefficientDatumLaw
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LeadingCoefficientTermLawTheta
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EndomorphismLawFromFirstRowTwist
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistFirstRowScalarMultiple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.RowVacScalar GlobalTheory.FirstRowTermLaw GlobalTheory.FirstRowEndLaw
noncomputable section
namespace GlobalTheory.FirstRowScalar
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
variable {G : GridData L sc} {W : G.Weil} {U : Set T}
section Red
open GlobalTheory.FunObj.Comparison₂
variable {S κ K : Type} [CommRing S] [CommRing κ] [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {φ : S →+* κ} {ψ : S →+* K} {r t j a : ℕ} {ea : Ix (Fin r) (Fin t) j ≃ Fin a}
end Red
theorem firstRow_scalar_multiple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
          ∏ w : locPl ch.G t, GlobalTheory.FirstRowEndLaw.endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k) =
        ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
          (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) :=
  fun _ _ => ⟨0, fun _ _ _ => ⟨0, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s ch _ _ t k hk hk' c hc =>
    scalar_of_is ch.S.toGridChoice s.core.lev t k hk hk' c hc⟩⟩
end GlobalTheory.FirstRowScalar
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_firstRow_scalar_multiple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
          ∏ w : locPl ch.G t, GlobalTheory.FirstRowEndLaw.endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k) =
        ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
          (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  first | exact @_root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple | exact _root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple | (intros; apply _root_.GlobalTheory.FirstRowScalar.firstRow_scalar_multiple <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData
open GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FirstRowEndLaw
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k] {Γ : Grid k}
end Local
end GlobalTheory.FirstRowEndLaw
namespace GlobalTheory.FirstRowEndLaw
open GlobalTheory.FunObj.GivenAdm
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}
variable {μ₀ : T} {G : GridData L sc} {t : T} {w : Pl D.host.E}
end GlobalTheory.FirstRowEndLaw
namespace GlobalTheory.FirstRowEndLaw
open GlobalTheory.FunObj.GivenAdm
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} {G : GridData L sc} {t : T} {w : Pl D.host.E}
end GlobalTheory.FirstRowEndLaw
namespace GlobalTheory.FirstRowEndLaw
open GlobalTheory.FunObj.GivenAdm
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} {G : GridData L sc} {w : Pl D.host.E}
end GlobalTheory.FirstRowEndLaw
namespace GlobalTheory.FirstRowEndLaw
set_option maxHeartbeats 1600000 in
theorem square_identity_reduction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (a : Fin ch.n) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      ∃ lam : locPl ch.G t → ℂ,
        (∀ w : locPl ch.G t, (locGrid ch.G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (Tflip ch.W ch.S.B t (ch.Phi a) w) =
          lam w • Tflip ch.W ch.S.B t (ch.Phi a) w) ∧
        (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c * ∏ w, lam w =
          ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  intro hP hS
  obtain ⟨CF0, hsc⟩ := _root_.GlobalTheory.T.twist_firstRow_scalar_multiple hP hS
  refine ⟨CF0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, hsc⟩ := hsc ε CF hC
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hat => ?_⟩
  have hs := hsc D large₂ he hx Γ Pl0 T A Ks R F s ch hch hat
  intro t a k hk hk' c hc
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := pde_ne_q' s
  have hcg : ∀ P ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hch.guard t
  refine ⟨fun w => endLam ch.G t w.1 (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w.1 k), fun w => ?_, hs t k hk hk' c hc⟩
  exact Tflip_law hL ch.W ch.S.B t (ch.Phi a) hde hcg w.2 _ (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hk).1 w)
end GlobalTheory.FirstRowEndLaw
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_law_from_first_row_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (a : Fin ch.n) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
      ∃ lam : locPl ch.G t → ℂ,
        (∀ w : locPl ch.G t, (locGrid ch.G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (Tflip ch.W ch.S.B t (ch.Phi a) w) =
          lam w • Tflip ch.W ch.S.B t (ch.Phi a) w) ∧
        (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c * ∏ w, lam w =
          ∏ w : locPl ch.G t, (locGrid ch.G t w).edgeFactor .one
            (Pi.mulSingle (0, D.R.m) (GlobalTheory.FirstRowTermLaw.kapAt ch.S.toGridChoice t w k)) (.ex 0 D.R.m) := by
  first | exact @_root_.GlobalTheory.FirstRowEndLaw.square_identity_reduction | exact _root_.GlobalTheory.FirstRowEndLaw.square_identity_reduction | (intros; apply _root_.GlobalTheory.FirstRowEndLaw.square_identity_reduction <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.FirstRowTermLaw
end GlobalTheory.FirstRowTermLaw
namespace GlobalTheory.FirstRowTermLaw
set_option maxHeartbeats 1000000 in
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
    ∀ (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
        (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
            (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := _root_.GlobalTheory.T.endomorphism_law_from_first_row_twist hP hS
  refine ⟨a₁, fun ε CF hC => ?_⟩
  obtain ⟨x₁, hc₁⟩ := h₁ ε CF hC
  refine ⟨x₁, ?_⟩
  intro D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc t a β hβ τ hτ k hkl hk c hc xs ys
  obtain ⟨lam, hlam, hscal⟩ := hc₁ D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc t a k hkl hk c hc
  have hL : (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D) (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn ((actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) :=
    sum_update_comp τ (fun d j => (d.1 j).fn) (fun d i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D) (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) xs ys
  rw [hL]
  exact law_gen ch.S.toGridChoice (Set.mem_univ t) hτ k lam hlam _ hscal xs ys
end GlobalTheory.FirstRowTermLaw
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leading_coefficient_term_law_theta : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
    ∀ (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
        (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
            (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  first | exact @_root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally | exact _root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally | (intros; apply _root_.GlobalTheory.FirstRowTermLaw.lift_splits_locally <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FirstRowDatum
theorem first_coefficient_datum_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := _root_.GlobalTheory.T.leading_coefficient_term_law_theta hP hS
  obtain ⟨a₂, h₂⟩ := hS
  refine ⟨max a₁ a₂, fun ε CF hC => ?_⟩
  have hb₁ := h₁ ε CF (le_of_max_le_left hC)
  have hb₂ := h₂ ε CF (le_of_max_le_right hC)
  obtain ⟨x₁, hc₁⟩ := hb₁
  obtain ⟨x₂, hc₂⟩ := hb₂
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ k hkl hk xs ys
  have key := hc₁ D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ k hkl hk
  have hOK := hc₂ D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a
  have hv := hOK.vec β τ hτ
  obtain ⟨e, he, hsupp, -⟩ := hτ
  have hsv := GlobalTheory.FirstRowShift.rowShift0_model (G := ch.G) (W := ch.W) (U := Set.univ) ch.S.toGridChoice s.core.lev (t := t) (e := e) (Set.mem_univ t) he k hkl
  obtain ⟨c, hc, hshift⟩ := hsv
  have hkey := key c hc
  generalize hχk : (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) = χk at hkey ⊢
  simp only [Finsupp.sum] at hkey ⊢
  rcases Finset.eq_empty_or_nonempty τ.support with h0 | ⟨d₀, hd₀⟩
  · simp [h0]
  have hTC : ∀ j : Fin D.R.m, ∃ Tm, IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
      (latO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) (ch.S.N.latS (.top t j) : Set _) (ch.S.N.latT (.top t j) : Set _)
        fun _ => True) 1 (ch.S.Z.vac (.top t j)) Tm := by
    intro j
    obtain ⟨f, hf⟩ := (hv d₀ hd₀).1 j
    have hE := ((hsupp d₀ hd₀).1 j).2.1
    unfold FinDatum.IsTheta at hf
    rw [hE] at hf
    exact hf.1
  have hTR : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel ch.W.ψ (symplO _ _) (heisO ch.W.ψ _ _) e
      (latO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) (ch.S.N.latS (.chi i D.R.m : Pair T) : Set _)
        (ch.S.N.latT (.chi i D.R.m : Pair T) : Set _) fun _ => True) 1 (ch.S.Z.vac (.chi i D.R.m : Pair T)) Tm := by
    intro i
    obtain ⟨f, hf⟩ := (hv d₀ hd₀).2 i
    have hE := ((hsupp d₀ hd₀).2 i).2.1
    unfold FinDatum.IsTheta at hf
    rw [hE] at hf
    exact hf.1
  choose TmC hTmC using hTC
  choose TmR hTmR using hTR
  have hvecC : ∀ d ∈ τ.support, ∀ j, ch.S.Z.vec (d.1 j) = TmC j (d.1 j).fn := by
    intro d hd j
    obtain ⟨f, hf⟩ := (hv d hd).1 j
    have hE := ((hsupp d hd).1 j).2.1
    have hz := ((hsupp d hd).1 j).2.2
    have hf' := hf
    unfold FinDatum.IsTheta at hf'
    rw [hE] at hf'
    rw [Normal.vec, FinDatum.vec_eq ch.W hf, hz, hf'.2 _ (hTmC j)]
    show ch.W.om _ 1 _ = _
    rw [map_one]; rfl
  have hvecR : ∀ d ∈ τ.support, ∀ i, ch.S.Z.vec (d.2 i) = TmR i (d.2 i).fn := by
    intro d hd i
    obtain ⟨f, hf⟩ := (hv d hd).2 i
    have hE := ((hsupp d hd).2 i).2.1
    have hz := ((hsupp d hd).2 i).2.2
    have hf' := hf
    unfold FinDatum.IsTheta at hf'
    rw [hE] at hf'
    rw [Normal.vec, FinDatum.vec_eq ch.W hf, hz, hf'.2 _ (hTmR i)]
    show ch.W.om _ 1 _ = _
    rw [map_one]; rfl
  have hext := sum_prod_map_eq_zero₂ TmC TmR (τ.support.disjSum τ.support)
    (Sum.elim (fun d => χk * c * τ d) (fun d => -τ d))
    (Sum.elim (fun d : PureDat ch.G t => fun j => (d.1 j).fn) (fun d : PureDat ch.G t => fun j => (d.1 j).fn))
    (Sum.elim (fun d : PureDat ch.G t => Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
        (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)))
      (fun d : PureDat ch.G t => fun i => (d.2 i).fn))
    (fun x y => by
      have h1 := hkey x y
      rw [Finset.mul_sum] at h1
      rw [Finset.sum_disjSum]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib]
      rw [← h1, add_neg_eq_zero]
      exact Finset.sum_congr rfl fun d _ => by ring) xs ys
  rw [Finset.sum_disjSum] at hext
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, add_neg_eq_zero] at hext
  refine Eq.trans ?_ (hext.trans ?_)
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hsb := (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).sb
    rw [((hsupp d hd).2 (GlobalTheory.FirstRowVertex.firstIx D)).2.1] at hsb
    simp only [hvecC d hd, hvecR d hd]
    rw [hshift (TmR (GlobalTheory.FirstRowVertex.firstIx D)) (hTmR _) _ hsb, GlobalTheory.FirstRowVertex.prod_update_smul]
    have hu : ∀ i, Function.update (fun i => TmR i (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
        (TmR (GlobalTheory.FirstRowVertex.firstIx D) (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn
          (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y))) i (ys i) =
        TmR i (Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
          (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn
            (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i) (ys i) := by
      intro i
      by_cases hi : i = GlobalTheory.FirstRowVertex.firstIx D
      · subst hi
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hi]
    simp only [hu]
    ring
  · refine Finset.sum_congr rfl fun d hd => ?_
    simp only [hvecC d hd, hvecR d hd]
end GlobalTheory.FirstRowDatum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_first_coefficient_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  first | exact @_root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law | exact _root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law | (intros; apply _root_.GlobalTheory.FirstRowDatum.first_coefficient_datum_law <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FirstRowVertex
open GlobalTheory.LastVertexInv in
theorem pair_points_first_vertex_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m)) (k : FinPt ch.G (.grid 0 D.R.m))
      (_ : finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _)) (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (v : VV ℂ (wt ch.G (.top 0))) (w : VV ℂ (listedWt ch.G (.grid 0 D.R.m))),
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v
        ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • w) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := _root_.GlobalTheory.T.twist_first_coefficient_law hP hS
  obtain ⟨a₂, h₂⟩ := hS
  refine ⟨max a₁ a₂, fun ε CF hC => ?_⟩
  have hb₁ := h₁ ε CF (le_of_max_le_left hC)
  have hb₂ := h₂ ε CF (le_of_max_le_right hC)
  obtain ⟨x₁, hc₁⟩ := hb₁
  obtain ⟨x₂, hc₂⟩ := hb₂
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ x y k hkl hk v w
  have key := hc₁ D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ k hkl hk
  have hOK := hc₂ D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a
  generalize hχk : (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) = χk at key ⊢
  have hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.2 i)) :=
    fun d hd => ⟨fun j => vec_theta ch.S.toGridChoice (defPair_top t j) (inRange_top t j) _ ((hOK.vec β τ hτ d hd).1 j),
      fun i => vec_theta ch.S.toGridChoice (defPair_chi i) (inRange_chi i) _ ((hOK.vec β τ hτ d hd).2 i)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_multilinear_columnRowKernelPairing ch.S.toGridChoice t x y v w
  have thr : ∀ d ∈ τ.support, ∀ i,
      IsThetaFunO ch.W.ψ _ _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) := by
    intro d hd i
    by_cases hi0 : i = firstIx D
    · subst hi0
      simp only [movedRow, Function.update_self]
      exact rowShift0_theta ch.S.toGridChoice k ((hth d hd).2 _)
    · simp only [movedRow, Function.update_of_ne hi0]
      exact (hth d hd).2 i
  have thr' : ∀ d ∈ τ.support, ∀ i, IsThetaFunO ch.W.ψ _ _
      (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
        (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i) := by
    intro d hd i
    by_cases hi0 : i = firstIx D
    · subst hi0
      simp only [Function.update_self]
      exact GlobalTheory.OrientedHeis.theta_smul χk (thr d hd _)
    · simp only [Function.update_of_ne hi0]
      exact thr d hd i
  have lhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v w =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)) := by
    simp only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq, rowMapV_update_zero ch.S.toGridChoice _ y k ((hth d hd).2 _)]
    have e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) =
        fun j : Fin D.R.m => ch.S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh ch.W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) :
        WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) :=
      funext fun i => coe_toTh ch.W _ (thr d hd i)
    rw [e1, e2]
  have rhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (ch.S.Z.vec (d.2 i))) := by
    simp only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq]
    have e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) =
        fun j : Fin D.R.m => ch.S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh ch.W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.2 i)) :
        WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        fun i : Fin D.R.m => ch.S.Z.vec (d.2 i) :=
      funext fun i => coe_toTh ch.W _ ((hth d hd).2 i)
    rw [e1, e2]
  have hscale : ∀ d ∈ τ.support,
      M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) =
      χk * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)) := by
    intro d hd
    have eg : (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T)
        (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) =
        Function.update (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T) (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i))
          (firstIx D) (χk • toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D))) := by
      funext i
      by_cases hi0 : i = firstIx D
      · subst hi0
        apply Subtype.ext
        have h1 := coe_toTh ch.W _ (thr' d hd (firstIx D))
        simp only [Function.update_self] at h1 ⊢
        rw [h1, Submodule.coe_smul, coe_toTh ch.W _ (thr d hd _)]
      · simp only [Function.update_of_ne hi0]
    rw [eg, MultilinearMap.map_update_smul, Function.update_eq_self, smul_eq_mul]
    rfl
  rw [LinearMap.map_smul, smul_eq_mul, lhs, rhs, Finsupp.sum, Finset.mul_sum]
  have step1 : (∑ d ∈ τ.support, χk * (τ d * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)))) =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hscale d hd]
    ring
  rw [step1]
  refine GlobalTheory.T.multilinear_sum_eq_of_function_product_sums_eq M τ _ _ _ _ fun xs ys => ?_
  have hk' := key xs ys
  simp only [Finsupp.sum] at hk' ⊢
  refine (?_ : _ = χk * _).trans (hk'.trans (Finset.sum_congr rfl fun d hd => ?_))
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ (thr' d hd _)]
    rw [prod_update_smul, Function.update_eq_self]
    simp only [movedRow]
    ring
  · simp only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ ((hth d hd).2 _)]
end GlobalTheory.FirstRowVertex
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertex_pair_points_transformation_law : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m)) (k : FinPt ch.G (.grid 0 D.R.m))
      (_ : finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _)) (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (v : VV ℂ (wt ch.G (.top 0))) (w : VV ℂ (listedWt ch.G (.grid 0 D.R.m))),
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v
        ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • w) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w := by
  first | exact @_root_.GlobalTheory.FirstRowVertex.pair_points_first_vertex_law | exact _root_.GlobalTheory.FirstRowVertex.pair_points_first_vertex_law | (intros; apply _root_.GlobalTheory.FirstRowVertex.pair_points_first_vertex_law <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.FirstRowLaw
section Gen
variable {Gg Γg : Type} [Group Gg] [Group Γg] {Wg : Type} [NormedAddCommGroup Wg] [InnerProductSpace ℂ Wg]
end Gen
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} {W : G.Weil} {U : Set T}
theorem first_row_invariant_under_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (u : (R.HX t).H) (v : VV ℂ (wt ch.G (.top 0))) (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m))
      (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v (ch.S.formC t u (y 0 * k)) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v (ch.S.formC t u (y 0)) := by
  intro hP hS
  obtain ⟨a, h1⟩ := GlobalTheory.T.gridBottomLevel_le_formLevel_largeDepth
  obtain ⟨b, h2⟩ := _root_.GlobalTheory.T.vertex_pair_points_transformation_law hP hS
  refine ⟨max a b, fun ε CF hC => ?_⟩
  obtain ⟨x₁, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x₂, h2⟩ := h2 ε CF (le_of_max_le_right hC)
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ u v x y k hk0
  have hk := h1 D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t k hk0
  have hC := h2 D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ x y k hk0 hk v
  rw [formC_mul ch.S s.core.models.HX t u (y 0) k hk]
  exact hC _
end GlobalTheory.FirstRowLaw
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
section
open GlobalTheory.DefStep GlobalTheory.JetsOne GlobalTheory.ExpansionInvariance
private theorem last_functional_compatible {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T} (hL : L.Is μ0) (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) :
    ∃ (c : ℂ) (s : GA D (G.V (.grid D.R.m D.R.m)) →* GA D (G.V (.top D.R.m))), (∀ h, stabilizerEmbedding G.sp.topDec h = s h) ∧
      LastOK (realAct W.θ S.N.fr (.top D.R.m)) Λ (realAct W.θ S.N.fr (.grid D.R.m D.R.m)) Λ' s (finEmb G.sp.topDec)
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m D.R.m))
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hdef := GlobalTheory.TopIntegral.isDefinite_last G
  haveI : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) := isCompact_iff_compactSpace.1 (Eqv.isCompact_GinfC hdef.1 hdef.2)
  obtain ⟨κ₀, k1, k2⟩ := exists_haar _ hdef
  obtain ⟨c, hc⟩ := GlobalTheory.TopIntegral.real_average W.θ_is S.N Λ Λ' κ₀
  obtain ⟨s, h1, h2, h3⟩ := GlobalTheory.TopIntegral.exists_orthogonal_summand_embedding_hom G.sp.topDec
  refine ⟨c, s, h2, hdef, posDef_grid hL le_rfl, fun g hg => realAct_fin _ _ _ hg, fun g hg => realAct_fin _ _ _ hg, h1, h3,
    fun z => (h2 _).symm.trans (GlobalTheory.RealType.Emb_fin _ z), fun k hk => h2 k ▸ GlobalTheory.RealType.Emb_mem_inf _ hk,
    fun u u' => ?_, fun κ a1 a2 u u' => ?_⟩
  · simp only [← h2]
    exact (GlobalTheory.TopIntegral.continuous_integrand W.θ_is S.N Λ Λ' u u').comp continuous_subtype_val
  · obtain rfl : κ = κ₀ := Measure.isHaarMeasure_eq_of_isProbabilityMeasure κ κ₀
    simp only [← h2]
    exact hc u u'
private theorem pairing_of_points_expansion {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (c : ℂ) (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0)))
    (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) (X : ∀ j, FinPt G (.top j))
    (Y : ∀ i, FinPt G (.grid i D.R.m)) :
    c * pairPts S τ X Y (Ψ (X 0)) (F (Y 0)) = τ.sum fun d a => a *
      GlobalTheory.JetsOne.pairP (V := fun j => G.V (.top j)) (V' := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.top j)))
        (Mo' := fun j => VV ℂ (wt G (.grid j D.R.m))) (colComp S d) (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x))
        (rowComp S d) (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹
          (funOf (listedWt G (.grid 0 D.R.m)) (F x))) D.R.m
        (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) X Y := by
  rw [pairPts, Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  refine (mul_left_comm c (τ d) _).trans (congrArg (τ d * ·) ?_)
  exact (congrArg₂ (fun a b => (c • brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))) a b)
    (ptV_eq_chainTo (V := fun j => G.V (.top j)) (Mo := fun j => VV ℂ (wt G (.top j))) (colComp S d)
      (fun x => rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ (Ψ x)) X D.R.m)
    (ptV_eq_chainTo (V := fun j => G.V (.grid j D.R.m)) (Mo := fun j => VV ℂ (wt G (.grid j D.R.m))) (rowComp S d)
      (fun x => rhoVr (tauE D) (wt G (.grid 0 D.R.m)) (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) (F x)))
      Y D.R.m)).symm
end
theorem _root_.GlobalTheory.T.twisted_pairing_identity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun ch => ∀ P : PolCol ch.G × PolRow ch.G, ∃ κ : ℂ, ∀ t a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ M τ, IsTermVol t ch.S.toGridChoice (ch.Phi a) β M → ch.S.IsExpansion t (ch.Phi a) β τ → ∀ y, defTot t ch.S.toGridChoice M (Finsupp.single P 1) τ (colFn ch a) (formTop ch t y) = κ * ch.S.classSum (ch.Phi a) β τ (psiC (ch.Psi a)) (ch.S.formC t y) := by
  intro hP hS
  obtain ⟨C0, H⟩ := Big.and hS (_root_.GlobalTheory.FirstRowLaw.first_row_invariant_under_twist hP hS)
  refine ⟨C0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  refine ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc P => ?_⟩
  obtain ⟨hOK, h0⟩ := H D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨Λ0, hΛ0⟩ := GlobalTheory.JetsOne.col_real ch
  obtain ⟨Λ0', hΛ0'⟩ := GlobalTheory.JetsOne.form_real ch s.core.models.cX
  obtain ⟨Λ, rfl, hΛ⟩ := GlobalTheory.JetsOne.col_chain ch.S.toGridChoice hL P Λ0
  obtain ⟨Λ', rfl, hΛ'⟩ := GlobalTheory.JetsOne.row_chain ch.S.toGridChoice hL P Λ0'
  obtain ⟨c, σ, hσ, hlast⟩ := last_functional_compatible ch.S.toGridChoice hL (Λ D.R.m) (Λ' D.R.m)
  refine ⟨c, fun t a β hβ M τ hM hτ y => ?_⟩
  have hv := (hOK t a).vec β τ hτ
  obtain ⟨v1, v2⟩ := TermVolDef.isMeasDef_of_isTermVol ch.S.toGridChoice hL t _ β M hM
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.T.normalisedKernelExpansionSum_levelInvariant ch.S.toGridChoice hL (GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s) (hi.guard t)
    (Set.mem_univ t) hβ hτ hv (psiC (ch.Psi a)) (ch.S.formC t y)
  have hK0 : ∀ h : 0 < D.R.m, ch.S.levTop t (ch.Phi a) β 0 h = ch.G.Kplus := fun _ => rfl
  have key := GlobalTheory.JetsOne.glue (V := fun j => ch.G.V (.top j)) (V' := fun j => ch.G.V (.grid j D.R.m)) τ
    (fun d hd => hΛ t (Set.mem_univ t) d (hv d hd).1) (hΛ0 a) (GlobalTheory.JetsOne.col_left ch a)
    (fun d hd => GlobalTheory.JetsOne.col_near _ P d (hv d hd).1 (GlobalTheory.JetsOne.col_fix ch a (v1 0 hm).2.1))
    (fun d hd => hΛ' t (Set.mem_univ t) d (hv d hd).2) (hΛ0' t y) (GlobalTheory.JetsOne.form_aut s ch t y).1
    (fun d hd => GlobalTheory.JetsOne.row_near _ P d (hv d hd).2 (GlobalTheory.JetsOne.form_aut s ch t y).2) hlast
    (fun n hn => posDef_top ch.G hn.le) (fun n hn => posDef_grid hL hn)
    (fun j => M.ν (.top j)) (fun j => M.fd (.top j)) (ch.S.levTop t (ch.Phi a) β) (fun n hn => (v1 n hn).2)
    (fun j => M.ν (.grid j D.R.m)) (fun j => M.fd (.grid j D.R.m)) (ch.S.levRow t) (fun n hn => (v2 n hn).2)
    (fun X Y => c * GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ X Y (psiC (ch.Psi a) (X 0)) (ch.S.formC t y (Y 0)))
    (pairing_of_points_expansion ch.S.toGridChoice τ c _ _)
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := i2 (GlobalTheory.JetsOne.psiC_right ch a) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i1 X Y _ j.succ_pos hj k hk))
    (fun X Y j hj k hk => by
      rcases j with _ | j
      · have := h0 t a β hβ τ hτ y (psiC (ch.Psi a) (X 0)) X Y k hk
        beta_reduce
        rw [Function.update_self, this]
      · exact congrArg _ (i3 X Y _ j.succ_pos hj k hk))
    (fun X Y k h1 hk => congrArg _ (i4 X Y k h1 hk))
  rw [defTot, Finsupp.sum_single_index (by simp)]
  simp only [one_mul, GlobalTheory.JetsOne.defPer_eq, hσ]
  refine key.trans ?_
  rw [GridChoice.classSum, mul_finsum]
  exact finsum_congr fun c' => mul_left_comm _ _ _
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
namespace GlobalTheory.RowClaim.JetsAssembly
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
variable {D : D7} {T : Type}
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
theorem twisted_jet_one_of_all : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → Big fun ch => JetsOne ch := _root_.GlobalTheory.T.twisted_pairing_identity
theorem twistedJet_succ_eq_assembly : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → StepJets := by
  intro hP hS
  obtain ⟨C0, H⟩ := _root_.GlobalTheory.RowClaim.JetsAssembly.twisted_jet_one_of_all hP hS
  refine ⟨C0, fun ε CF hC => ?_⟩
  obtain ⟨x₀, H⟩ := H ε CF hC
  exact ⟨x₀, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch i j =>
    jetsAt_of_one ch s.core.lev (H D large₂ e hx Γ Pl0 T A Ks R F s ch i j)⟩
end GlobalTheory.RowClaim.JetsAssembly
end
end

section
open GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_jets_assemble : _root_.GlobalTheory.FunPr.ThetaLocalInputs → SumOKK → StepJets := by
  first | exact @_root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly | exact _root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly | (intros; apply _root_.GlobalTheory.RowClaim.JetsAssembly.twistedJet_succ_eq_assembly <;> assumption)
end
