module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.TeichmullerCongruence

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PhiTTmul
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def AW (_ : Res l K) : Type := Acris l

instance (r : Res l K) : CommRing (AW r) := inferInstanceAs (CommRing (Acris l))

instance (r : Res l K) : Algebra (WittVector l r.k) (AW r) := r.w.toAlgebra

instance (r : Res l K) : Module (per l K).A (AW r) := inferInstanceAs (Module (Acris l) (Acris l))

instance (r : Res l K) : SMulCommClass (WittVector l r.k) (per l K).A (AW r) :=
  ⟨fun w a x => mul_left_comm (r.w w) (show Acris l from a) (show Acris l from x)⟩

def ofA (r : Res l K) (a : (per l K).A) : AW r := a

abbrev LW (r : Res l K) (M : Model l K) (j : ℕ) : Type 1 := (Wc.HS l (B.schFn M.p) r.ρ j).lim

abbrev HL (M : Model l K) (j : ℕ) : Type 1 := (M.HA true).N j

def phiL (M : Model l K) (j : ℕ) : HL M j →+ HL M j := (M.phiH j).lim.toAddMonoidHom

def galL (M : Model l K) (j : ℕ) (g : K.fixingSubgroup) : HL M j →+ HL M j := (M.HA true).act j g

def pullL {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (j : ℕ) : HL M' j →+ HL M j :=
  (Model.pullH u hu true j).lim.toAddMonoidHom

abbrev AL (r : Res l K) (M : Model l K) (j : ℕ) : Type 1 := AW r ⊗[WittVector l r.k] LW r M j

structure Fac (r : Res l K) (N : ℕ) where
  e : Model l K → ℕ → ℕ
  α : ∀ M j, HL M j →+ AL r M j
  β : ∀ M j, AL r M j →ₗ[(per l K).A] HL M j
  phiT : ∀ M j, AL r M j →+ AL r M j
  galT : ∀ M j, K.fixingSubgroup → AL r M j →+ AL r M j
  phiT_tmul : ∀ M, M.Sm → ∀ j (a : (per l K).A) (y : LW r M j),
    phiT M j (ofA r a ⊗ₜ y) = ofA r ((per l K).φ a) ⊗ₜ (Wc.phiS l (B.schFn M.p) r.ρ j).lim y
  galT_tmul : ∀ M, M.Sm → ∀ j g (a : (per l K).A) (y : LW r M j), galT M j g (ofA r a ⊗ₜ y) = ofA r ((per l K).σA g a) ⊗ₜ y
  lin : ∀ M, M.Sm → ∀ j (a : (per l K).A) (x : HL M j), α M j (a • x) = ((per l K).φ^[N] a) • α M j x
  fac : ∀ M, M.Sm → ∀ j (x : HL M j), β M j (α M j x) = ((l : (per l K).A) ^ e M j) • (phiL M j)^[N] x
  phi : ∀ M, M.Sm → ∀ j (x : HL M j), α M j (phiL M j x) = phiT M j (α M j x)
  gal : ∀ M, M.Sm → ∀ j g (x : HL M j), α M j (galL M j g x) = galT M j g (α M j x)
  galβ : ∀ M, M.Sm → ∀ j g (y : LW r M j), galL M j g (β M j ((1 : AW r) ⊗ₜ y)) = β M j ((1 : AW r) ⊗ₜ y)
  nat : ∀ (M M' : Model l K) (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p), M.Sm → M'.Sm → ∀ j (x : HL M' j), ∃ m : ℕ,
    ((l : (per l K).A) ^ m) • (((l : (per l K).A) ^ e M' j) • α M j (pullL u hu j x) -
      ((l : (per l K).A) ^ e M j) • (LinearMap.lTensor (AW r) (Wc.pullS l r.ρ (B.schMap u hu) j).lim) (α M' j x)) = 0

def perCOf (r : Res l K) (C₀ : Type) [CommRing C₀] (c : Acris l →+* C₀) (ι : C₀ →+* (per l K).B) (φ : C₀ →+* C₀)
    (σ : K.fixingSubgroup → C₀ →+* C₀) (q : ℚ_[l] →+* C₀) (k : Wc.K₀ l r.k →+* C₀) : PerC (per l K) where
  C := C₀
  K₀ := Wc.K₀ l r.k
  c := c
  ι := ι
  φ := φ
  σ := σ
  q := q
  k := k

end CrystallineSemistableComparison.Pb
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuMor
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg

namespace CrystallineSemistableComparison.Pb.Mid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : Res l K) {N : ℕ}

abbrev HM (M : Model l K) (n j : ℕ) : Type 1 := CH.H (B.OM (Lm r M n) ((base l).cris n)) j

def muMor (M : Model l K) (n : ℕ) (hT : TeichmullerCongruence r N) :
    CH.Mor (B.OM (Lm r M n) ((base l).cris n)) (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n))
      (RingHom.id _) :=
  B.omMor (mIn r M n hT) (RingHom.id _) fun _ => rfl

def nuMor (M : Model l K) (n : ℕ) (hT : TeichmullerCongruence r N) :
    CH.Mor (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) (B.OM (Lm r M n) ((base l).cris n)) (phiA l N) :=
  B.omMor (mOut r M n hT) (phiA l N) (phiP_cris n N)

def mu (M : Model l K) (n j : ℕ) (hT : TeichmullerCongruence r N) :
    HM r M n j →ₗ[Acris l] CH.H (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) j :=
  (muMor r M n hT).pull j

def nu (M : Model l K) (n j : ℕ) (hT : TeichmullerCongruence r N) :
    CH.H (B.OM (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).cris n)) j →ₛₗ[phiA l N] HM r M n j :=
  (nuMor r M n hT).pull j

end CrystallineSemistableComparison.Pb.Mid
end
end
