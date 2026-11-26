module

public import Formalism.LocalToGlobal.HeckeThetaElements.IsHeckeElt
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
public import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.DatumVec
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

namespace Formalism.IndefR.Datum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev EAf (D : D7) : Type := D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F

def toEAf (D : D7) : AE D →+* EAf D :=
  ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom).comp (finPart D)

def eToEAf (D : D7) : D.host.E →+* EAf D := Algebra.TensorProduct.includeLeftRingHom

def frMapO (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x : WO S T) :
    Matrix (Fin T.rank) (Fin S.rank) (EAf D) :=
  HMul.hMul (HMul.hMul (βT⁻¹).val ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D))) βS.val

def frMapAdj (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (x : WO S T) : Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  HMul.hMul (HMul.hMul (βS⁻¹).val
    ((HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
      (T.gram.map (incA D))).map (toEAf D)))
    βT.val

def IsIntM {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) : Prop :=
  ∀ i j, N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E


open Classical in
def redM (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) :
    Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP) :=
  fun i j => if h : N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E then Formalism.L2.DIV.resS D.host.F PP ⟨N i j, h⟩ else 0

def topL {κ : Type} [Zero κ] {b a : ℕ} (k : ℕ) (y : Matrix (Fin b) (Fin a) κ) : Matrix (Fin k) (Fin k) κ :=
  fun i j => if h : i.val < b ∧ j.val < a then y ⟨i.val, h.1⟩ ⟨j.val, h.2⟩ else 0

def LowZero {κ : Type} [Zero κ] {b a : ℕ} (k : ℕ) (y : Matrix (Fin b) (Fin a) κ) : Prop :=
  ∀ i j, k ≤ i.val → j.val < k → y i j = 0


open Classical in
def omegaG {a b : ℕ} (L : Formalism.L2.DIV.LevDat D.host.E ℂ a) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧
      ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (Formalism.L2.DIV.kP PP.1),
        (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
        (∀ PP : ↥L.Pg, g PP ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        (fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (g PP)) ∈ L.P.H then
    ((L.P.chi ⟨fun PP => Formalism.L2.DIV.upperLeftBlock L.hr (h.2.choose PP), h.2.choose_spec.2.2⟩ : ℂˣ) : ℂ) *
      (∏ PP : ↥L.Pg, ∏ c ∈ Finset.range L.s,
        ((L.cg (c + 1) PP.1 (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf L.r L.t) (c + 1) (h.2.choose PP)) : ℂˣ) : ℂ)) *
      ∏ PP : ↥L.Pg, (((χj PP.1 (Matrix.GeneralLinearGroup.det (h.2.choose PP))) : ℂˣ) : ℂ)⁻¹
  else 0


open Classical in
def omegaQ {a b : ℕ} (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (r : ℕ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (k : ℤ) (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if h : ∀ PP ∈ Q, LowZero r (y PP) ∧ IsUnit (topL r (y PP)).det then
    ∏ PP ∈ Q.attach, (((ξ PP.1 (h PP.1 PP.2).2.unit) : ℂˣ) : ℂ) ^ k
  else 0


open Classical in
def omegaK {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : ℂ :=
  if ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1 then 1 else 0

def IsIdemSum (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  (∃ es : Formalism.L2.DIV.Pl D.host.E → AE D, (∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) ∧ e = ∑ PP ∈ P, es PP) ∧
    e * cA D e = 0


open Classical in
def IsStepVecOf (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ) : Prop :=
  IsVacO ψ θ S T sS sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (LS.Pg ∪ Q) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if IsHalf e x ∧ IsIntM (frMapO S T βS βT x) then
        omegaG LS χj (fun PP => redM PP (frMapO S T βS βT x)) *
          omegaQ Q LS.r ξ 1 (fun PP => redM PP (frMapO S T βS βT x))
        else 0) f


open Classical in
def IsThPVecOf (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (f₀ f : WO S T → ℂ) : Prop :=
  IsVacO ψ θ S T sS sT ΛS ΛT f₀ ∧ ∃ e : AE D, IsIdemSum e (Pg ∪ Q) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀
      (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) then
        omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) *
          omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x))
        else 0) f

def pureTensorO (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (f : WO S T → ℂ) : MvPolynomial (FVar D T.rank S.rank) ℂ →ₗ[ℂ] (WO S T → ℂ) :=
  pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) f

def PlaceModelExistsSum (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ (f₀ : WO S T → ℂ), IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ →
      (∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm) ∧
      ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm


open Classical in
def StepVecExists (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (LS : Formalism.L2.DIV.LevDat D.host.E ℂ S.rank) (χj : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ)
    (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint LS.Pg Q →
    (∃ e : AE D, IsIdemSum e (LS.Pg ∪ Q)) →
    ∀ f₀, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → ∃ f, IsStepVecOf ψ θ S T sS sT ΛS ΛT βS βT LS χj Q ξ f₀ f


open Classical in
def ThPVecExists (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D)
    (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E))
    (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → Disjoint Pg Q →
    (∃ e : AE D, IsIdemSum e (Pg ∪ Q)) →
    ∀ f₀, IsVacO ψ θ S T sS sT ΛS ΛT f₀ → ∃ f, IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f

def VecLaw {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (KS : Subgroup (GA D S))
    (chS : GA D S → ℂ) (KT : Subgroup (GA D T)) (chT : GA D T → ℂ) (f : WO S T → ℂ) : Prop :=
  (∀ κ ∈ KS, om (κ, 1) f = chS κ • f) ∧ ∀ κ ∈ KT, om (1, κ) f = chT κ • f

end Formalism.IndefR.Datum

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Col

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete3

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

theorem definite_coordinates_in_subspaces (X : CxData A3.fam3.amb3) (b : Bool) : X.CrdZ (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x
  cases b <;> exact toF_mem_Z _ _ _

theorem definite_coordinates_in_good_part (X : CxData A3.fam3.amb3) (b : Bool) :
    X.CoordinatesInGoodPart (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro t x
  cases b <;> exact BlockGood.toF_mem_goodR _ _ _ x

theorem lift_coordinates_in_subspaces (X : CxData A3.fam3.amb3) (b : Bool) : X.CrdZL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x
  cases b <;> exact toF_mem_Z _ _ _

theorem lift_coordinates_in_good_part_family (X : CxData A3.fam3.amb3) (b : Bool) :
    X.LiftCoordinatesInGoodPart (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro j t x
  cases b <;> exact BlockGood.toF_mem_goodR _ _ _ x

theorem definite_isometry_of_norms {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s) (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1))
    (hn : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)) (b : Bool) : X.IsoR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro t x y
  have h2 := hok.ok2
  cases b
  · rw [hJ t, hn.1]
    exact BlockGood.csum_toF_at _ h2.conj (h2.what₂ t) _ h2.irr _ x y
  · rw [hJ t, hn.2]
    exact BlockGood.csum_toF_at _ h2.conj (h2.what₂ t) _ h2.irr _ x y

theorem lift_isometry_of_norms {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1))
    (hn : X.nP false = (Nat.card P0 : ℝ) ∧ X.nP true = (Nat.card P1 : ℝ)) (b : Bool) : X.IsoL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j t x y
  have h2 := hok.ok2
  cases b
  · rw [hJ j t, hn.1]
    exact BlockGood.csum_toF_at _ h2.conj (h2.lifts j t) _ h2.irr _ x y
  · rw [hJ j t, hn.2]
    exact BlockGood.csum_toF_at _ h2.conj (h2.lifts j t) _ h2.irr _ x y

theorem definite_adjoint_closed {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s)
    (hH : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) (hK : X.KFormR)
    (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1)) : X.AdjClosedR := by
  intro t i
  rcases i with (p | k) | g
  · obtain ⟨p', hp'⟩ := (hH t).1.adj p
    exact ⟨Sum.inl (Sum.inl p'), X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inl (Sum.inl p)) (Sum.inl (Sum.inl p'))
      fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH t).2.adj k
    exact ⟨Sum.inl (Sum.inr k'), X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inl (Sum.inr k)) (Sum.inl (Sum.inr k'))
      fun f f' => hk' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.what₂ t).act g f f'⟩

theorem lift_adjoint_closed {X : CxData A3.fam3.amb3} {s : ℕ} (hok : A3.fam3.Ok3 s)
    (hH : ∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) (hK : X.KFormL)
    (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) : X.AdjClosedL := by
  intro j t i
  rcases i with (p | k) | g
  · obtain ⟨p', hp'⟩ := (hH j t).1.adj p
    exact ⟨Sum.inl (Sum.inl p'), X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inl (Sum.inl p))
      (Sum.inl (Sum.inl p')) fun f f' => hp' f f'⟩
  · obtain ⟨k', hk'⟩ := (hH j t).2.adj k
    exact ⟨Sum.inl (Sum.inr k'), X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inl (Sum.inr k))
      (Sum.inl (Sum.inr k')) fun f f' => hk' f f'⟩
  · exact ⟨Sum.inr g⁻¹, X.opLC_adjoint hK (cvOf3 A3 P0 ψ0 P1 ψ1) hJ j t (Sum.inr g) (Sum.inr g⁻¹)
      fun f f' => csum_act_inv (hok.ok2.lifts j t).act g f f'⟩

end Concrete3

section Equiv3

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}

theorem coordinates_mem_subspace {B : BlockDat K G Pl0} (ℓ : Lvl K G) (Z : Submodule K B.S.Forms) (y : Fin (B.dZ ℓ Z) → K) :
    B.toF ℓ Z y ∈ Z := by
  exact toF_mem_Z ℓ Z y

theorem part_iff_rows3 (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) (p : A3.fam3.base3.Ix)
    (ℓ : Lvl K G) (y : Fin ((A3.fam3.F.R A3.fam3.F.μ0).dZ ℓ (X.Z A3.fam3.F.μ0)) → K) :
    y ∈ (A3.fam3.RI A3.fam3.F.μ0).part3 ℓ (X.Z A3.fam3.F.μ0) p.1 ↔
      X.Θ A3.fam3.F.μ0 (X.jR A3.fam3.F.μ0 ((A3.fam3.F.R A3.fam3.F.μ0).toF ℓ (X.Z A3.fam3.F.μ0) y)) ∈ X.EEp p := by
  have : FiniteDimensional K (A3.fam3.F.R A3.fam3.F.μ0).S.Forms := Module.Finite.of_basis (A3.fam3.F.R A3.fam3.F.μ0).S.basis
  rw [InertDat3.inert_part_eq_comap, Submodule.mem_comap, InertDat3.inertTypeEigenspaceSum, hH.parts p]
  exact mem_eigSum_iff_map ((X.Θ A3.fam3.F.μ0).comp (X.jR A3.fam3.F.μ0)) (hOk.what₂ _).comm
    (InertDat3.splitOver_opAll _ (hOk.ok2.what₂ _) (hOk.what₂ _)) hH.comm
    (fun i v => by
      show X.Θ _ (X.jR _ (A3.fam3.amb3.opR _ (Sum.inl i) v)) = _
      rw [X.jR_opR hR, hH.intw]; rfl)
    (DefFam3.stable3_rows hst A3.fam3.F.μ0) (fun z hz h0 => X.theta_jR_inj hR _ z hz h0) _ (coordinates_mem_subspace ℓ _ y)

theorem part_iff_lifts3 (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) (j : Fin m)
    (p : A3.fam3.base3.Ix) (ℓ : Lvl K G) (y : Fin ((A3.fam3.F.L j A3.fam3.F.μ0).dZ ℓ (X.Zl j A3.fam3.F.μ0)) → K) :
    y ∈ (A3.fam3.LI j A3.fam3.F.μ0).part3 ℓ (X.Zl j A3.fam3.F.μ0) (A3.fam3.tr3 j p.1) ↔
      X.θ' j A3.fam3.F.μ0 (X.jL j A3.fam3.F.μ0 ((A3.fam3.F.L j A3.fam3.F.μ0).toF ℓ (X.Zl j A3.fam3.F.μ0) y)) ∈ X.Wp j p := by
  have : FiniteDimensional K (A3.fam3.F.L j A3.fam3.F.μ0).S.Forms := Module.Finite.of_basis (A3.fam3.F.L j A3.fam3.F.μ0).S.basis
  rw [InertDat3.inert_part_eq_comap, Submodule.mem_comap, InertDat3.inertTypeEigenspaceSum, hH.parts j p]
  exact mem_eigSum_iff_map ((X.θ' j A3.fam3.F.μ0).comp (X.jL j A3.fam3.F.μ0)) (hOk.lifts _ _).comm
    (InertDat3.splitOver_opAll _ (hOk.ok2.lifts _ _) (hOk.lifts _ _))
    (hH.comm j)
    (fun i v => by
      show X.θ' _ _ (X.jL _ _ (A3.fam3.amb3.opL _ _ (Sum.inl i) v)) = _
      rw [X.jL_opL hL, hH.intw]; rfl)
    (DefFam3.stable3_lifts hst j A3.fam3.F.μ0) (fun z hz h0 => X.theta_jL_inj hL j _ z hz h0) _ (coordinates_mem_subspace ℓ _ y)

variable (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs))
  (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)

theorem definite_equivariance_of_primitive (hR : X.KFormR) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) (b : Bool) :
    X.H3 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro p x
  rw [CxData.iC_cpt_eq]
  cases b
  · exact part_iff_rows3 hR hst hOk hH p (A3.fam3.F.lvl P0 ψ0) x
  · exact part_iff_rows3 hR hst hOk hH p (A3.fam3.F.lvl P1 ψ1) x

theorem lift_equivariance_of_primitive (hL : X.KFormL) (hst : X.zs.Stable) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) (b : Bool) :
    X.H3W (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  intro j p x
  rw [CxData.tC_cpt_eq]
  cases b
  · exact part_iff_lifts3 hL hst hOk hH j p (A3.fam3.F.lvlA P0 ψ0) x
  · exact part_iff_lifts3 hL hst hOk hH j p (A3.fam3.F.lvlA P1 ψ1) x

end Equiv3

end Formalism.IndefR.Cx
end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.ConjLemmas
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.FrobeniusOrbits

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem emb_mul' (g g' : D.R.GG) (x : D.host.E) :
    D.host.emb (g * g') x = D.host.emb g (D.host.sigmaOf g' x) := by
  simp only [Host.emb, Host.sigmaOf, map_mul, RingHom.comp_apply]
  rfl

theorem conj_comp_emb (g : D.R.GG) :
    (starRingEnd ℂ).comp (D.host.emb g) = D.host.emb (g * D.R.cc) := by
  ext x
  rw [RingHom.comp_apply, emb_mul', ← D.host.conjE_apply (D.host.emb g)]
  rfl

theorem cc_mul_cc : D.R.cc * D.R.cc = 1 := by
  simp [Formalism.HC.Frame.cc, c0, Prod.ext_iff]

theorem ArchLab.emb_eq (A : ArchLab D) (τ : D.what₂.Tau) :
    A.emb τ = D.host.emb ((D.eTau (A.perm τ)).1 * (if A.side then 1 else D.R.cc)) := by
  rcases A with ⟨p, s⟩
  cases s
  · simp [ArchLab.emb, tauE, conj_comp_emb]
  · simp [ArchLab.emb, tauE]

theorem emb_injective : Function.Injective (D.host.emb) := (factEmb D.R D.host).1.1

theorem snd_side (b : Bool) : ((if b then 1 else D.R.cc : D.R.GG)).1.2 = if b then 1 else -1 := by
  cases b <;> rfl

theorem labExists : LabExists D := by
  intro σ
  obtain ⟨γ, hγ⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  have hlab : ∀ τ, labE σ τ = D.host.emb (γ * (D.eTau τ).1) := by
    intro τ
    ext x
    rw [emb_mul', hγ]
    rfl
  by_cases hγP : γ ∈ D.R.Psi
  · let f : D.what₂.Tau → D.what₂.Tau := fun τ => D.eTau.symm ⟨γ * (D.eTau τ).1, mul_mem hγP (D.eTau τ).2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e1 := congrArg (fun x => (D.eTau x).1) hab
      simp only [f, Equiv.apply_symm_apply] at e1
      exact D.eTau.injective (Subtype.ext (mul_left_cancel e1))
    refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), true⟩, fun τ => ?_⟩
    rw [hlab τ]
    simp [ArchLab.emb, tauE, f]
  · have hnot : ∀ τ, γ * (D.eTau τ).1 ∉ D.R.Psi := by
      intro τ hm
      apply hγP
      have h1 : (γ * (D.eTau τ).1).1.2 = 1 := hm
      have h2 : (D.eTau τ).1.1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
      show γ.1.2 = 1
      simpa [Prod.fst_mul, Prod.snd_mul, h2] using h1
    have hmem : ∀ τ, γ * (D.eTau τ).1 * D.R.cc ∈ D.R.Psi := by
      intro τ
      have h1 := hnot τ
      rw [Formalism.HC.Frame.mem_Psi_iff] at h1 ⊢
      show (γ * (D.eTau τ).1).1.2 * (-1) = 1
      rcases Int.units_eq_one_or (γ * (D.eTau τ).1).1.2 with h | h
      · exact absurd h h1
      · rw [h]; rfl
    let f : D.what₂.Tau → D.what₂.Tau := fun τ => D.eTau.symm ⟨γ * (D.eTau τ).1 * D.R.cc, hmem τ⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e1 := congrArg (fun x => (D.eTau x).1) hab
      simp only [f, Equiv.apply_symm_apply] at e1
      exact D.eTau.injective (Subtype.ext (mul_left_cancel (mul_right_cancel e1)))
    refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), false⟩, fun τ => ?_⟩
    rw [hlab τ, ArchLab.emb_eq]
    simp only [Equiv.ofBijective_apply, f, Equiv.apply_symm_apply, Bool.false_eq_true, if_false]
    rw [mul_assoc (γ * (D.eTau τ).1), cc_mul_cc, mul_one]

end Formalism.IndefR.Conj

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PHeisThC
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC Filter Topology
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

theorem eq_one_of_re_pow_gt (u : ℂ) (hu : ‖u‖ = 1) (h : ∀ n : ℕ, 1 / 2 < (u ^ n).re) : u = 1 := by
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖u - 1‖)
  have h1 : ‖u ^ N - 1‖ ≤ 2 := by
    calc ‖u ^ N - 1‖ ≤ ‖u ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hu]; norm_num
  have h2 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, u ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    calc (N : ℝ) / 2 = ∑ _i ∈ Finset.range N, (1 / 2 : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => (h i).le
  have h3 : (N : ℝ) / 2 * ‖u - 1‖ ≤ 2 := by
    calc (N : ℝ) / 2 * ‖u - 1‖ ≤ ‖∑ i ∈ Finset.range N, u ^ i‖ * ‖u - 1‖ :=
          mul_le_mul_of_nonneg_right h2 hpos.le
      _ = ‖u ^ N - 1‖ := by rw [← norm_mul, geom_sum_mul]
      _ ≤ 2 := h1
  have h4 : 4 / ‖u - 1‖ * ‖u - 1‖ = 4 := div_mul_cancel₀ _ hpos.ne'
  nlinarith [mul_lt_mul_of_pos_right hN hpos]

theorem psiOpen : PsiOpenP := by
  intro F _ _ ψ hψ
  obtain ⟨hcont, hnorm, -, -⟩ := hψ
  let g : Af F → ℂ := fun y => ψ (pairA F 0 y)
  have hp : Continuous (pairA F 0) := by
    unfold pairA; exact continuous_const.prodMk continuous_id
  have hg : Continuous g := hcont.comp hp
  have gzero : g 0 = 1 := by
    show ψ (pairA F 0 0) = 1
    have e : pairA F 0 0 = 0 := rfl
    rw [e, AddChar.map_zero_eq_one]
  have gadd : ∀ a b, g (a + b) = g a * g b := by
    intro a b
    show ψ (pairA F 0 (a + b)) = ψ (pairA F 0 a) * ψ (pairA F 0 b)
    rw [← AddChar.map_add_eq_mul]
    congr 1
    unfold pairA
    show ((0 : Ainf F), a + b) = ((0 + 0 : Ainf F), a + b)
    rw [add_zero]
  have gnsmul : ∀ (n : ℕ) a, g (n • a) = g a ^ n := by
    intro n a
    induction n with
    | zero => simp [gzero]
    | succ n ih => rw [succ_nsmul, gadd, ih, pow_succ]
  let G : AddSubgroup (Af F) :=
    { carrier := {y | ∀ z ∈ Ohat F, g (z * y) = 1}
      zero_mem' := by
        intro z _
        rw [mul_zero]; exact gzero
      add_mem' := by
        intro a b ha hb z hz
        rw [mul_add, gadd, ha z hz, hb z hz, one_mul]
      neg_mem' := by
        intro a ha z hz
        have h1 := gadd (z * -a) (z * a)
        rw [← mul_add, neg_add_cancel, mul_zero, gzero, ha z hz, mul_one] at h1
        exact h1.symm }
  refine ⟨G, ?_, ?_, ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds G (g := 0) ?_
    have key : ∀ᶠ d in 𝓝 (0 : Af F), ∀ z ∈ Ohat F, 1 / 2 < (g (z * d)).re := by
      refine (isCompact_Ohat F).eventually_forall_of_forall_eventually fun z _ => ?_
      have hc : Continuous fun p : Af F × Af F => (g (p.2 * p.1)).re :=
        Complex.continuous_re.comp (hg.comp (continuous_snd.mul continuous_fst))
      have h0 : 1 / 2 < (g (z * 0)).re := by rw [mul_zero, gzero]; norm_num
      exact (isOpen_lt continuous_const hc).mem_nhds h0
    refine Filter.mem_of_superset key fun d hd z hz => ?_
    apply eq_one_of_re_pow_gt _ (hnorm _)
    intro n
    have hnz : n • z ∈ Ohat F :=
      SetLike.mem_coe.mpr (nsmul_mem (SetLike.mem_coe.mp hz) n)
    have := hd _ hnz
    rwa [smul_mul_assoc, gnsmul] at this
  · intro y hy z hz w hw
    show g (w * (z * y)) = 1
    rw [← mul_assoc]
    exact hy _ (SetLike.mem_coe.mpr (mul_mem (SetLike.mem_coe.mp hw) (SetLike.mem_coe.mp hz)))
  · intro y hy
    have := hy 1 (SetLike.mem_coe.mpr (one_mem _))
    rwa [one_mul] at this

theorem psiSmooth : PsiSmoothP := by
  intro D ψ hψ k s hs
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := hψ
  have h := hall θ hθ
  have hc : ∀ ρ, ContDiff ℝ ∞ fun t : Fin k → ℝ => θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E)) := by
    intro ρ
    let L : (Fin k → ℝ) →+ ℂ :=
      { toFun := fun t => θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E))
        map_zero' := by simp
        map_add' := fun a b => by simp [map_add (f := _), TensorProduct.add_tmul] }
    have hL : Continuous L := (hθ ρ).2.comp hs
    exact (L.toRealLinearMap hL).contDiff
  have e : (fun t => ψ (pairA D.host.F (s t) 0)) = fun t =>
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) *
        ∑ ρ, θ ρ (s t ⊗ₜ[D.host.F] (1 : D.host.E))) := by
    funext t; exact h (s t)
  rw [e]
  exact (contDiff_const.mul (ContDiff.sum fun ρ _ => hc ρ)).cexp

end Formalism.IndefR.PHeisTh

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.InBlock
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.CutPassage3S
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

def CutPassage3S : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (G : Type) [Group G] [Fintype G]
    (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 K G Pl0 I0 Ty T m) (s : ℕ) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* Kˣ) (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (X : CxData A3.fam3.amb3) (C CH : ℝ)
    (gE : Representation ℂ G X.EE) (S : Type) [Fintype S] (Ws : S → Type) [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ),
    A3.fam3.Ok3 s → A3.fam3.TypesSep3 →
    X.zs.Stable → X.zs.InBlock → X.H4pos →
    (A3.side3 P0 ψ0 X.zs).Pos → (A3.side3 P1 ψ1 X.zs).Pos →
    (∀ b, X.H2 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b) → (∀ b, X.RATmu (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b) →
    PrincipalLevelBijectivity A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) →
    X.RATmu (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false →
    (∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ) → GEquiv3 A3 X gE →
    X.nP false = (Nat.card P0 : ℝ) → X.nP true = (Nat.card P1 : ℝ) →
    Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ A3.A.fam.X → Formalism.IndefR.IndefiniteEpsilonOperator.M1 τ ⟨P0, ψ0⟩ → 0 < nbar →
    NearConstantMultiplicities τ ⟨P1, ψ1⟩ nbar ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).de →
    ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH).la = Formalism.IndefR.IndefiniteEpsilonOperator.la G →
      Passage ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Z.num C CH)
        (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false) (X.data (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) true)

end Formalism.IndefR.CxPass
end
end

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

structure In3 (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type)
    (m : ℕ) where
  A3 : FamIn3 K G Pl0 I0 Ty T m
  P0 : Subgroup G
  ψ0 : P0 →* Kˣ
  P1 : Subgroup G
  ψ1 : P1 →* Kˣ
  Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)
  Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)
  Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3
  X : CxData A3.fam3.amb3
  gE : Representation ℂ G X.EE

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

abbrev A : FamIn K G Pl0 T m := I.A3.A

abbrev cr : Crd I.A3.fam3.amb3 (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

abbrev cg : Crd I.A3.fam3.amb3 (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc) := crdOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc

def lvP : Bool → Subgroup G := fun b => cond b I.P1 I.P0

def lvψ : ∀ b, I.lvP b →* Kˣ
  | false => I.ψ0
  | true => I.ψ1

abbrev Sb (b : Bool) := I.X.data I.cr b

abbrev Sg := (prin I.X).data I.cg false

abbrev iCg := I.X.iC I.cg false I.A3.fam3.base3.μ0

def Jm (b : Bool) : Matrix (Fin I.Sg.D) (Fin (I.Sb b).D) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat I.iCg (I.X.iC I.cr b I.A3.fam3.base3.μ0))

def ρf (g : G) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat I.iCg ((I.gE g).comp I.iCg))

def Jt (b : Bool) (t : I.A3.fam3.base3.Tup) :
    Matrix (Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).dQ t)) K :=
  kMat I.A3.fam3.base3.v0.embedding (relMat (I.X.iC I.cg false t) (I.X.iC I.cr b t))


open Classical in
def epM (P : Subgroup G) (ψ : P →* Kˣ) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  haveI : Fintype P := Fintype.ofFinite P
  ((Nat.card P : K)⁻¹) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)

def eMat {W : Type} [AddCommGroup W] [Module K W] (τ : Representation K G W) : Matrix (Fin I.Sg.D) (Fin I.Sg.D) K :=
  (Formalism.IndefR.TransferLatticeStatement.charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, Formalism.IndefR.TransferLatticeStatement.charOf τ x⁻¹ • I.ρf x

abbrev LA {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) (nbar : ℝ) : LevelAmb K (I.Sb false).D (I.Sb true).D where
  Dg := I.Sg.D
  Xg := I.Sg.XE
  Rg := I.Sg.RR
  ep0 := I.epM I.P0 I.ψ0
  ep1 := I.epM I.P1 I.ψ1
  S := S
  fS := inferInstance
  es s := I.eMat (τ s)
  nS s := Formalism.IndefR.IndefiniteEpsilonOperator.nOf (τ s) ⟨I.P1, I.ψ1⟩
  nbar := nbar
  G := Fintype.card G
  h0 := Nat.card I.P0
  h1 := Nat.card I.P1
  ι0 := I.Jm false
  ι1 := I.Jm true

structure Hyp (s : ℕ) : Prop where
  ok : I.A3.fam3.Ok3 s
  sep : I.A3.fam3.TypesSep3
  stable : I.X.zs.Stable
  inBlock : I.X.zs.InBlock
  h4pos : I.X.H4pos
  pos0 : (I.A3.side3 I.P0 I.ψ0 I.X.zs).Pos
  pos1 : (I.A3.side3 I.P1 I.ψ1 I.X.zs).Pos
  h2 : ∀ b, I.X.H2 I.cr b
  ratMu : ∀ b, I.X.RATmu I.cr b
  h2g : PrincipalLevelBijectivity I.A3 I.X (P1 := I.P1) (ψ1 := I.ψ1) (Dc := I.Dc) (Sp := I.Sp) (Zsc := I.Zsc)
  ratMug : I.X.RATmu I.cg false
  gunit : ∀ (g : G) (x y : I.X.EE), ⟪I.gE g x, I.gE g y⟫_ℂ = ⟪x, y⟫_ℂ
  gequiv : GEquiv3 I.A3 I.X I.gE
  np0 : I.X.nP false = (Nat.card I.P0 : ℝ)
  np1 : I.X.nP true = (Nat.card I.P1 : ℝ)

def PRho : Prop :=
  ∀ s, I.Hyp s → I.ρf 1 = 1 ∧ (∀ g h, I.ρf (g * h) = I.ρf g * I.ρf h) ∧
    ∀ g (x : Fin I.Sg.D → K), I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.ρf g *ᵥ x)) =
      I.gE g (I.iCg (cpt I.A3.fam3.base3.v0.embedding x))

def PJ : Prop :=
  ∀ s, I.Hyp s → ∀ b, (∀ x : Fin (I.Sb b).D → K, I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.Jm b *ᵥ x)) =
      I.X.iC I.cr b I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) ∧ Function.Injective (I.Jm b).mulVec

def PJt : Prop :=
  ∀ s, I.Hyp s → ∀ b t,
    (∀ x, I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding (I.Jt b t *ᵥ x)) =
      I.X.iC I.cr b t (cpt I.A3.fam3.base3.v0.embedding x)) ∧
    (∀ x, I.cg.toR I.X.zs false t (I.Jt b t *ᵥ x) = I.cr.toR I.X.zs b t x) ∧
    ∀ x, I.Jm b *ᵥ (I.X.rowMat I.cr b t *ᵥ x) = I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ x)

def PRange : Prop :=
  ∀ s, I.Hyp s → ∀ b, LinearMap.range (I.Jm b).mulVecLin = LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin

def PMet : Prop :=
  ∀ s, I.Hyp s → ∀ b v (x y : Fin (I.Sb b).D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (I.Sb b).D)) (I.Sb b).XE v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt (Nat.card (I.lvP b))) I.Sg.XE) v
        (I.Jm b *ᵥ x) (I.Jm b *ᵥ y)

def PFrames : Prop := ∀ s, I.Hyp s → ∀ v, IsUnit (I.Sg.XE v).det

def PUni : Prop :=
  ∀ s, I.Hyp s → ∀ v (g : G) (x y : Fin I.Sg.D → K),
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v (I.ρf g *ᵥ x) (I.ρf g *ᵥ y) =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin I.Sg.D)) I.Sg.XE v x y

def PLat : Prop := ∀ s, I.Hyp s → Submodule.IsLattice K I.Sg.RR

def PGLat : Prop := ∀ s, I.Hyp s → ∀ (g : G), ∀ x ∈ I.Sg.RR, I.ρf g *ᵥ x ∈ I.Sg.RR

def PSand : Prop :=
  ∀ s, I.Hyp s → ∀ b,
    (∀ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x ∈ I.Sg.RR) ∧
    ∀ y ∈ I.Sg.RR, y ∈ LinearMap.range (I.epM (I.lvP b) (I.lvψ b)).mulVecLin →
      ∃ x ∈ (I.Sb b).RR, I.Jm b *ᵥ x = ((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • y

def PGood {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s)) : Prop :=
  ∀ s, I.Hyp s → Formalism.IndefR.TransferLatticeStatement.IsGood τ → CharsX τ I.A.fam.X → ∑ t, I.eMat (τ t) = 1

end In3

end Formalism.IndefR.CxPass
end
end
