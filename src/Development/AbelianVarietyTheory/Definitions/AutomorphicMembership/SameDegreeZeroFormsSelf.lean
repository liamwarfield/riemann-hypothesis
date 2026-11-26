module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SPack (D : D7) (F : ∀ u, Forms0 D u) where
  X : HidaSetting D
  hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I
  Y : Formalism.L2.SG.Full.Full X
  fin : FinX Y
  ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ
  measTie : X.MeasTie hb
  ψ_char : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ
  ψ_std : Formalism.L2.SG.LocVol.IsStdChar ψ
  measCompat : Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ
  locCompat : ∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w
  tr : ∀ u, Transport X u (F u)
  into : ∀ u, ColDictInto X (tr u) Y.hK
  bij : ∀ u, ColDictBij X (tr u) Y.hK
  lev : ∀ u, LevelMatch X (tr u) Y.hK
  isom : ∀ u, ColDictIsom X (tr u) Y.hK (Y.cs u) (fin.shInj u)
  inst : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D
  G : GoodOp X

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

structure SRest {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) where
  hI : SIso D.s (sOf P.fin)
  autTie : Formalism.MainNotions.S.AutTie D P.X.B P.X.pl
  colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
    colDict P.X (P.tr u) P.Y.hK (P.into u) (P.bij u) (hI.eCu u x) = D.s_Cu u x
  j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G
  rowPin : ∀ x : D.what₂.EE, hI.eHH (D.sEE x) = conjHH P.X P.G (j x)
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

def SRest.toSTies {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) : Formalism.L2.SG.SpectralTiesReal.STies D where
  X := P.X
  hb := P.hb
  Y := P.Y
  hI := fun _ => S.hI
  ψ := P.ψ
  autTie := S.autTie
  measTie := P.measTie
  ψ_char := P.ψ_char
  ψ_std := P.ψ_std
  measCompat := P.measCompat
  locCompat := P.locCompat

theorem SRest.rowTie {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) : RowDictTie P.X P.G S.hI.eHH :=
  ⟨S.j, S.rowPin⟩

def SPack.toNew {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
    (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) : SNew D where
  s := sOf P.fin
  s_HH := hD
  s_Cu := fun u => colDictT P.X (P.tr u) P.Y.hK (P.fin.shInj u) (P.into u) (P.bij u)
  s_PlF := Equiv.refl _
  s_Cu_isom := fun u x y => P.isom u x y
  sEE := (conjHH P.X P.G).comp j.toLinearIsometry

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Level

theorem mult_anti {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ}
    (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun _ hX => ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

theorem principal_le_level {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ)
    (k : GA D V) (hk : k ∈ levS V β (flag1L L)) :
    k ∈ levS V β (withP L P) ∧ levChi V β (withP L P) k = levChi V β (flag1L L) k := by
  have h1 : rTup β L (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
  have h2 : rTup β L (finE V k) ∈ P.H := h1 ▸ P.H.one_mem
  refine ⟨⟨hk.1, hk.2.1, h2⟩, ?_⟩
  unfold levChi
  rw [levFn_withP, levFn_flag1, h1, extendOne_of_mem _ P.H.one_mem]
  exact congrArg Units.val ((congrArg (· * _) (map_one P.chi)).trans (one_mul _))

variable (R : RealDat D A Ks)

def multAt (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : Submodule ℂ (MMap (R.MY j)) :=
  Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P)) (levChi _ (R.βY j) (R.datYt t j P))

def toMM (t : T) (j : ℕ) : R.CC t j →ₗ[ℂ] MMap (R.MY j) :=
  (PiTensorProduct.lift.symm : (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ≃ₗ[ℂ] MMap (R.MY j)).toLinearMap ∘ₗ (R.CC t j).subtype

def lvlPart (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : Submodule ℂ (R.CC t j) := (multAt R P t j).comap (toMM R t j)

def ipCC (t : T) (j : ℕ) (U U' : R.CC t j) : ℂ := ipM (R.MY j) (R.νY t j) (R.fdY t j) (toMM R t j U) (toMM R t j U')

def topLift (t : T) : (R.HX t).H →ₗ[ℂ] R.CC t (D.R.m - 1) := R.ioX t ∘ₗ (R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict

def botLift (t : T) : R.CC t 1 →ₗ[ℂ] MMap (R.MY 0) := postOn (R.MY 0) R.e0 ∘ₗ toMM R t 0 ∘ₗ R.ioY t 0

theorem toMM_injective (t : T) (j : ℕ) : Function.Injective (toMM R t j) :=
  (PiTensorProduct.lift.symm : (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ≃ₗ[ℂ] MMap (R.MY j)).injective.comp Subtype.val_injective

theorem range_toMM (t : T) (j : ℕ) : LinearMap.range (toMM R t j) = multAt R R.triv t j := by
  ext X
  constructor
  · rintro ⟨U, rfl⟩
    exact (mem_multT R.θ (R.MY j) _ _ _).1 U.2
  · intro hX
    exact ⟨⟨PiTensorProduct.lift X, Submodule.mem_map_of_mem hX⟩, PiTensorProduct.lift.symm_apply_apply X⟩

theorem multAt_le (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : multAt R P t j ≤ multAt R R.triv t j :=
  mult_anti _ _ (principal_le_level (R.βY j) (R.datYt t j R.triv) P)

theorem multAt_zero (P : LevelP R.Pg D.R.r ℂ) (t : T) :
    multAt R P t 0 = Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  have e := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) P R.chi (R.xiR t)
  have e1 : levG (Yc D 0) (R.βY 0) (R.datYt t 0 P) = levG (Yc D 0) (R.βY 0) (R.dat0 P) := e.1
  have e2 : ∀ k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 P),
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 P) k = levChi (Yc D 0) (R.βY 0) (R.dat0 P) k := e.2
  exact le_antisymm (mult_anti _ _ fun k hk => ⟨e1.ge hk, e2 k (e1.ge hk)⟩) (mult_anti _ _ fun k hk => ⟨e1.le hk, (e2 k hk).symm⟩)

theorem EEat_le_triv (P : LevelP R.Pg D.R.r ℂ) : R.EEat P ≤ R.EEat R.triv :=
  inf_le_inf_right _ (mult_anti _ _ (principal_le_level (R.βY 0) (R.dat0 R.triv) P))

end Level

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem pred_m_add_one (D : D7) : D.R.m - 1 + 1 = D.R.m := by have := D.R.two_le_m; omega

def famCast (Sp : ℕ → Type) [∀ j, NormedAddCommGroup (Sp j)] [∀ j, InnerProductSpace ℂ (Sp j)] {i j : ℕ} (h : i = j) :
    Sp i ≃ₗᵢ[ℂ] Sp j := by
  subst h; exact LinearIsometryEquiv.refl ℂ _

def multCast (μ : D.what₂.Tup) {i j : ℕ} (h : i = j) : S.Mult μ i ≃ₗᵢ[ℂ] S.Mult μ j := famCast (S.Mult μ) h

def topEquiv (μ : D.what₂.Tup) : S.Mult μ (D.R.m - 1 + 1) ≃ₗᵢ[ℂ] S.Amb μ := (multCast S μ (pred_m_add_one D)).trans (S.multTop μ)

end Side

variable {R : RealDat D A Ks} {F : Face D A} {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE]
  [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE}


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure MultTie (Y : SideTie R F tup b S) where

  eM : ∀ t j, S.Mult (tup t) j →ₗ[ℂ] R.CC t j

  eM_zero : ∀ t x, toMM R t 0 (eM t 0 x) = R.HE.e (Y.eE (S.multZero (tup t) x))

  eM_range : ∀ t j, 0 < j → j < D.R.m → LinearMap.range (eM t j) = lvlPart R (R.levR F b) t j

  eM_inner : ∀ t j, 0 < j → j < D.R.m → ∀ x y, ipCC R t j (eM t j x) (eM t j y) = ((RealDat.nP F b : ℝ) : ℂ) * ⟪x, y⟫_ℂ

  io_zero : ∀ t x, toMM R t 0 (eM t 0 (S.io (tup t) 0 x)) = botLift R t (eM t 1 x)

  io_mid : ∀ t j, 0 < j → j + 1 < D.R.m → ∀ x, eM t j (S.io (tup t) j x) = R.ioY t j (eM t (j + 1) x)

  io_top : ∀ t x, eM t (D.R.m - 1) (S.io (tup t) (D.R.m - 1) x) = topLift R t (Y.eA t (topEquiv S (tup t) x))

section Inhabitant

theorem exists_factor {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (g : Y →ₗ[ℂ] Z) (hg : Function.Injective g) (f : X →ₗ[ℂ] Z) (hf : ∀ x, f x ∈ LinearMap.range g) :
    ∃ h : X →ₗ[ℂ] Y, ∀ x, g (h x) = f x :=
  ⟨(LinearEquiv.ofInjective g hg).symm.toLinearMap ∘ₗ f.codRestrict _ hf, fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective g hg).apply_symm_apply ⟨f x, hf x⟩)⟩

theorem haar_chain (hY : R.models_νY) (hY' : R.models_νY') (t : T) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h1 : j + 1 < D.R.m
  · exact ⟨(hY t j h1).1.1, (hY t j h1).2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨(hY' t).1.1, (hY' t).2⟩


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure HChain (m : ℕ) (E B : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] where

  Sp : ℕ → Type
  [nSp : ∀ j, NormedAddCommGroup (Sp j)]
  [iSp : ∀ j, InnerProductSpace ℂ (Sp j)]
  [fSp : ∀ j, FiniteDimensional ℂ (Sp j)]

  bot : Sp 0 ≃ₗᵢ[ℂ] E

  top : Sp m ≃ₗᵢ[ℂ] B

  io : ∀ j, Sp (j + 1) →ₗ[ℂ] Sp j

attribute [instance] HChain.nSp HChain.iSp HChain.fSp


end Inhabitant

def MultTied {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0) : Prop := Function.Surjective Y.tup ∧ Nonempty (MultTie Y.sharp)

theorem isMultiplicityInner_mul_inner {V : HSp D} {Sp : D.what₂.Tau → SPar} {M : DSModel V Sp} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) {d : ℂ} (hd : d ≠ 0)
    (h : ∀ x y, ipM M μ 𝓕 (e x) (e y) = d * ⟪x, y⟫_ℂ) (x y : H) : IsMultIP M μ 𝓕 (e x) (e y) (d * ⟪x, y⟫_ℂ) := by
  have key : ∀ x y : H, ⟪x, y⟫_ℂ ≠ 0 → IsMultIP M μ 𝓕 (e x) (e y) (d * ⟪x, y⟫_ℂ) := fun x y hxy => by
    rw [← h]
    refine ipM_spec M μ 𝓕 _ _ ?_
    by_contra hn
    exact mul_ne_zero hd hxy ((h x y).symm.trans (by rw [ipM, dite_eq_right hn]))
  by_cases hxy : ⟪x, y⟫_ℂ = 0
  swap
  · exact key x y hxy
  by_cases hx : x = 0
  · subst hx
    intro v v'
    simp
  have hxx : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx
  have h₁ := key x x hxx
  have h₂ := key x (x + y) (by rwa [inner_add_right, hxy, add_zero])
  intro v v'
  have hf : (fun g => star (e x v g) * e y v' g) = fun g => star (e x v g) * e (x + y) v' g - star (e x v g) * e x v' g := by
    funext g
    simp only [map_add (f := _), add_apply, Pi.add_apply]
    ring
  rw [hf]
  refine ⟨(h₂ v v').1.sub (h₁ v v').1, ?_⟩
  rw [integral_sub (h₂ v v').1 (h₁ v v').1, (h₂ v v').2, (h₁ v v').2, inner_add_right]
  ring

namespace MultTie

variable {Y : SideTie R F tup b S} (M : MultTie Y)


end MultTie

namespace MultTied

variable {X0 : BaseLevelRowSide D} {Y : RowsTie R F X0}

end MultTied

end GlobalTheory.Mem.Th

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.FrobeniusOrbits GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

structure Obj2 (D : D7) : Type 1 where

  gatT : GatTies D

  th : ThetaX D

  cmp : LatCmp D

  tw : TwForms D

  Gy : G.LatInst D

  errX : ErrX D

  nch : NChoice D

  xd : ThData D

  lev : LevelData D

  X : DivX D

  p0 : BaseLevelRowSide D

  ker : ∀ u w (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    LocalToGlobal₂ D gatT cmp tw u w h (Gy.Ch u w h)

  amb : AmbForm D (RowSide.sharp D)

  amb0 : AmbForm D p0.s

  gauge : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig

def layObj {D : D7} (Y : Lay D) : Obj2 D := { Y with }

def Obj2.tr {D : D7} (O : Obj2 D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : Obj2 (setDiv D N h) where
  gatT := gatTr N h O.gatT
  th := thTr N h O.th
  cmp := cmpTr N h O.cmp
  tw := twTr N h O.tw
  Gy := latTr N h O.Gy
  errX := errTr N h O.errX
  nch := nchTr N h O.nch
  xd := xdTr N h O.xd
  lev := O.lev
  X := divTr N h O.X
  p0 := ⟨sideTr N h O.p0.s⟩
  ker := fun u w g => { O.ker u w g with }
  amb := { O.amb with }
  amb0 := { O.amb0 with }
  gauge := O.gauge

def pointPropertyOfObjects (QO : ∀ D : D7, Obj2 D → Prop) : PtProp := fun D _ gatT _ Gy _ X _ ex =>
  QO D { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
         lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def allDiv (QO : ∀ D : D7, Obj2 D → Prop) (D : D7) (Y : Lay D) : Prop := ∀ N h, QO (setDiv D N h) ((layObj Y).tr N h)

def extraObj {D : D7} {L : SizeData₂ D} {gatT : GatTies D} {Gx : G.Inst D L} {Gy : G.LatInst D} {K : G.Consts} {X : DivX D}
    {cX : ExtraC} (ex : Extra D L gatT Gx Gy K X cX) : Obj2 D :=
  { gatT := gatT, th := ex.th, cmp := ex.cmp, tw := ex.tw, Gy := Gy, errX := ex.errX, nch := ex.nch, xd := ex.xd,
    lev := ex.lev, X := X, p0 := ex.p0, ker := ex.ker, amb := ex.amb, amb0 := ex.amb0, gauge := ex.gauge }

def ofObj {D : D7} (O : Obj D) : Obj2 D := extraObj O.ex

def pointObj {C : FC} (p : Pt C) : Obj2 p.D := extraObj p.xa.ex

theorem ofObj_obj {C : FC} {D : D7} (Y : Lay D) (p : LedPart C Y) : ofObj (Y.obj p) = layObj Y := rfl

theorem pointObj_pt {C : FC} {D : D7} {Y : Lay D} (p : LedPart C Y) : pointObj p.pt = (layObj Y).tr (nPrime p.L) p.ht := rfl

end GlobalTheory.Mem.Top

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix

namespace GlobalTheory.GoodMetric

variable {ι : Type} {m : ι → ℕ}

abbrev EntIx (m : ι → ℕ) : Type := Σ τ, Fin (m τ) × Fin (m τ)

def evEnt {M : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)) {R : Type} [CommRing R] (A : Mat m R) :
    Matrix (Fin M) (Fin M) R :=
  P.map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2)

structure PolyRep (m : ι → ℕ) : Type where

  M : ℕ

  ent : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)
  one : ∀ (R : Type) [CommRing R], evEnt ent (1 : Mat m R) = 1
  mul : ∀ (R : Type) [CommRing R] (A B : Mat m R), evEnt ent (A * B) = evEnt ent A * evEnt ent B
  transp : ∀ (R : Type) [CommRing R] (A : Mat m R), evEnt ent (fun τ => (A τ)ᵀ) = (evEnt ent A)ᵀ

namespace PolyRep

def ev (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) : Matrix (Fin ρ.M) (Fin ρ.M) R := evEnt ρ.ent A

def lie [Fintype ι] (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) : Matrix (Fin ρ.M) (Fin ρ.M) R :=
  Matrix.of fun i j => ∑ v : EntIx m,
    aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2) (pderiv v (ρ.ent i j)) * A v.1 v.2.1 v.2.2

def proj (m : ι → ℕ) (τ : ι) : PolyRep m where
  M := m τ
  ent := Matrix.of fun i j => X ⟨τ, (i, j)⟩
  one R _ := by ext i j; simp [evEnt]
  mul R _ A B := by ext i j; simp [evEnt, Matrix.mul_apply]
  transp R _ A := by ext i j; simp [evEnt]

end PolyRep

end GlobalTheory.GoodMetric

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RedivisionStructureEq
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure New (D : D7) : Type 1 where
  Z : SNew D
  N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V
  h : D.what₂.Word → ℝ

def reD (D : D7) (Z : New D) : D7 := GlobalTheory.EX.OB.setDiv (reS D Z.Z) Z.N Z.h


set_option maxHeartbeats 4000000 in
def SameForms0LevelsAndValues {D : D7} (Z : New D) (F : ∀ u, Forms0 D u) (F' : ∀ u, Forms0 (reD D Z) u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev = (F u).cls0.lev ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY

variable {D : D7} (Z : New D)

def wd (u : D.what₂.Word) : (reD D Z).what₂.Word := u

def New.self (D : D7) : New D := ⟨SNew.self D, fun u => (D.div.Nu u).L, D.div.h⟩

def New.ofDiv (D : D7) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (h : D.what₂.Word → ℝ) : New D := ⟨SNew.self D, N, h⟩


set_option maxHeartbeats 4000000 in
def reX (X : HidaSetting D) : HidaSetting (reD D Z) := { X with }

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdPstCycRepNeTrivWD
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Pst.Test

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) (LL : FinExt l)

section Generic

variable {LL} {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK Bw.Kw) V) (x : ↥(Dpst P ρ))

theorem apply_eq_of_nilpotent {W : Type} [AddCommGroup W] [Module ℂ W] (hd : finrank ℂ W = 1) {v : W}
    (hv : v ≠ 0) (u : End ℂ W) (hu : IsNilpotent (u - 1)) : u v = v := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' v hv).mp hd ((u - 1) v)
  have hp : ∀ n : ℕ, ((u - 1) ^ n) v = c ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  have hc0 : c = 0 := by
    have := hp k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    exact pow_eq_zero_iff'.mp (this.resolve_right hv) |>.1
  rw [hc0, zero_smul, LinearMap.sub_apply, eq_comm, sub_eq_zero] at hc
  exact hc

end Generic

theorem lpDim_wdAt {a : ℕ} (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) :
    (wdAt P ι Bw h hj r).lpDim = a := by
  by_cases hr : IsPstAt P Bw r
  · obtain ⟨LL', r', -, h2, h3⟩ := wdAt_of_isPstAt ι Bw h hj hr
    rw [h3, lpDim_wdPst ι Bw h hj h2, LetterDim.finrank_wdSpace l P ι _ LL' _ _ h2]
    simp
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, lpDim_trivWD]


omit P ι in
theorem exists_induces (hw : w ∈ placesOver E l) (h : IsPlaceOver A w) :
    ∃ (LL : FinExt l) (Bw : LocBridge l E Ω (Dec (F := E) A) ↥(OL LL)), Induces Bw := by
  obtain ⟨j, L0, hj, hL⟩ := GlobalTheory.PlaceBridge.exists_locBridge l E Ω w A hw h
  obtain ⟨Bw, hB, -⟩ := hL L0 le_rfl
  exact ⟨L0, Bw, fun x => by rw [hB]; exact hj x⟩


end GlobalTheory.Pst.Test
end
end
