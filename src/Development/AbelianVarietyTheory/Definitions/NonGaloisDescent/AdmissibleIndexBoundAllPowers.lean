module

public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharFiniteOrderOfTrivialAtInfinity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.TwAll

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (Y : NExp D.R D.host D.what₂ D.LL0 N X) (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)

def admissibleIndexBoundAllPowers (N0 : X.Tw → ℕ) : Prop :=
  ∀ i : X.Tw, X.NonzeroIndexPlace i → Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' → ∀ F : RFam Y i,
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, ABHyp Y i F j b) →
    ∀ A0 : Finset (PlE D.host),
    ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
      Formalism.MainNotions.BlochKatoReduction.Gen.PsiOk i A0 Q k' (ψ' ^ a) ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partAT bkP i Q k' (ψ' ^ a) eps' ∧
      Formalism.MainNotions.BlochKatoReduction.Gen.partC N0 i Q k' (ψ' ^ a) eps' ∧ Formalism.MainNotions.BlochKatoReduction.Gen.partD i Q k' (ψ' ^ a) eps' ∧
      partAB Y i F Q k' (ψ' ^ a) eps'

def goodTwistExistsAllCoprimePowers (E : ExpDat Y) (N0 : X.Tw → ℕ) (i : X.Tw) : Prop :=
  Formalism.MainNotions.BlochKatoReduction.Gen.SetHyp bkP i → ∀ eps' : ℝ, 0 < eps' →
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, FullRk Y E i j b (SgJ Y E i j b)) →
  ∀ S : ∀ (j : ℕ) (b : Bool), Finset (Y.Dat i j b),
    (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, BasisOf Y i j b (SgJ Y E i j b) (S j b)) →
  ∀ A : Finset (PlE D.host),
  ∃ (Q : Finset (PlE D.host)) (k' : ℕ) (ψ' : X.RCG i Q →* (X.Ok i k')ˣ), ∀ a : ℤ, IsCoprime a (X.l i : ℤ) →
    GoodTw Y bkP E N0 i eps' S A Q k' (ψ' ^ a)

variable {Y} (T : NTh D.R D.host D.what₂ D.LL0 N X Y)

def TypeKept (E : ExpDat Y) : Prop := ∀ i, X.NonzeroIndexPlace i → ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b k Q
  (ψ : G D.host.E N.Om →* (X.Ok i k)ˣ), TwOK i k Q ψ → UnrG ψ → ∀ a ∈ E.Dat0 i j b,
    Y.thPsi i j b k Q ψ a ⊆ ((((Fm0 Y i j b).restrictScalars (X.O i)).baseChange (X.Ok i k) :
      Submodule (X.Ok i k) (X.Ok i k ⊗[X.O i] Y.Fm i j b)) : Set (X.Ok i k ⊗[X.O i] Y.Fm i j b))

end GlobalTheory.TwAll
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
noncomputable section

namespace GlobalTheory.LiftLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped TensorProduct

section Rec

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def LabCompat (i : N.Loc) : Prop := ∀ σ Sig, HasParamW N A i σ Sig → (N.goodRow σ ↔ goodSig N A Sig)

def AtMOfParam (i : N.Loc) : Prop :=
  ∀ x ∈ ZgoodN N A i, ∀ Sig, HasParamX N A i x Sig → ∀ σ, HasParamW N A i σ Sig → AtM N A i σ

def CharSum : Prop :=
  ∀ (w : PlE H) (a b χ : A.LP w) (s : ℝ), A.lpDim χ = 1 →
    A.lpChar (A.lpSum a b) χ = A.lpSum (A.lpChar a χ) (A.lpChar b χ) ∧
    A.lpChar (A.lpTw a s) χ = A.lpTw (A.lpChar a χ) s ∧ A.lpChar (A.lpZero w) χ = A.lpZero w

end Rec

section Exp

open Formalism.MainNotions.IntegralHeckeForms

def CommG (D : D7) : Prop :=
  ∀ (i : D.ntw.Tw), D.ntw.NonzeroIndexPlace i → ∀ (b : Bool), ∀ j ∈ Finset.Icc 1 D.R.m, ∀ g k P, HkIdx i k P →
    (D.nexp.actG i j b g).toLinearMap ∘ₗ D.nexp.hkF i j b k P = D.nexp.hkF i j b k P ∘ₗ (D.nexp.actG i j b g).toLinearMap

end Exp

end GlobalTheory.LiftLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom

namespace GlobalTheory.LamTie

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def TeichTriv (χ : Formalism.L2.Host.HChar H.E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 H.E), OverP H H.pde w ∨ OverP H H.pde' w →
    ∀ x : (w.adicCompletion H.E)ˣ, x ^ (Ideal.absNorm w.asIdeal - 1) = 1 → χ.loc w x = 1

variable {H} {χ χ' : Formalism.L2.Host.HChar H.E}

theorem isUnitAt_of_pow_eq_one {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {x : (w.adicCompletion E)ˣ}
    (hx : x ^ (Ideal.absNorm w.asIdeal - 1) = 1) : IsUnitAt w x := by
  have h1 : Ideal.absNorm w.asIdeal - 1 ≠ 0 := by have := GlobalTheory.Mem.WildChar.one_lt_absNorm w; omega
  have := congrArg (fun y : (w.adicCompletion E)ˣ => Valued.v (y : w.adicCompletion E)) hx
  simp only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] at this
  exact (pow_eq_one_iff_left h1).1 this

namespace TeichTriv

theorem of_unr (h : ∀ w, OverP H H.pde w ∨ OverP H H.pde' w → χ.UnrAt w) : TeichTriv H χ :=
  fun w hw x hx => h w hw x (isUnitAt_of_pow_eq_one hx)

end TeichTriv

end Host

namespace LamDat

variable {D : D7} (Z : LamDat D)

def Teich : Prop := ∀ a, TeichTriv D.host (Z.chi a)

variable {Z}

end LamDat

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

def IsLamTieFull (Z : LamDat D) : Prop :=
  ∀ i, X.NonzeroIndexPlace i → (∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i) ∧
    ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      (∀ lam : X.abelian₂ i, ∃ (j a : Fin D.R.m) (s : ℕ), IsLam X Z i (atSide X (X.sideL i lam) ι) lam j a s ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)) ∧
      ∀ (j a : Fin D.R.m) (s : ℕ) (b : Bool), 1 ≤ s → s ≤ BlochKatoReduction.Gen.NFun D.R + 1 →
        ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ IsLam X Z i (atSide X b ι) lam j a s ∧
          IsThOf X i (atSide X b ι) lam (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 (X.l i) j a)

variable {X} {Z : LamDat D}

theorem isLamTieFull_of_labels (J A : ∀ i, X.abelian₂ i → Fin D.R.m) (S : ∀ i, X.abelian₂ i → ℕ)
    (hS : ∀ i, X.NonzeroIndexPlace i → ∀ P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ X.S0 i)
    (hι : ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
      ∀ lam : X.abelian₂ i, IsLam X Z i (atSide X (X.sideL i lam) ι) lam (J i lam) (A i lam) (S i lam) ∧
        IsThOf X i (atSide X (X.sideL i lam) ι) lam (phi D.host) (S i lam) (Z.kap (J i lam) (A i lam) (S i lam)) (cond0 D.host Z.w0)
          (Z.lam0 (X.l i) (J i lam) (A i lam)))
    (hall : ∀ i, X.NonzeroIndexPlace i → ∀ (j a : Fin D.R.m) (s : ℕ) (b : Bool), 1 ≤ s → s ≤ BlochKatoReduction.Gen.NFun D.R + 1 →
      ∃ lam : X.abelian₂ i, X.sideL i lam = b ∧ J i lam = j ∧ A i lam = a ∧ S i lam = s) : IsLamTieFull X Z := fun i hi => by
  obtain ⟨ι, h1, h2⟩ := hι i hi
  refine ⟨hS i hi, ι, h1, fun lam => ⟨_, _, _, h2 lam⟩, fun j a s b hs hs' => ?_⟩
  obtain ⟨lam, rfl, rfl, rfl, rfl⟩ := hall i hi j a s b hs hs'
  exact ⟨lam, rfl, h2 lam⟩

namespace IsLamTieFull

end IsLamTieFull

end Record

end GlobalTheory.LamTie
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK
open scoped Formalism.Per

namespace GlobalTheory.BKReal

variable {l : ℕ} [hl : Fact l.Prime]

scoped instance algZlBdRp : Algebra ℤ_[l] (Per.BdRp l) :=
  ((GlobalTheory.MemLoc.aDp l).comp (algebraMap ℤ_[l] (Ainf l))).toAlgebra


variable (l) in
def ainfToBdRp : Ainf l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := GlobalTheory.MemLoc.aDp l
  commutes' _ := rfl


variable (l) in
def crisP : Per.Acris l →+* Per.BdRp l := (GlobalTheory.MemLoc.exists_isCrisP l).choose


variable (l) in
theorem isCrisP_crisP : GlobalTheory.MemLoc.IsCrisP (crisP l) := (GlobalTheory.MemLoc.exists_isCrisP l).choose_spec

theorem eq_crisP {j : Per.Acris l →+* Per.BdRp l} (h : GlobalTheory.MemLoc.IsCrisP j) : j = crisP l :=
  (GlobalTheory.MemLoc.crisP_unique_equivariant l _ (isCrisP_crisP l)).1 j h

theorem crisP_ainf (x : Ainf l) : crisP l (ainfToAcris l x) = ainfToBdRp l x :=
  (congrArg (crisP l) (GlobalTheory.RingIface.tower l x)).trans
    ((isCrisP_crisP l).on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x))


variable (l) in
def acrisToBdRp : Per.Acris l →ₐ[ℤ_[l]] Per.BdRp l where
  toRingHom := crisP l
  commutes' _ := crisP_ainf _

theorem complete_BdRp {d : Ainf l} (hd : Ideal.span {d} = RingHom.ker (Per.θ l)) :
    IsAdicComplete (Ideal.span {ainfToBdRp l d}) (Per.BdRp l) := by
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have h2 := congrArg (Ideal.map (GlobalTheory.MemLoc.aDp l)) (hd.trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE))
  rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h2
  have h3 := (GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE).2.2.1
  rw [← h2] at h3
  exact h3

variable {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O] (t : Wq l a →ₐ[ℤ_[l]] O)


variable (l O) in
abbrev OD : Type := O ⊗[ℤ_[l]] Per.BdRp l


variable (l O) in
def toOD : OA l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id _ _) (ainfToBdRp l)


variable (l O) in
def crisToOD : OCr l O →ₐ[O] OD l O := Algebra.TensorProduct.map (AlgHom.id _ _) (acrisToBdRp l)

theorem crisToOD_toOCr (x : OA l O) : crisToOD l O (toOCr l O x) = toOD l O x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul o w => exact congrArg (fun y : Per.BdRp l => o ⊗ₜ[ℤ_[l]] y) (crisP_ainf w)
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem isUnit_l_OD : IsUnit (l : OD l O) := by
  simpa only [map_natCast] using (GlobalTheory.MemLoc.isUnit_l_BdRp l).map
    (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)

def constD : (ZMod a → O) →ₐ[O] OD l O := (toOD l O).comp (constA t)

namespace PiSys

variable [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] {e : ℕ} [NeZero e] (O) (K : Type) [NormedField K]
  [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (ϖ : PiSys l e)


omit [NeZero e] in
def iAl : invL l (A O K) →+* OD l O :=
  IsLocalization.Away.lift (l : A O K) (g := ((toOD l O).comp (ϖ.iA O K)).toRingHom)
    (by rw [map_natCast]; exact isUnit_l_OD)


omit [NeZero e] in
theorem iAl_of_mem {f : K⟦X⟧} (h : f ∈ A O K) (h' : f ∈ invL l (A O K)) :
    ϖ.iAl O K ⟨f, h'⟩ = toOD l O (ϖ.iA O K ⟨f, h⟩) :=
  IsLocalization.Away.lift_eq (S := invL l (A O K)) (l : A O K)
    (g := ((toOD l O).comp (ϖ.iA O K)).toRingHom) (by rw [map_natCast]; exact isUnit_l_OD) ⟨f, h⟩

theorem complete_OD : IsAdicComplete (Ideal.span {ϖ.iAl O K (EIn l e _)}) (OD l O) := by
  rw [show ϖ.iAl O K (EIn l e _) = 1 ⊗ₜ ainfToBdRp l (ϖ.ev 1 (eis l 1 e)) from
    (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))]
  exact GlobalTheory.HWL.TensorWitt.complete_tensor (Module.Free.chooseBasis ℤ_[l] O) _
    (h := complete_BdRp (ϖ.span_ev_eis 1))

def iHatRing : Ahat O K l e →+* OD l O :=
  haveI := ϖ.complete_OD O K
  (AdicCompletion.ofAlgEquiv (Ideal.span {ϖ.iAl O K (EIn l e _)})).symm.toRingEquiv.toRingHom.comp
    (GlobalTheory.AdicMaps.adicMap (idE O K l e) _ (ϖ.iAl O K) (by simp [Ideal.span_le]))

theorem iHatRing_ofAl (f : invL l (A O K)) : ϖ.iHatRing O K (ofAl O K l e f) = ϖ.iAl O K f :=
  haveI := ϖ.complete_OD O K
  (congrArg (AdicCompletion.ofAlgEquiv (Ideal.span {ϖ.iAl O K (EIn l e _)})).symm
    (GlobalTheory.AdicMaps.adicMap_alg _ _ _ _ f)).trans ((AdicCompletion.ofAlgEquiv _).symm.commutes _)

def iHat : Ahat O K l e →ₐ[O] OD l O where
  toRingHom := ϖ.iHatRing O K
  commutes' o := (ϖ.iHatRing_ofAl O K (algebraMap O _ o)).trans
    ((ϖ.iAl_of_mem O K (algebraMap O (A O K) o).2 _).trans (((toOD l O).comp (ϖ.iA O K)).commutes o))

theorem iHat_ofAl (f : invL l (A O K)) : ϖ.iHat O K (ofAl O K l e f) = ϖ.iAl O K f := ϖ.iHatRing_ofAl O K f

theorem iHat_ofA (f : A O K) : ϖ.iHat O K (ofA O K l e f) = toOD l O (ϖ.iA O K f) :=
  (ϖ.iHat_ofAl O K _).trans (ϖ.iAl_of_mem O K f.2 _)

def iSD : invL l (S O K e) →+* OD l O :=
  IsLocalization.Away.lift (l : S O K e) (g := ((crisToOD l O).comp (ϖ.iS O K)).toRingHom)
    (by rw [map_natCast]; exact isUnit_l_OD)

theorem iSD_of_mem {f : K⟦X⟧} (h : f ∈ S O K e) (h' : f ∈ invL l (S O K e)) :
    ϖ.iSD O K ⟨f, h'⟩ = crisToOD l O (ϖ.iS O K ⟨f, h⟩) :=
  IsLocalization.Away.lift_eq (S := invL l (S O K e)) (l : S O K e)
    (g := ((crisToOD l O).comp (ϖ.iS O K)).toRingHom) (by rw [map_natCast]; exact isUnit_l_OD) ⟨f, h⟩

variable {O}

def iD : (ZMod a → Ahat O K l e) →ₐ[O] OD l O := glue (constD t) (ϖ.iHat O K)

theorem iD_ofA (f : ZMod a → A O K) : ϖ.iD t K (fun τ => ofA O K l e (f τ)) = toOD l O (ϖ.iTot t K f) :=
  (map_glue (toOD l O).toRingHom 0 (fun τ => by rw [add_zero]; rfl) fun τ => by
    rw [sub_zero]; exact (ϖ.iHat_ofA O K _).symm).symm

end PiSys

end GlobalTheory.BKReal
end
end
