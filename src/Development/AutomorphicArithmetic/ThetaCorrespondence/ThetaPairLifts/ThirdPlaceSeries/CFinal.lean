module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkNFam
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PreAtMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentConditionsEveryLocalisationStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpolyStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZeroStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProductStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingletonStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvG6OfAdmStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Tie0CutOfTie0
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.InCongruenceModuleJeReCutTOfRestrict
noncomputable section

namespace UpperTheory.GalC

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices Formalism Formalism.BasicNotions Formalism.MainNotions.N UpperTheory.GalC.Alg

variable {A X Γ : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Group Γ] {n r : ℕ}
  {T : Subalgebra A (X → A)} (S : Set X) {rep : X → (Γ →* GL (Fin n) A)}

theorem mem_cutT {f : X → A} (hf : f ∈ T) : (fun y : S => f y.1) ∈ cutT T S := ⟨f, hf, rfl⟩

theorem inRing_cut {a : X → Matrix (Fin n) (Fin n) A} (h : InRing T rep a) :
    InRing (cutT T S) (fun y : S => rep y.1) (fun y => a y.1) := by
  obtain ⟨m, f, g, hf, rfl⟩ := h
  refine ⟨m, fun k y => f k y.1, g, fun k => mem_cutT S (hf k), ?_⟩
  funext y
  simp [Finset.sum_apply]

theorem inCongruenceModuleJeRe_cutT_of_restrict {π : S} {e s : X → Matrix (Fin n) (Fin n) A} (h : InMatrixCongruenceModule T rep π.1 e s) :
    InMatrixCongruenceModule (cutT T S) (fun y : S => rep y.1) π (fun y => e y.1) (fun y => s y.1) := by
  obtain ⟨m, j, a, hj, rfl⟩ := h
  refine ⟨m, fun k y => j k y.1, fun k y => a k y.1, fun k => ⟨mem_cutT S (hj k).1, (hj k).2.1, inRing_cut S (hj k).2.2⟩, ?_⟩
  funext y
  simp [Finset.sum_apply]

theorem setting_cut [Nonempty S] {t : ℕ} {Z : Finset X} {Z' : Finset S} (hZ : ∀ y ∈ Z', y.1 ∈ Z)
    {ρ : X → (Γ →* GL (Fin r) A)} {χ : ℕ → (Γ →* Aˣ)} (h : HidaSetting t T Z rep ρ χ) :
    HidaSetting t (cutT T S) Z' (fun y : S => rep y.1) (fun y => ρ y.1) χ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  haveI := h1
  refine ⟨cutT_local T S, fun x y hxy => ?_, fun x => h3 x.1, fun g d => mem_cutT S (h4 g d), fun x => h5 x.1,
    fun x y g => h6 x.1 y.1 g, fun x hx => h7 x.1 (hZ x hx), fun x hx => h8 x.1 (hZ x hx)⟩
  obtain ⟨f, hf, hne⟩ := h2 x.1 y.1 fun e => hxy (Subtype.ext e)
  exact ⟨_, mem_cutT S hf, hne⟩

theorem isChoice_cut {t : ℕ} {ρ : X → (Γ →* GL (Fin r) A)} {χ : ℕ → (Γ →* Aˣ)} {π : S} {g0 : Γ} {L : ℕ}
    {eB e1 X0 : X → Matrix (Fin n) (Fin n) A} (h : IsChoice t T rep ρ χ π.1 g0 L eB e1 X0) :
    IsChoice t (cutT T S) (fun y : S => rep y.1) (fun y => ρ y.1) χ π g0 L (fun y => eB y.1) (fun y => e1 y.1)
      (fun y => X0 y.1) := by
  obtain ⟨⟨hB, h1, hBB, h11, hB1, h1B⟩, hdec, ⟨ϖ, s, hϖ, hs, rfl⟩, hroot⟩ := h
  refine ⟨⟨inRing_cut S hB, inRing_cut S h1, ?_, ?_, ?_, ?_⟩, hdec, ⟨ϖ, fun y => s y.1, hϖ, inCongruenceModuleJeRe_cutT_of_restrict S hs, rfl⟩,
    fun y => hroot y.1⟩
  · funext y; exact congrFun hBB y.1
  · funext y; exact congrFun h11 y.1
  · funext y; exact congrFun hB1 y.1
  · funext y; exact congrFun h1B y.1

theorem span_cut {O : Type} [CommRing O] [IsDomain O] [Algebra A O] {TO : Subalgebra O (X → O)}
    (h : Subalgebra.toSubmodule TO = Submodule.span O ((fun f : X → A => fun x => algebraMap A O (f x)) '' (T : Set _))) :
    Subalgebra.toSubmodule (cutT TO S) =
      Submodule.span O ((fun f : S → A => fun x => algebraMap A O (f x)) '' (cutT T S : Set _)) := by
  have e1 : Subalgebra.toSubmodule (cutT TO S) = (Subalgebra.toSubmodule TO).map (resA O S).toLinearMap :=
    Subalgebra.map_toSubmodule
  rw [e1, h, Submodule.map_span, cutT, Subalgebra.coe_map, ← Set.image_comp, ← Set.image_comp]
  rfl

end UpperTheory.GalC
end
end

noncomputable section

namespace UpperTheory.GalC.Tr

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.NRows

variable {D : D7} {c : CutD D}

theorem ptV_iff (i : (cut D c).nd.Loc) (P : D.naut.AV i.1) (x : (cut D c).nd.X i) :
    (cut D c).naut.ptV i P = some x ↔ D.naut.ptV i.1 P = some x.1 := optIn_eq_some

theorem par_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) (Sig : List (Part D.naut.CG)) :
    HasParamX (cut D c).nd (cut D c).naut i x Sig ↔ HasParamX D.nd D.naut i.1 x.1 Sig :=
  exists_congr fun _ => and_congr optIn_eq_some Iff.rfl

theorem zn_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    x ∈ ZN (cut D c).nd (cut D c).naut i ↔ x.1 ∈ ZN D.nd D.naut i.1 :=
  exists_congr fun _ => and_congr optIn_eq_some Iff.rfl

theorem zg_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    x ∈ ZgoodN (cut D c).nd (cut D c).naut i ↔ x.1 ∈ ZgoodN D.nd D.naut i.1 :=
  and_congr (zn_iff i x) (exists_congr fun Sig => and_congr (par_iff i x Sig) Iff.rfl)

theorem z_iff (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) : x ∈ (cut D c).nd.Z i ↔ x.1 ∈ D.nd.Z i.1 :=
  ((cut D c).Z_tie i x).trans ((zn_iff i x).trans (D.Z_tie i.1 x.1).symm)

theorem hg_of {i : (cut D c).nd.Loc} (h : HG (cut D c).nd (cut D c).naut i) : HG D.nd D.naut i.1 :=
  h.elim fun x hx => ⟨x.1, (zg_iff i x).1 hx⟩

theorem eigC_eq (i : (cut D c).nd.Loc) (x : (cut D c).nd.X i) :
    eigC (cut D c).nd (cut D c).naut i x = eigC D.nd D.naut i.1 x.1 := by
  have e : {P | (cut D c).naut.ptV i P = some x} = {P | D.naut.ptV i.1 P = some x.1} := Set.ext fun P => ptV_iff i P x
  unfold eigC
  rw [e]; rfl

theorem res_eq {O X : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X → O)) [IsLocalRing T] (f : T) (x y : X) :
    IsLocalRing.residue O ((f : X → O) x) = IsLocalRing.residue O ((f : X → O) y) := by
  let g : T := f - algebraMap O T ((f : X → O) x)
  have hx : (g : X → O) x = 0 := by simp [g]
  have hg : ¬ IsUnit g := fun h => by
    have := h.map ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom)
    have e : ((Pi.evalRingHom (fun _ : X => O) x).comp T.val.toRingHom) g = 0 := hx
    rw [e] at this
    exact not_isUnit_zero this
  have hy : ¬ IsUnit ((g : X → O) y) := fun h => by
    obtain ⟨u, hu⟩ := h
    let k : T := 1 - algebraMap O T (↑u⁻¹ : O) * g
    have hk : IsUnit k := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (algebraMap O T (↑u⁻¹ : O) * g) with h | h
      · exact absurd (isUnit_of_mul_isUnit_right h) hg
      · exact h
    have := hk.map ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom)
    have e : ((Pi.evalRingHom (fun _ : X => O) y).comp T.val.toRingHom) k = 0 := by
      show (1 : O) - (↑u⁻¹ : O) * (g : X → O) y = 0
      rw [← hu, Units.inv_mul, sub_self]
    rw [e] at this
    exact not_isUnit_zero this
  have e : (g : X → O) y = (f : X → O) y - (f : X → O) x := by simp [g]
  rw [e] at hy
  rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hy

theorem hecke_res (D : D7) (i : D.nd.Loc) (x y : D.nd.X i) (w : PlE D.host) :
    (heckePol D.nd i x w).map (IsLocalRing.residue (D.nd.O i)) = (heckePol D.nd i y w).map (IsLocalRing.residue (D.nd.O i)) := by
  haveI := D.nd.T_local i
  unfold heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Polynomial.map_add (f := _), Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, map_mul, res_eq (D.nd.T i) _ x y]

theorem atM_iff (i : (cut D c).nd.Loc) (σ : D.what₂.FT) : AtM (cut D c).nd (cut D c).naut i σ ↔ AtM D.nd D.naut i.1 σ := by
  refine exists_congr fun Sig => and_congr Iff.rfl ⟨fun ⟨x, h⟩ => ⟨x.1, h⟩, fun ⟨x, h⟩ => ?_⟩
  obtain ⟨y⟩ := (cut D c).nd.neX i
  refine ⟨y, fun w hw => ?_⟩
  obtain ⟨p, h1, h2⟩ := h w hw
  exact ⟨p, h1, h2.trans (hecke_res D i.1 x y.1 w)⟩

theorem rhoBar_iff (i : (cut D c).nd.Loc) (rb : G D.host.E D.nd.Om →* GL (Fin D.R.r) (IsLocalRing.ResidueField (D.nd.O i.1))) :
    IsRhoBar (cut D c).nd i rb ↔ IsRhoBar D.nd i.1 rb := by
  refine and_congr Iff.rfl ⟨fun h x w hw B σ hB hσ => ?_, fun h x => h x.1⟩
  obtain ⟨y⟩ := (cut D c).nd.neX i
  exact (h y w hw B σ hB hσ).trans (hecke_res D i.1 y.1 x w)

theorem goodPart_eq (i : (cut D c).nd.Loc) : goodPartM (cut D c).nd (cut D c).naut i = goodPartM D.nd D.naut i.1 := by
  have e : {σ | (cut D c).nd.goodRow σ ∧ AtM (cut D c).nd (cut D c).naut i σ} = {σ | D.nd.goodRow σ ∧ AtM D.nd D.naut i.1 σ} :=
    Set.ext fun σ => and_congr Iff.rfl (atM_iff i σ)
  unfold goodPartM
  rw [e]; rfl

theorem iSup_good (hc : c.Good) (i : (cut D c).nd.Loc) {α : Type} [CompleteLattice α] (F : D.nd.X i.1 → α) :
    ⨆ x ∈ ZgoodN (cut D c).nd (cut D c).naut i, F x.1 = ⨆ x ∈ ZgoodN D.nd D.naut i.1, F x :=
  le_antisymm (iSup₂_le fun x hx => le_iSup₂_of_le (f := fun x _ => F x) x.1 ((zg_iff i x).1 hx) le_rfl)
    (iSup₂_le fun x hx => le_iSup₂_of_le (f := fun (x : (cut D c).nd.X i) _ => F x.1)
      ⟨x, hc.good i.1 x ((D.Zgood_tie i.1 x).2 hx)⟩ ((zg_iff i _).2 hx) le_rfl)

theorem tie0_cut_of_tie0 (h : SumRepresentations.tie0 D) : SumRepresentations.tie0 (cut D c) :=
  ⟨h.1, ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, fun i => h.2.1.2.2.2 i.1⟩,
    fun i => h.2.2.1 i.1, fun i => h.2.2.2.1 i.1, fun i => h.2.2.2.2.1 i.1, fun i => h.2.2.2.2.2 i.1⟩

theorem fourthAdmissible_restrictToPoints (h : SumRepresentations.ArchimedeanSignatureMatching D) : SumRepresentations.ArchimedeanSignatureMatching (cut D c) := ⟨fun i => h.1 i.1, fun i => h.2.1 i.1, h.2.2⟩
theorem hypO_cut (h : SumRepresentations.hypO D) : SumRepresentations.hypO (cut D c) := fun i x => h i.1 x.1
theorem rhoBar_cut (h : ResidualIrreducibleRankR D) : ResidualIrreducibleRankR (cut D c) := fun i hg rb hrb => h i.1 (hg_of hg) rb ((rhoBar_iff i rb).1 hrb)

theorem rowsB_cut (h : RowsB D) : RowsB (cut D c) :=
  { rowSize := fun i => h.rowSize i.1, a3 := fun i => h.a3 i.1, a4 := fourthAdmissible_restrictToPoints h.a4, thetaOne := fun i => h.thetaOne i.1 }

theorem rowsC_cut (hc : c.Good) (h : RowsC D) : RowsC (cut D c) :=
  { c4b := fun σ k v h1 h2 i => h.c4b σ k v h1 h2 i.1
    rho := fun i x hx Sig hS => h.rho i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    dz := fun i x hx Sig hS => h.dz i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    parUp := fun i x hx Sig hS => by
      rw [eigC_eq]; exact h.parUp i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    downMem := fun i x hx Sig hS => by
      rw [eigC_eq]; exact h.downMem i.1 x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
    goodPart := fun i => by
      refine (goodPart_eq i).trans ((h.goodPart i.1).trans ((iSup_good hc i _).symm.trans ?_))
      refine iSup_congr fun x => iSup_congr fun _ => ?_
      have e : {Sig | HasParamX (cut D c).nd (cut D c).naut i x Sig} = {Sig | HasParamX D.nd D.naut i.1 x.1 Sig} :=
        Set.ext fun Sig => par_iff i x Sig
      rw [e]; rfl }


set_option maxHeartbeats 1000000 in
def ledBack (L : SizeData₂ (cut D c)) : SizeData₂ D := { L with }

theorem pointsAdmissible_restrictToPoints (hc : c.Good) (h : SumRepresentations.ConclusionZ D) : SumRepresentations.ConclusionZ (cut D c) := by
  classical
  intro i hg
  obtain ⟨a, b, d⟩ := h i.1 (hg_of hg)
  refine ⟨fun x hx Sig hS => ?_, ?_, ?_⟩
  · rw [eigC_eq]; exact a x.1 ((zg_iff i x).1 hx) Sig ((par_iff i x Sig).1 hS)
  · rw [goodPart_eq]
    refine b.trans ((iSup_good hc i _).symm.trans (iSup_congr fun x => iSup_congr fun _ => (eigC_eq i x).symm))
  · have e : dM (cut D c).nd (cut D c).naut i = dM D.nd D.naut i.1 := by unfold dM; rw [goodPart_eq]; rfl
    rw [e, ← d]
    refine Finset.sum_of_injOn (fun x => x.1) (fun x _ y _ k => Subtype.ext k) (fun _ _ => Finset.mem_univ _)
      (fun x _ hx => if_neg fun hz => hx ⟨⟨x, hc.good i.1 x ((D.Zgood_tie i.1 x).2 hz)⟩, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩)
      fun x _ => ?_
    have m : (cut D c).nd.mult i x = D.nd.mult i.1 x.1 := Alg.mult_eq _ _ _ (D.nd.T_sep i.1) x
    by_cases hz : x.1 ∈ ZgoodN D.nd D.naut i.1
    · rw [if_pos hz, if_pos ((zg_iff i x).2 hz), m]
    · rw [if_neg hz, if_neg fun k => hz ((zg_iff i x).1 k)]

theorem jointCondition_restrictToPoints (h : KillingConditions.LocalisationUniqueness D) : KillingConditions.LocalisationUniqueness (cut D c) :=
  fun i i' h1 h2 h3 σ hσ a b => Subtype.ext (h i.1 i'.1 h1 h2 h3 σ hσ ((atM_iff i σ).1 a) ((atM_iff i' σ).1 b))

theorem live_of {i : (cut D c).nd.Loc} (h : GlobalTheory.CoefDuty.Live (cut D c).nd i) : GlobalTheory.CoefDuty.Live D.nd i.1 := by
  obtain ⟨π, hπ, k⟩ := h
  exact ⟨π.1, (z_iff i π).1 hπ, k⟩

theorem large_cut (h : GlobalTheory.CoefDuty.Large D) : GlobalTheory.CoefDuty.Large (cut D c) := by
  refine ⟨hypO_cut h.1, fun i x => h.2.1 i.1 x.1, fun i hl => ?_⟩
  obtain ⟨r, ρ, hr, A, i1, i2, i3, i4, i5, i6, i7, TA, repA, ρA, χA, hE, hS, hC⟩ := h.2.2 i.1 (live_of hl)
  haveI : Nonempty (c.Xs i.1) := (c.ne i.1 i.2).to_subtype
  refine ⟨fun x => r x.1, fun x => ρ x.1, fun x => hr x.1, A, i1, i2, i3, i4, i5, i6, i7, Alg.cutT TA (c.Xs i.1),
    fun x => repA x.1, fun x => ρA x.1, χA,
    ⟨hE.1, span_cut (O := D.nd.O i.1) (TO := D.nd.T i.1) (c.Xs i.1) hE.2.1, fun x => hE.2.2.1 x.1, fun x hx => hE.2.2.2.1 x.1 ((z_iff i x).1 hx), hE.2.2.2.2⟩,
    setting_cut _ (fun y hy => (z_iff i y).1 hy) hS, fun π hπ => ?_⟩
  obtain ⟨g0, L, eB, e1, X0, a, b, d⟩ := hC π.1 ((z_iff i π).1 hπ)
  exact ⟨g0, L, fun y => eB y.1, fun y => e1 y.1, fun y => X0 y.1, a, isChoice_cut _ b, fun x => d x.1⟩

theorem cutRec_cut (hc : c.Good) : CutRec (cut D c) := by
  intro i P hP k w hw
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hP
  exact hc.nice i.1 i.2 P x.1 x.2 ((ptV_iff i P x).1 hx) k w hw

end UpperTheory.GalC.Tr
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExistsUnitOneAddGenerator
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial
open Formalism.MainNotions.N.PlaceLabelTeichmuller

namespace UpperTheory.GalC

attribute [local instance] GlobalTheory.PassOp.factGk GlobalTheory.PassOp.neZeroGk

theorem exists_unit_one_add_generator (D : D7) (hCen : GlobalTheory.Pass.CentralElt D) (i : D.nd.Loc) :
    ∃ z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))), ∀ F,
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) F =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F := by
  classical
  let zc : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) →
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    fun p => (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose
  let z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) :=
    ∑ p, if goodVec D p then zc p else 0
  have hp : ∀ p, PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (zc p : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • tens (fun kv => ESer D kv (p kv)) := by
    intro p
    obtain ⟨L, hnd, hall, he⟩ := (hCen i fun kv => Formalism.CyclotomicNorms.monicOf (p kv)).choose_spec
    rw [he]
    congr 1
    have e1 : (L.map fun kv => ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        L.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, GlobalTheory.PassOp.prod_plc _ L hnd]
    congr 1
    funext j
    rw [if_pos (hall j)]
  have hz : PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) =
      (D.what₂.restRowsFiniteGroupCard : ℂ) • D.ntypes.e0 := by
    rw [e0_eq, eGood, Finset.smul_sum, AddSubmonoidClass.coe_finsetSum]
    show MonoidAlgebra.mapRingHom _ (iotaO D.nd D.naut i) _ = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact hp p
    · simp
  have hcen : D.ntypes.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) :=
    Subalgebra.mem_center_iff.2 fun b => (goodElement_mem_center_groupAlgebra D b).symm
  refine ⟨z, fun F => ?_⟩
  rw [hz]
  unfold NTypes.onMt
  rw [dite_eq_left (Subalgebra.smul_mem _ hcen _), dite_eq_left hcen, ← LinearMap.smul_apply, ← map_smul]
  rfl

theorem exists_tuple (D : D7) (μ : D.what₂.Tup) (j : ℕ) (F : D.what₂.Mt μ j) (hF : D.ntypes.onMt μ j D.ntypes.e0 F ≠ 0) :
    ∃ s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X], D.ntypes.goodTuple s ∧
      ∀ k v, D.ntypes.onMt μ j (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k (s k v))) F ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  apply hF
  let ef := fun p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) =>
    fun kv => (⟨ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv))),
      GlobalTheory.CutAtGood.atPlace_mem_center D kv.1 kv.2 _ (D.ntypes.eSer_central kv.1 _)⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))))
  have ht : ∀ p : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)),
      tens (fun kv => ESer D kv (p kv)) = ((∏ kv, ef p kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        MonoidAlgebra ℂ (G0g D.nd)) := by
    intro p
    have hnd := (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).nodup_toList
    have hall : ∀ kv, kv ∈ (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList := fun kv => by simp
    have hprod : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
        ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))).prod =
        ((∏ kv, ef p kv : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
      have hmap : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
          ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
          ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map (ef p)).map (Subalgebra.val _) := by
        rw [List.map_map]; rfl
      rw [hmap, ← map_list_prod (Subalgebra.val _), ← List.prod_toFinset (ef p) hnd]
      simp
    rw [← hprod]
    have e1 : ((Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv =>
        ArithmeticCylinders.atPlace D kv.1 kv.2 (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (p kv)))) =
        (Finset.univ : Finset (Σ k : Fin 2, D.nd.PlG k)).toList.map fun kv => plc kv (ESer D kv (p kv)) :=
      List.map_congr_left fun kv _ => atPlace_eq D kv.1 kv.2 _
    rw [e1, GlobalTheory.PassOp.prod_plc _ _ hnd]
    congr 1
    funext q
    rw [if_pos (hall q)]
  have he : D.ntypes.e0 = ((∑ p, if goodVec D p then ∏ kv, ef p kv else 0 :
      ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)) := by
    rw [e0_eq, eGood, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs with hg
    · exact ht p
    · rfl
  have onMt_coe (c : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
      D.ntypes.onMt μ j (c : MonoidAlgebra ℂ (G0g D.nd)) = D.ntypes.cenMt μ j c := by
    unfold NTypes.onMt
    rw [dite_eq_left c.2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [he, onMt_coe, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun p _ => ?_
  split_ifs with hg
  · by_contra hc
    obtain ⟨k, v, h0⟩ := hcon (fun k v => Formalism.CyclotomicNorms.monicOf (p ⟨k, v⟩)) hg
    apply hc
    rw [← Finset.prod_erase_mul _ (ef p) (Finset.mem_univ ⟨k, v⟩), map_mul, Module.End.mul_apply]
    have hzero : D.ntypes.cenMt μ j (ef p ⟨k, v⟩) F = 0 := by
      rw [← onMt_coe]
      exact h0
    rw [hzero, map_zero]
  · rw [map_zero]; rfl

theorem exists_type (D : D7) (P : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (PI : D.naut.AV i) (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i))
    (hF : F ∈ D.naut.typeV i PI) (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X])
    (h1 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f)) F ≠ 0) :
    ∃ τ ∈ P.kty i PI k v, (P.lz k).lab τ = f := by
  classical
  have hc : ∀ τ ∈ (Finset.univ : Finset ((P.lz k).Irr D.R.r)),
      Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := by
    intro τ _
    split_ifs
    · exact GlobalTheory.CutAtGood.atPlace_mem_center D k v _ fun b => (P.lz k).idem_central τ b
    · rw [GlobalTheory.CutAtGood.atPlace_zero]
      exact Subalgebra.zero_mem _
  have hsum : D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (∑ τ, ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)) =
      ∑ τ, D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)) := by
    let a := fun τ => ArithmeticCylinders.atPlace D k v (if (P.lz k).lab τ = f then (P.lz k).idem τ else 0)
    have hco : ∀ τ, a τ ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)) := fun τ => hc τ (Finset.mem_univ _)
    have hcoe (c : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) :
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (c : MonoidAlgebra ℂ (G0g D.nd)) =
          D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) c := by
      unfold NTypes.onMt
      rw [dite_eq_left c.2]
    change D.ntypes.onMt _ _ (∑ τ, a τ) = ∑ τ, D.ntypes.onMt _ _ (a τ)
    have hval : (∑ τ, a τ) = ((∑ τ, (⟨a τ, hco τ⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))))) : MonoidAlgebra ℂ (G0g D.nd)) := by
      simp only [AddSubmonoidClass.coe_finsetSum]
    rw [hval, ← AddSubmonoidClass.coe_finsetSum, hcoe, map_sum]
    apply Finset.sum_congr rfl
    intro τ _
    exact (hcoe ⟨a τ, hco τ⟩).symm
  rw [P.eSer_eq k, GlobalTheory.CutAtGood.atPlace_sum, hsum, LinearMap.sum_apply] at h1
  obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  by_cases hlab : (P.lz k).lab τ = f
  · rw [if_pos hlab] at hτ
    exact ⟨τ, (P.kty_spec i PI k v τ).2 ⟨F, hF, hτ⟩, hlab⟩
  · exfalso
    apply hτ
    rw [if_neg hlab, GlobalTheory.CutAtGood.atPlace_zero]
    unfold NTypes.onMt
    rw [dite_eq_left (Subalgebra.zero_mem _)]
    have e0 : (⟨0, Subalgebra.zero_mem _⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) = 0 := rfl
    rw [e0, map_zero]
    rfl

theorem tuple_labels {D : D7} {s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]} (hg : D.ntypes.goodTuple s) (i : D.nd.Loc)
    (k : Fin 2) (v : D.nd.PlG k) :
    ((s k v).Monic ∧ (s k v).natDegree = D.R.r ∧ (s k v).coeff 0 ≠ 0) ∧ Squarefree (s k v) ∧
      ∀ u : (ZMod (D.host.g k))ˣ, u = PairedCharacterCondition.chiJ D i k v ∨ u = (PairedCharacterCondition.chiJ D i k v)⁻¹ → ¬ (s k v).IsRoot (u : ZMod (D.host.g k)) := by
  obtain ⟨h1, h2⟩ := hg k
  refine ⟨h1.1 v, h1.2.1 v, fun u hu hr => ?_⟩
  obtain ⟨ℓ, hℓg, hℓ⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  have hℓne : ℓ ≠ D.host.g k := by omega
  have hmem : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ∈
      Formalism.CyclotomicNorms.rootsBar (s k v) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.mem_roots (Polynomial.map_monic_ne_zero (f := algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))) (h1.1 v).1)]
    exact hr.map (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)))
  rcases hu with rfl | rfl
  · exact h1.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl
  · exact h2.2.2.2.1 ℓ hℓ hℓne v ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩ _ hmem rfl

theorem nc_of_type (D : D7) (Q : PairedCharacterCondition.Pend D) (hDZ : PairedCharacterCondition.admDZ Q) (h1 : SumRepresentations.adm1 D) (h0 : SumRepresentations.tie0 D) (i : D.nd.Loc) (PI : D.naut.AV i)
    {s : ∀ k, D.nd.PlG k → (ZMod (D.host.g k))[X]} (hg : D.ntypes.goodTuple s)
    (hs : ∀ k v, ∃ τ ∈ Q.kty i PI k v, (Q.lz k).lab τ = s k v) (k : Fin 2) (w : PlE D.host)
    (hw : w ∈ placesOver D.host.E (D.host.g k)) : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locV i PI w) := by
  obtain ⟨v, hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  obtain ⟨τ, hτ, e⟩ := hs k v
  obtain ⟨-, a, b⟩ := tuple_labels hg i k v
  exact UpperTheory.GalS.nc_of_label Q hDZ h1 i k v PI τ hτ (e ▸ a) (e ▸ b) w hv

end UpperTheory.GalC
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GaloisAdmissibleOfRestrictedCmDatum
namespace UpperTheory.GalC.Tr

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem galois_admissible_of_restricted_cmDatum {D : D7} {c : CutD D} (h : UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut) :
    UpperTheory.GalS.AutomorphicGaloisAdmissible (cut D c).nd (cut D c).naut := fun i =>
  ⟨fun a ha π hc hr => by
    obtain ⟨ρ, c1, s, o, u, e⟩ := (h i.1).1 a ha π hc hr
    exact ⟨ρ, c1, s, fun w hw => ⟨(o w hw).dim, (o w hw).eq_of_unr, (o w hw).ine, (o w hw).mono⟩,
      fun w hw g => ⟨(u w hw g).1, (u w hw g).2.1, ⟨(u w hw g).2.2.rel.dim, (u w hw g).2.2.rel.mono, (u w hw g).2.2.rel.ine⟩,
        (u w hw g).2.2.one⟩, e⟩, (h i.1).2⟩

end UpperTheory.GalC.Tr
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.FactsOfPre
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.CompatibilityTiesEigenRestriction
noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Alg

def descHom {O X M B : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] [Semiring B] [Algebra O B]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (S : Set X) (z : B →ₐ[O] Module.End O M)
    (h : ∀ b (f : T), z b * act f = act f * z b) : B →ₐ[O] Module.End O (cutM T act S) where
  toFun b := desc T act S (z b) (h b)
  map_one' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_one]; rfl
  map_mul' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [Module.End.mul_apply, desc_mk, desc_mk, desc_mk, map_mul]; rfl
  map_zero' := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, map_zero]; rfl
  map_add' a b := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [LinearMap.add_apply, desc_mk, desc_mk, desc_mk, map_add (f := _), LinearMap.add_apply, map_add (f := _)]
  commutes' a := LinearMap.ext fun u => by
    obtain ⟨m, rfl⟩ := (outM T act S).mkQ_surjective u
    rw [desc_mk, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply, map_smul]

variable {D : D7} (c : CutD D)

def zCut (Q : PairedCharacterCondition.Pend D) (i : D.nd.Loc) (S : Set (D.nd.X i)) :
    ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))) →ₐ[D.nd.O i]
      Module.End (D.nd.O i) (cutM (D.nd.T i) (D.nd.act i) S) :=
  descHom (D.nd.T i) (D.nd.act i) S (Q.zO i) (Q.zO_comm i)


set_option maxHeartbeats 2000000 in
def pendCut (Q : PairedCharacterCondition.Pend D) : PairedCharacterCondition.Pend (cut D c) where
  lz := Q.lz
  eSer_eq := Q.eSer_eq
  eSer_LL := Q.eSer_LL
  zetaPrimitiveRoot := fun i => Q.zetaPrimitiveRoot i.1
  om := Q.om
  om_one := Q.om_one
  om_mul := Q.om_mul
  tameInertiaChar_mul_root := Q.tameInertiaChar_mul_root
  om_wild := Q.om_wild
  om_open := Q.om_open
  om_inj := Q.om_inj
  om_tg := Q.om_tg
  inertiaCharpoly_eigenvalues := Q.inertiaCharpoly_eigenvalues
  inertiaCharpoly_character := Q.inertiaCharpoly_character
  zO := fun i => zCut Q i.1 (c.Xs i.1)
  zO_comm := fun i z f => desc_comm (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) f
  zL_stable := fun i => Q.zL_stable i.1
  zO_act := fun i z x y h =>
    (congrArg (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) (Q.zO_act i.1 z x y h)).trans
      (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) _).symm
  prMt_type := fun i PI x hx => by
    obtain ⟨a, b⟩ := Q.prMt_type i.1 PI x hx
    refine ⟨fun p hp => qK_mem (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (x := p) (a p.1 (optIn_eq_some.1 hp)), fun hn => ?_⟩
    show qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.prMt i.1 x) = 0
    cases hp : D.naut.ptV i.1 PI with
    | none => rw [b hp, map_zero]
    | some p =>
      refine qK_out (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (D.nd.T_sep i.1) (x := p) (fun hm => ?_) (a p hp)
      have := (optIn_eq_some (S := c.Xs i.1) (x := ⟨p, hm⟩)).2 hp
      exact Option.some_ne_none _ (this.symm.trans hn)
  Par_surj := fun i x Sig h => Q.Par_surj i.1 x.1 Sig (h.imp fun _ k => ⟨optIn_eq_some.1 k.1, k.2⟩)
  kty := fun i => Q.kty i.1
  kty_spec := fun i => Q.kty_spec i.1

theorem eigSpan_cut {Q : PairedCharacterCondition.Pend D} (h : GlobalTheory.Pass.EigSpan Q) : GlobalTheory.Pass.EigSpan (pendCut c Q) := by
  intro i z x a ha u hu
  have hu' : u ∈ (heckeEig (D.nd.T i.1) (D.nd.act i.1) x.1).map (qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1)) := by
    rw [map_eig _ _ _ (D.nd.T_sep i.1) x]; exact hu
  obtain ⟨v, hv, rfl⟩ := hu'
  have e := h i.1 z x.1 a (fun PI hP => ha PI (optIn_eq_some.2 hP)) v hv
  refine (qK_desc (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) _ (Q.zO_comm i.1 z) v).trans ?_
  rw [e]
  have k : ∀ (b : D.nd.O i.1) (w : TensorProduct (D.nd.O i.1) (FractionRing (D.nd.O i.1)) (D.nd.Mt i.1)),
      qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) (b • w) = b • qK (D.nd.T i.1) (D.nd.act i.1) (c.Xs i.1) w := fun b w => by
    rw [← algebraMap_smul (FractionRing (D.nd.O i.1)) b w, map_smul, algebraMap_smul]
  exact k a v

theorem compatibilityTies_eigenRestriction (h : Tie4 D) : Tie4 (cut D c) := by
  obtain ⟨a, ⟨Q, hDZ, hE⟩, b, d⟩ := h
  exact ⟨fun i => a i.1, ⟨pendCut c Q, fun i => hDZ i.1, eigSpan_cut c hE⟩, fun i => b i.1, fun i => d i.1⟩

end UpperTheory.GalC
end
end

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory Tr

variable {D : D7}


set_option maxHeartbeats 1000000 in
@[reducible] def nchCut (c : CutD D) (x : NChoice D) : NChoice (cut D c) := { x with }

set_option maxHeartbeats 1000000 in
theorem nct_cut (c : CutD D) {x : NChoice D} (h : NChTie D x) : NChTie (cut D c) (nchCut c x) :=
  { h with
    twOf_eq := fun a => h.twOf_eq a.1
    twSide_eq := fun a => h.twSide_eq a.1
    Q_eq := fun a => h.Q_eq a.1
    psi_eq := h.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

end UpperTheory.GalC
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTyzTer
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.NLink.Final
section Slot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab _root_.Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
end Slot
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField ReciprocityTheory.Gal GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Fc GlobalTheory.NFacts
abbrev _root_.GlobalTheory.NLink.Final.mainTheorem : Prop :=  GlobalTheory.NLink.Hypotheses₂ → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → SerN → GlobalTheory.Published.DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfDependence hL cDep) (fun Q L => _root_.GlobalTheory.Fc.R1.SlotNormCondition Q L fun 𝒞 => Formalism.MainNotions.Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm)
end GlobalTheory.NLink.Final
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CFacts
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AdmissibleSevenRestrict
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NoG4Restrict
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.GalC.Tr
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
theorem no_g4_restrict_alt {D : D7} {c : CutD D} (_ : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (_ : ∀ i, UpperTheory.GalS.UnusedSlot55 D.nd D.naut i) :
    ∀ i, UpperTheory.GalS.UnusedSlot55 (cut D c).nd (cut D c).naut i := fun _ => trivial
end UpperTheory.GalC.Tr
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC.Tr
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.NRows
variable {D : D7} {c : CutD D}
theorem admissible_seven_restrict_alt (h : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D) : _root_.Formalism.MainNotions.SumRepresentations.adm7_alt (cut D c) := h
theorem admA_cut (h : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt D) : _root_.Formalism.MainNotions.SumRepresentations.AdmAAlt (cut D c) :=
  ⟨tie0_cut_of_tie0 h.1, hypO_cut h.2.1, fun i => h.2.2.1 i.1, _root_.UpperTheory.GalC.Tr.galois_admissible_of_restricted_cmDatum h.2.2.2.1, fun i => h.2.2.2.2.1 i.1,
    fourthAdmissible_restrictToPoints h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
theorem admissible_cut (h : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum D) : _root_.Formalism.MainNotions.SumRepresentations.AdmissibleDatum (cut D c) :=
  ⟨⟨_root_.UpperTheory.GalC.Tr.admA_cut h.1.1, _root_.UpperTheory.GalC.Tr.admissible_seven_restrict_alt h.1.2⟩, rhoBar_cut h.2.1, h.2.2⟩
theorem rsA_cut_of_aux41 (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : _root_.GlobalTheory.NRows.RowsAAlt D) : _root_.GlobalTheory.NRows.RowsAAlt (cut D c) :=
  { tieLab := h.tieLab, hecke := h.hecke, tie0 := tie0_cut_of_tie0 h.tie0, a2 := _root_.UpperTheory.GalC.Tr.galois_admissible_of_restricted_cmDatum h.a2, an1 := h.an1, an2 := h.an2
    a5 := h.a5, temp := _root_.UpperTheory.GalC.Tr.admissible_seven_restrict_alt h.temp, g4p := _root_.UpperTheory.GalC.Tr.no_g4_restrict_alt h41 h.g4p, gsp := h.gsp }
theorem rs_cut_of_good_aux41 (hc : c.Good) (h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D) (h : _root_.GlobalTheory.NRows.PointConditions' D) : _root_.GlobalTheory.NRows.PointConditions' (cut D c) :=
  { a := _root_.UpperTheory.GalC.Tr.rsA_cut_of_aux41 h41 h.a, b := rowsB_cut h.b, c := rowsC_cut hc h.c
    typeNZ := fun i x hx F hF => h.typeNZ i.1 x.1 ((zg_iff i x).1 hx) F (eigC_eq i x ▸ hF)
    rank := fun L => h.rank (ledBack L) }
theorem admissible_tame_eigenvalues_of_cut (h : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues D) : _root_.UpperTheory.GalS.AdmissibleResidualTameEigenvalues (cut D c) :=
  fun i Sig hx => h i.1 Sig (hx.elim fun x k => ⟨x.1, (par_iff i x Sig).1 k⟩)
end UpperTheory.GalC.Tr
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsGood
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Polynomial
open Formalism.MainNotions.N.PlaceLabelTeichmuller
namespace UpperTheory.GalC
attribute [local instance] GlobalTheory.PassOp.factGk GlobalTheory.PassOp.neZeroGk
theorem exists_good_alt (hCen : ∀ (D : D7) (_ : PairedCharacterCondition.Pend D), GlobalTheory.Pass.CentralElt D) {D : D7} {nch : NChoice D} (hP : _root_.UpperTheory.GalC.GaloisPreconditions D nch)
    (hT : Tie4 D) : ∃ c : CutD D, c.Good := by
  classical
  obtain ⟨-, ⟨Q, hDZ, hEig⟩, -, hSer⟩ := hT
  have h0 : SumRepresentations.tie0 D := hP.adm.1.1.1
  have h1 : SumRepresentations.adm1 D := hP.adm.1.1.2.2.1
  have h5 : SumRepresentations.adm5 D := hP.adm.1.1.2.2.2.2.2.2
  have h41 : _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D := hP.Conclusion1.1
  let Xs : ∀ i, Set (D.nd.X i) := fun i => {x | ∃ PI, D.naut.ptV i PI = some x ∧ ∃ F ∈ D.naut.typeV i PI,
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F ≠ 0}
  have hZ : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ D.nd.Z i := fun i x hx => (D.Z_tie i x).2 ((D.Zgood_tie i x).1 hx).1
  have hgood : ∀ i, ∀ x ∈ D.nd.Zgood i, x ∈ Xs i := fun i x hx => by
    obtain ⟨PI, hPI⟩ := D.naut.pt_surj i x
    obtain ⟨F, hF, hF0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i PI)
    exact ⟨PI, hPI, F, hF, by
      rw [(_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx]; exact hF0⟩
  refine ⟨⟨fun i => (D.nd.Zgood i).Nonempty, Xs, fun i ⟨x, hx⟩ => ⟨x, hgood i x hx⟩⟩,
    fun _ => Iff.rfl, hgood, fun i x hx ⟨PI, hPI, F, hF, hne⟩ => ?_, fun i _ => ?_, fun i _ P x ⟨PI, hPI, F, hF, hne⟩ hx k w hw => ?_⟩
  · by_contra hxg
    exact hne ((_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x hx PI hPI F hF).2 hxg)
  · obtain ⟨z, hact⟩ := exists_unit_one_add_generator D (hCen D Q) i
    refine ⟨Q.zO i z, Q.zO_comm i z, fun x hx u hu => ?_, fun x hx u hu => ?_⟩
    · have := hEig i z x (D.what₂.restRowsFiniteGroupCard : D.nd.O i) (fun PI hPI F hF => by
        rw [hact, (_root_.GlobalTheory.PassOp.onMt_e0_eq_self_of_mem_zgood_and_eq_zero_of_notMem D Q hSer h41 h0 h1 h5 i x (hZ i x hx) PI hPI F hF).1 hx, map_natCast]) u hu
      rw [this, ← algebraMap_smul (KK D.nd i) (D.what₂.restRowsFiniteGroupCard : D.nd.O i) u, map_natCast, Int.cast_natCast]
    · have := hEig i z x 0 (fun PI hPI F hF => by
        have e : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = 0 := by
          by_contra hne
          exact hx ⟨PI, hPI, F, hF, hne⟩
        rw [hact, e, smul_zero, map_zero, zero_smul]) u hu
      rw [this, zero_smul]
  · obtain ⟨s, hg, hs⟩ := exists_tuple D _ _ F hne
    have hn := nc_of_type D Q hDZ h1 h0 i PI hg (fun k v => exists_type D Q i PI F hF k v _ (hs k v)) k w hw
    obtain ⟨Pa, hB⟩ := h1 i PI
    obtain ⟨Pa', hB'⟩ := h1 i P
    have hperm : Pa.Perm Pa' := ((h41 i).2.1 PI P (by rw [hPI]; exact Option.some_ne_none x)
      (hPI.trans hx.symm)).1 Pa Pa' hB hB'
    have hB2 := GlobalTheory.RowThetaParam.isBCV_of_perm D.nd D.naut hperm.symm hB'
    have hsp := GlobalTheory.DepthZeroType.isSplitPl_of_over D k w hw
    rwa [← hB.2.2.2.1 w hsp, hB2.2.2.2.1 w hsp] at hn
end UpperTheory.GalC
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory Tr
variable {D : D7}
set_option maxHeartbeats 1000000 in
theorem pre_cut_alt {c : CutD D} (hc : c.Good) {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) : _root_.UpperTheory.GalC.GaloisPreconditions (cut D c) (nchCut c x) :=
  have R := _root_.UpperTheory.GalC.Tr.rs_cut_of_good_aux41 hc h.Conclusion1.1 h.what₂
  have A := _root_.UpperTheory.GalC.Tr.admissible_cut (c := c) h.adm
  have lam : GlobalTheory.NRows.LamUsed (cut D c) := h.lam
  { what₂ := R
    adm := A
    Conclusion1 := _root_.UpperTheory.GalS.Parts.main_alt_alt _ A.1 R.a.tieLab R.b.rowSize R.a.hecke lam.loc R.b.thetaOne R.a.g4p
    z := pointsAdmissible_restrictToPoints hc h.z
    rhoBar := rhoBar_cut h.rhoBar
    g3p := _root_.UpperTheory.GalC.Tr.admissible_tame_eigenvalues_of_cut h.g3p
    weight := fun i => h.weight i.1
    block := fun i => h.block i.1
    muUnr := fun i => h.muUnr i.1
    depthG := fun i => h.depthG i.1
    bc := h.bc
    lam := lam
    c2 := jointCondition_restrictToPoints h.c2
    large := large_cut h.large
    nct := nct_cut c h.nct
    trip := fun a => h.trip a.1
    same := fun a => h.same a.1
    good := h.good }
theorem facts_of_galois_preconditions_of_cutRec (hCh : GlobalTheory.TwSys.Cheb) (lf : LocalFiniteness) (ltd : LocalTateDuality) (lec : LocalEulerChar)
    {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) (hC : CutRec D) : _root_.GlobalTheory.NFacts.NormChoiceFacts D x :=
  have ex : GlobalTheory.StringRepresentationDecomposition.RbEx D := GlobalTheory.T.residualRankPartExists_of_jointCondition D h.what₂.c.rho
  have h0 : SumRepresentations.tie0 D := h.adm.1.1.1
  have h1 : SumRepresentations.adm1 D := h.adm.1.1.2.2.1
  have g2 := _root_.UpperTheory.GalS.de_rham_points_weight_jumps_alt D h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC
  { what₂ := h.what₂, adm := h.adm, Conclusion1 := h.Conclusion1
    Conclusion2 := ⟨_root_.UpperTheory.GalS.prvG5_of_admissible_cutRec lf ltd lec D h.adm ex hC, _root_.GlobalTheory.T.prvG6_of_admissible' D h.adm ex, h.z⟩
    rhoBar := h.rhoBar, g3p := h.g3p, weight := h.weight, block := h.block, g2 := g2
    admJ := fun L hL => _root_.UpperTheory.GalS.admJ_of_admPar D L h0 h1 h.what₂.a.a2 h.what₂.a.a5 hC h.weight h.block hL
    muUnr := h.muUnr, depthG := h.depthG, bc := h.bc, lam := h.lam, c2 := h.c2, large := h.large
    duties := _root_.UpperTheory.GalS.duties_of_large_aux41 hCh D h.large h.Conclusion1.1 g2.2 h.rhoBar
    nct := h.nct, trip := h.trip, same := h.same, good := h.good }
theorem exists_good_cut_facts_tie4 (hCh : GlobalTheory.TwSys.Cheb) (lf : LocalFiniteness) (ltd : LocalTateDuality) (lec : LocalEulerChar)
    {x : NChoice D} (h : _root_.UpperTheory.GalC.GaloisPreconditions D x) (hT : Tie4 D) :
    ∃ c : CutD D, c.Good ∧ _root_.GlobalTheory.NFacts.NormChoiceFacts (cut D c) (nchCut c x) ∧ Tie4 (cut D c) := by
  obtain ⟨c, hc⟩ := _root_.UpperTheory.GalC.exists_good_alt (GlobalTheory.T.central_elements_from_idempotent_coeffs GlobalTheory.CentralIdem.centralIdemCoeff) h hT
  exact ⟨c, hc, _root_.UpperTheory.GalC.facts_of_galois_preconditions_of_cutRec hCh lf ltd lec (_root_.UpperTheory.GalC.pre_cut_alt hc h) (cutRec_cut hc), compatibilityTies_eigenRestriction c hT⟩
end UpperTheory.GalC
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.GalC
theorem final_alt_alt : _root_.GlobalTheory.NLink.Final.mainTheorem := by
  intro hP prN hX serN dzs lf ltd lec hL cDep hAt
  exact _root_.UpperTheory.GalC.final_of_alt hP (fun _ _ h hT => _root_.UpperTheory.GalC.exists_good_cut_facts_tie4 prN.cheb lf ltd lec h hT) prN hX dzs hL cDep
    (_root_.UpperTheory.GalS.galois_preconditions_at_mem prN hX serN dzs lf ltd lec hL) hAt
end UpperTheory.GalC
end
end
