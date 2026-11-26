module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassifiedTorusTorsionPointEqUniformisationTorus
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsWeightEqParameterSubRho

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqScaleAtResidueChar
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem fvalP_eq_FK (D : D7) (L : SizeData₂ D) (j p : ℕ) :
    FvalP L j p = FK L.sc D j p := by
  have hg : (p ∈ L.gTypes) ↔ ∃ i, p = D.host.g i := by
    simp only [Formalism.BasicNotions.SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  unfold FvalP FK
  by_cases h : ∃ i, p = D.host.g i
  · rw [if_pos (hg.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hg.mp h')), if_neg h]

theorem Fval_eq_FK : ∀ (D : D7) (L : SizeData₂ D) (j : ℕ) (v : D.what₂.places.Pl),
    Fval L j v = FK L.sc D j (D.what₂.places.resChar v) := by
  intro D L j v
  exact fvalP_eq_FK D L j _

theorem resChar_eq_plc (D : D7) (w : D.what₂.places.Pl) :
    D.what₂.places.resChar w = Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  have hp : (D.what₂.places.resChar w).Prime := D.what₂.places.resChar_prime w
  have hmem := Formalism.L2.Col.att_resChar_mem D.what₂.places D.plEq D.val_eq w
  haveI : Nontrivial (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) :=
    Ideal.Quotient.nontrivial_iff.2 (D.plEq w).isPrime.ne_top
  have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) = 0 := by
    have := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
    simpa using this
  have hdvd : ringChar (𝓞 D.what₂.LL ⧸ (D.plEq w).asIdeal) ∣ D.what₂.places.resChar w :=
    ringChar.dvd h0
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1.symm

theorem ofRecord_Fj_succ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ) (hK : DV.KapDef D)
    (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m) :
    (Formalism.L2.DIV.ofRecord D L Del h0).Fj ((j : ℕ) + 1) y = F0K L.sc D y j := by
  have h := Formalism.L2.DIV.ofRecord_Fval D L Del h0 hK (j := (j : ℕ) + 1) (Nat.le_add_left 1 _)
    (Nat.succ_le_of_lt j.isLt) (D.plEq.symm y)
  rw [Fval_eq_FK] at h
  have hc : D.what₂.places.resChar (D.plEq.symm y) = Formalism.EigenvalueLevelCeiling.plc y := by
    rw [resChar_eq_plc, Equiv.apply_symm_apply]
  unfold F0K Formalism.L2.DIV.NumDatum.Fj
  rw [h, hc]

end GlobalTheory.Mem.Top.Bl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelTwistTrivialLocalMove
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelTwistTrivialLocalMove
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChTwRead

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def noFr (p : DecoF E n ST SG Q) : DecoF E n ST SG ∅ :=
  ⟨(p.deco, fun P => absurd P.2 (Finset.notMem_empty _)), fun P => absurd P.2 (Finset.notMem_empty _)⟩

theorem isPtOf_iff (g : GL (Fin n) (AfE F E)) (p : DecoF E n ST SG Q) :
    IsPtOf hc g p ↔ (g ∈ UAd hc n ∧ p.deco.1 = decoRaw ST SG g) ∧
      ∀ (P : Q) (i j : Fin n), adAt F P.1 ((g : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        algebraMap E _ (p.fr P (Pi.single j 1) i) := by
  have key := PtDeco.isPtOf_iff_decoRaw F E hc n ST SG ∅ g (noFr p) rfl
  constructor
  · intro h
    exact ⟨key.1 ⟨h.uni, h.lat, h.f, h.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩, h.fr⟩
  · rintro ⟨h, h'⟩
    have h2 := key.2 h
    exact ⟨h2.uni, h2.lat, h2.f, h2.be, h'⟩

theorem adAt_congr_prV (P : HeightOneSpectrum (𝓞 E)) {z z' : AfE F E}
    (h : prV (E := E) (P.under (𝓞 F)) z = prV (E := E) (P.under (𝓞 F)) z') : adAt F P z = adAt F P z' := by
  have h0 := TilX.adAt_eq_zero_of_prV P (z - z') (by rw [map_sub, h, sub_self])
  rwa [map_sub, sub_eq_zero] at h0

theorem exists_pt_of_agree {g₁ g' : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h₁ : IsPtOf hc g₁ p)
    (hg' : g' ∈ UAd hc n)
    (hv : ∀ P ∈ Q, bc (prV (E := E) (P.under (𝓞 F))) g' = bc (prV (E := E) (P.under (𝓞 F))) g₁) :
    ∃ q : DecoF E n ST SG Q, IsPtOf hc g' q := by
  obtain ⟨⟨-, hd1⟩, -⟩ := (isPtOf_iff hc g₁ p).1 h₁
  have hloc : ∀ P ∈ Q, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal p.deco.1.N := by
    intro P hP
    rw [hd1]
    exact updn_mem_loc (v := P.under (𝓞 F)) (P := P) rfl (hv P hP)
  refine ⟨⟨(⟨decoRaw ST SG g', decorated_lattice_exists hc n ST SG g' hg'⟩, p.fr), fun P x => ?_⟩, ?_⟩
  · show p.fr P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.UG.CS.globLat g' (stdLat E n)) ↔ _
    rw [hloc P.1 P.2]
    exact p.2 P x
  · refine (isPtOf_iff hc g' _).2 ⟨⟨hg', rfl⟩, fun P i j => ?_⟩
    show _ = algebraMap E _ (p.fr P (Pi.single j 1) i)
    rw [← h₁.fr P i j]
    apply adAt_congr_prV
    exact congrArg (fun g => g.1 i j) (hv P.1 P.2)

theorem isPtOf_mul {g g₁ s : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q} (h : GLG (E := E) (n := n) (SG := SG))
    (hq : q.deco.1 = p.deco.1.act 1 h) (hg : IsPtOf hc g p) (hg₁ : IsPtOf hc g₁ p) (hs : IsPtOf hc (g₁ * s) q) :
    IsPtOf hc (g * s) q := by
  obtain ⟨⟨hgu, hdg⟩, hfg⟩ := (isPtOf_iff hc g p).1 hg
  obtain ⟨⟨hu1, hd1⟩, hf1⟩ := (isPtOf_iff hc g₁ p).1 hg₁
  obtain ⟨⟨hsu, hds⟩, hfs⟩ := (isPtOf_iff hc (g₁ * s) q).1 hs
  have hsU : s ∈ UAd hc n := by
    have e : s = g₁⁻¹ * (g₁ * s) := by group
    rw [e]
    exact mul_mem (inv_mem hu1) hsu
  obtain ⟨hJ, -⟩ := mem_congruence_of_action hc ST SG hsu hu1 h (by rw [← hds, hq, hd1])
  have hK := mem_principal_of_same_decoration hc n ST SG hu1 hgu (hd1.symm.trans hdg)
  have hc' := K1_conj hc n ST SG ⟨_, hJ⟩ (a := ⟨g₁⁻¹ * g, principal_le_adelic_unitary hc n ST SG hK⟩)
    (Subgroup.mem_subgroupOf.2 hK)
  rw [Subgroup.mem_subgroupOf] at hc'
  have e : g * s = (g₁ * s) * ((((g₁ * s)⁻¹ * g₁) * (g₁⁻¹ * g)) * ((g₁ * s)⁻¹ * g₁)⁻¹) := by group
  have hdr : decoRaw ST SG (g * s) = decoRaw ST SG (g₁ * s) := by
    rw [e]
    exact decorated_lattice_mul_principal hc n ST SG _ hc'
  refine (isPtOf_iff hc (g * s) q).2 ⟨⟨mul_mem hgu hsU, hds.trans hdr.symm⟩, fun P i j => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hfs P i j, Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, map_mul, hfg P i l, hf1 P i l]

end GlobalTheory.Mem.Col2.ChTwRead

namespace GlobalTheory.Mem.Col2.TC.ChTw

theorem locMv_of_mem : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : Ch → GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)), x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) → (∀ v, I.UnderQ a v → bc (prV (E := B.host.E) v) x = 1) → x ∈ U (chOf c) → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ := by
  intro B X I hI _ u a i _ Ch chOf Lb U chi y st k hR c x hx hx1 hxU
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := hpk.uni
  have hg' : y c * x * k (chOf c) ∈ UAd B.sp.cm (B.R.N i) := by
    have e : y c * x * k (chOf c) = y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) := by group
    rw [e]
    exact mul_mem hp.uni (mul_mem (mul_mem (inv_mem hk) hx) hk)
  have hv : ∀ P ∈ I.Q a, bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * x * k (chOf c)) =
      bc (prV (E := B.host.E) (P.under (𝓞 B.host.F))) (y c * k (chOf c)) := by
    intro P hP
    have h1 := hx1 (P.under (𝓞 B.host.F)) ⟨P, hP, rfl⟩
    simp only [map_mul, h1, mul_one]
  obtain ⟨q, hq⟩ := ChTwRead.exists_pt_of_agree B.sp.cm hp hg' hv
  obtain ⟨κ, hκ1, hκq, hκc⟩ := (hR.lev c x q hq).1 hxU
  refine ⟨κ, hκ1, hκc, fun g hg => ?_⟩
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hγ : κ.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hκ1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  · refine ChTwRead.isPtOf_mul B.sp.cm κ.2.1.1 ?_ hg hp (by rw [e, hκq]; exact hq)
    show ((κ.1, (κ.2.1 : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs))) • ((I.stp u a i).rep c).1.1.deco).1 = _
    rw [hγ]
    rfl
end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLevelTwistTrivialLocalMoveStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartLevel_twistTrivial_localMove : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), i ≤ B.R.m → ∀ {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U : Ch → Subgroup (GA B (B.R.N i))) (chi : ∀ β, U β →* ℂˣ) (y : (I.stp u a i).Cl → GA B (B.R.N i)) (st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k : Ch → GA B (B.R.N i)), I.Reads u a i chOf Lb U chi y st k → ∀ (c : (I.stp u a i).Cl) (x : GA B (B.R.N i)), x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) → (∀ v, I.UnderQ a v → bc (prV (E := B.host.E) v) x = 1) → x ∈ U (chOf c) → ∃ κ, GlobalTheory.Mem.Col2.TC.ChTw.LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem | exact GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesEqUnionThreeParts
noncomputable section

namespace GlobalTheory.Mem.R3

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl}

def Dat.IwasawaPlaceIndex (z : Dat X I hX T Wt) : Set X.B.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({X.toD7.plEq w, Formalism.DivisionValues.conjPl (X.toD7.plEq w)} : Set (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))),
    (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0}

def Dat.W1jw (z : Dat X I hX T Wt) : Set X.B.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({X.toD7.plEq w, Formalism.DivisionValues.conjPl (X.toD7.plEq w)} : Set (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))),
    Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
              (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
        (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0}

def placesWithNonzeroContentOrConj (D : D7) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) : Set D.what₂.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({D.plEq w, Formalism.DivisionValues.conjPl (D.plEq w)} : Set (HeightOneSpectrum (𝓞 D.what₂.LL))), F0 w' j ≠ 0}

theorem Dat.auxiliaryPlaces_eq_union_three_parts (z : Dat X I hX T Wt) (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ) :
    z.W1 F0 = z.IwasawaPlaceIndex ∪ z.W1jw ∪ placesWithNonzeroContentOrConj X.toD7 F0 := by
  ext w
  simp only [Dat.W1, Dat.IwasawaPlaceIndex, Dat.W1jw, placesWithNonzeroContentOrConj, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, w', hw', h | h | h⟩
    · exact Or.inl (Or.inl ⟨j, w', hw', h⟩)
    · exact Or.inl (Or.inr ⟨j, w', hw', h⟩)
    · exact Or.inr ⟨j, w', hw', h⟩
  · rintro ((⟨j, w', hw', h⟩ | ⟨j, w', hw', h⟩) | ⟨j, w', hw', h⟩)
    · exact ⟨j, w', hw', Or.inl h⟩
    · exact ⟨j, w', hw', Or.inr (Or.inl h)⟩
    · exact ⟨j, w', hw', Or.inr (Or.inr h)⟩

theorem Dat.mem_auxiliaryPlaces_iff_three_parts (z : Dat X I hX T Wt) (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ)
    (w : X.B.places.Pl) : w ∈ z.W1 F0 ↔ (w ∈ z.IwasawaPlaceIndex ∨ w ∈ z.W1jw) ∨ w ∈ placesWithNonzeroContentOrConj X.toD7 F0 :=
  Set.ext_iff.mp (z.auxiliaryPlaces_eq_union_three_parts F0) w

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator

noncomputable section

namespace GlobalTheory.ToricTorsionSec

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ, Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem appTop_unitOn {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) :
    (spMap f).appTop.hom (unitOn u).val = (unitOn (Units.map f.toMonoidHom u)).val := by
  have e := congrArg (fun φ => φ.hom (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  exact e.symm

theorem isPullF_torusPt {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] (τ : Multiplicative D.X →* Fˣ)
    (g : GtPt D (Over.mk (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))))
    (hg : ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ)))) (q : GtPtF D F) (hq : GlobalTheory.UT.IsTor τ q) :
    GtPt.IsPullF F (𝟙 _) g q := by
  refine ⟨?_, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  · rw [hq.1, (hg 0).1, Category.id_comp, Hom.one_def, DegPre.zeroT, Over.comp_left, Over.comp_left]
    congr 1
    have e₁ := Over.w (toUnit (TF (R := R) F))
    have e₂ := Over.w (toUnit (Over.mk (spMap ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))))))
    simp only [Over.mk_hom] at e₁ e₂
    rw [← Category.comp_id (toUnit (TF (R := R) F)).left, ← Category.comp_id (toUnit (Over.mk _)).left]
    exact e₁.trans ((spMap_comp _ _).symm.trans e₂.symm)
  · refine Units.ext ?_
    rw [hq.2 χ y J hJ, val_pull hJ, Category.id_comp, GlobalTheory.TorusTorsion.TorusVal.val_eq (hg χ) _ hJ]
    exact gs_unit (𝟙 _) y ⊤ trivial (unitOn (τ (Multiplicative.ofAdd χ)))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) → ∀ k : ℕ, 1 ≤ k →
    ∃ s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G),
      (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
        a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A') (f : A →+* A')
        (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
        a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
        (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a : R →+* F) τ h (q : QkPt P.D.toPre F k),
        a = (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
        GlobalTheory.FlatTors.IsImage P F k q (s F a τ h).left := by
  intro E _ _ _ H R _ _ _ t P _ hR k hk
  obtain ⟨N, g₀, x₀, hfin, -, -, hU, htors, hform⟩ :=
    GlobalTheory.WholeBaseFinitePart.exists_torsion_toG E H R hR t P k hk
  let u : ∀ (A : Type) [CommRing A] (_ : Multiplicative P.D.toPre.X →* Aˣ),
      P.D.toPre.X →+ Additive Γ(Sp A, ⊤)ˣ := fun A _ τ =>
    AddMonoidHom.mk' (fun χ => Additive.ofMul (unitOn (τ (Multiplicative.ofAdd χ)))) (fun χ χ' => by
      simp only [ofAdd_add, map_mul, unitOn, ofMul_mul])
  have hu : ∀ (A : Type) [CommRing A] (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → k • u A τ = 0 := by
    intro A _ τ hτ
    refine AddMonoidHom.ext fun χ => Additive.toMul.injective ?_
    have e : (τ (Multiplicative.ofAdd χ)) ^ k = 1 := by rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    simp only [u, AddMonoidHom.nsmul_apply, AddMonoidHom.mk'_apply, toMul_nsmul, toMul_ofMul, unitOn, ← map_pow, e,
      map_one, AddMonoidHom.zero_apply, toMul_zero]
  have ex : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ),
      ∃ g : GtPt P.D.toPre (Over.mk (spMap a)), ∀ χ, TorusVal g χ (unitOn (τ (Multiplicative.ofAdd χ))) := by
    intro A _ a τ
    obtain ⟨g, hg⟩ := GlobalTheory.TorusTorsion.exists_torusPt (D := P.D.toPre) (T := Over.mk (spMap a)) (u A τ)
    exact ⟨g, hg⟩
  choose gT hgT using ex
  have ex₂ : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 →
      ∃! h : Over.mk (spMap a) ⟶ N, GtPt.IsPull h.left g₀ (gT A a τ) := by
    intro A _ a τ hτ
    obtain ⟨g', h₁, h₂⟩ := GlobalTheory.TorusTorsion.exists_nsmul_zero k (u A τ) (hu A τ hτ) (T := Over.mk (spMap a))
      (g := gT A a τ) (hgT A a τ)
    exact hU _ _ ⟨g', h₁, h₂⟩
  choose hT hhT hTu using ex₂
  refine ⟨fun A _ a τ hτ => hT A a τ hτ ≫ x₀, fun A _ a τ hτ => ?_,
    fun A A' _ _ a a' f τ hτ τ' hτ' ha hτf => ?_, fun A A' _ _ a ha a' f t₀ m₀ τ hτ z ha' hz => ?_,
    fun F _ _ _ a τ hτ q ha hq hqt => ?_⟩
  · show (hT A a τ hτ ≫ x₀) ^ k = 1
    rw [← MonObj.comp_pow, htors, MonObj.comp_one]
  · subst ha
    let ρ : Over.mk (spMap (f.comp a)) ⟶ Over.mk (spMap a) := Over.homMk (spMap f) (spMap_comp a f).symm
    have hρ : GtPt.IsPull ρ.left (gT A a τ) (gT A' (f.comp a) τ') :=
      GlobalTheory.TorusTorsion.isPull_of_units ρ (hgT A a τ) (hgT A' _ τ') fun χ => by
        refine (appTop_unitOn f _).trans ?_
        congr 2
        exact Units.ext (hτf _).symm
    have e := hTu A' _ τ' hτ' (ρ ≫ hT A a τ hτ) (isPull_trans (hhT A a τ hτ) hρ)
    show (hT A' (f.comp a) τ' hτ' ≫ x₀).left = spMap f ≫ (hT A a τ hτ ≫ x₀).left
    rw [← e]
    rfl
  · subst ha'
    exact GlobalTheory.T.classified_torusTorsionPoint_eq_uniformisationTorus E H R t P N g₀ x₀ hform A A' a ha f t₀ m₀ τ z hz (gT A' _ τ) (hgT A' _ τ) (hT A' _ τ hτ)
      (hhT A' _ τ hτ)
  · subst ha
    have hx : OverGen F N (hT F _ τ hτ).left := (Over.w (hT F _ τ hτ)).trans (spMap_comp _ _)
    have hp := isPullF_trans (hhT F _ τ hτ) (isPullF_torusPt τ (gT F _ τ) (hgT F _ τ) q.g hqt)
    rw [Category.id_comp] at hp
    exact GlobalTheory.WholeBaseFinitePart.generic E H R hR t P k hk N g₀ x₀ hfin htors hform F _ hx q hq hp

end GlobalTheory.ToricTorsionSec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsToricTorsionSectionsUniformisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toric_torsion_sections_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) [CharZero R], AdmBase R (maximalIdeal R) → ∀ k : ℕ, 1 ≤ k →
    ∃ s : ∀ (A : Type) [CommRing A] (a : R →+* A) (τ : Multiplicative P.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t.G),
      (∀ (A : Type) [CommRing A] (a : R →+* A) τ h, s A a τ h ^ k = 1) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (a' : R →+* A') (f : A →+* A') τ h τ' h',
        a' = f.comp a → (∀ χ, (τ' χ : A') = f (τ χ : A)) → (s A' a' τ' h').left = spMap f ≫ (s A a τ h).left) ∧
      (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : R →+* A) (ha : ∀ x ∈ maximalIdeal R, a x = 0) (a' : R →+* A') (f : A →+* A')
        (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t (spMap a)) τ h (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P.D.toPre.X),
        a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
        (s A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P ha m₀).left ≫ m₀.φ) ∧
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a : R →+* F) τ h (q : QkPt P.D.toPre F k),
        a = (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) → q.y = 0 → GlobalTheory.UT.IsTor τ q.g →
        GlobalTheory.FlatTors.IsImage P F k q (s F a τ h).left := by
  first | exact @GlobalTheory.ToricTorsionSec.main | exact GlobalTheory.ToricTorsionSec.main | (intros; apply GlobalTheory.ToricTorsionSec.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.TrueCx.FrameOnto

theorem exists_congr_one {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.PosDef) :
    ∃ S : Matrix n n ℂ, IsUnit S.det ∧ Sᴴ * M * S = 1 := by
  classical
  set U : Matrix n n ℂ := (hM.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hD : star U * M * U = diagonal (RCLike.ofReal ∘ hM.1.eigenvalues) := by
    have h := hM.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    exact h
  set c : n → ℂ := fun i => (RCLike.ofReal ((Real.sqrt (hM.1.eigenvalues i))⁻¹) : ℂ) with hc
  refine ⟨U * diagonal c, ?_, ?_⟩
  · rw [det_mul, det_diagonal]
    refine IsUnit.mul (isUnit_det_of_left_inverse (Unitary.coe_star_mul_self _)) ?_
    refine Ne.isUnit (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
    exact RCLike.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr (hM.eigenvalues_pos i)))
  · have hs : (U * diagonal c)ᴴ * M * (U * diagonal c) = diagonal (star c) * (star U * M * U) * diagonal c := by
      rw [conjTranspose_mul, diagonal_conjTranspose, ← star_eq_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [hs, hD, diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hl := hM.eigenvalues_pos i
    have hr : (Real.sqrt (hM.1.eigenvalues i))⁻¹ * hM.1.eigenvalues i * (Real.sqrt (hM.1.eigenvalues i))⁻¹ = 1 := by
      have h0 : Real.sqrt (hM.1.eigenvalues i) ≠ 0 := Real.sqrt_ne_zero'.mpr hl
      have h2 := Real.mul_self_sqrt hl.le
      field_simp
      linarith
    simp only [hc, Pi.star_apply, Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal]
    rw [← RCLike.ofReal_mul, ← RCLike.ofReal_mul, hr, RCLike.ofReal_one]

private lemma posDef_one_sub_mul_conjTranspose_of_posDef {p q : ℕ} {z : Matrix (Fin p) (Fin q) ℂ} (hz : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := by
  have hsd : (1 - z * zᴴ).PosSemidef := by
    haveI : Invertible (1 : Matrix (Fin p) (Fin p) ℂ) := invertibleOne
    haveI : Invertible (1 : Matrix (Fin q) (Fin q) ℂ) := invertibleOne
    have h1 : (fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) z zᴴ 1).PosSemidef := by
      rw [PosDef.fromBlocks₁₁ (A := (1 : Matrix (Fin p) (Fin p) ℂ)) z 1 PosDef.one]
      simpa using hz.posSemidef
    rw [PosDef.fromBlocks₂₂ 1 z (D := (1 : Matrix (Fin q) (Fin q) ℂ)) PosDef.one] at h1
    simpa using h1
  rw [hsd.posDef_iff_det_ne_zero]
  have hu : IsUnit (1 - zᴴ * z).det := (isUnit_iff_isUnit_det _).mp hz.isUnit
  refine (isUnit_det_of_right_inverse (B := 1 + z * (1 - zᴴ * z)⁻¹ * zᴴ) ?_).ne_zero
  have h := mul_nonsing_inv _ hu
  calc (1 - z * zᴴ) * (1 + z * (1 - zᴴ * z)⁻¹ * zᴴ)
      = 1 - z * zᴴ + z * ((1 - zᴴ * z) * (1 - zᴴ * z)⁻¹) * zᴴ := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
          Matrix.one_mul, Matrix.mul_assoc]
    _ = 1 := by
        rw [h, Matrix.mul_one]
        abel

theorem exists_moeb_zero {p q : ℕ} {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    ∃ g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ, gᴴ * Jpq p q * g = Jpq p q ∧ moeb g 0 = z := by
  classical
  have hQ : (1 - zᴴ * z).PosDef := hz
  obtain ⟨S, hSu, hS⟩ := exists_congr_one hQ
  obtain ⟨T, hTu, hT⟩ := exists_congr_one (posDef_one_sub_mul_conjTranspose_of_posDef hQ)
  have hJ : Jpq p q = fromBlocks 1 0 0 (-1) := rfl
  refine ⟨fromBlocks T (z * S) (zᴴ * T) S, ?_, ?_⟩
  · rw [hJ, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
    · refine Eq.trans ?_ hT
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
    · refine Eq.trans ?_ (congrArg Neg.neg hS)
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, conjTranspose_mul, conjTranspose_conjTranspose]
      abel
  · unfold moeb
    rw [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
      Matrix.mul_zero, Matrix.mul_zero, zero_add, zero_add, Matrix.mul_assoc, mul_nonsing_inv _ hSu,
      Matrix.mul_one]

private lemma gram_eq_upper_bounds {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    ReciprocityTheory.ChartRestriction.G.FD.gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma coe_idx_symm_inl {r j : ℕ} (hj : j ≤ r) (a : Fin j) :
    (((idx hj).symm (Sum.inl a) : Fin r) : ℕ) = r - j + a := by
  unfold idx
  simp

private lemma coe_idx_symm_inr {r j : ℕ} (hj : j ≤ r) (b : Fin (r - j)) :
    (((idx hj).symm (Sum.inr b) : Fin r) : ℕ) = b := by
  unfold idx
  simp

private lemma reindex_diagonal_sgn_eq_neg_Jpq {r j : ℕ} (hj : j ≤ r) :
    reindex (idx hj) (idx hj) (diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (r - j) a : ℝ) : ℂ)) =
      -Jpq j (r - j) := by
  have hJ : Jpq j (r - j) = fromBlocks 1 0 0 (-1) := rfl
  rw [hJ]
  ext (a | a) (b | b) <;>
    simp [reindex_apply, diagonal_apply, coe_idx_symm_inl, coe_idx_symm_inr, ReciprocityTheory.ChartRestriction.G.FD.sgn, Matrix.one_apply] <;>
    split_ifs <;> simp

theorem frame_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z ∈ DomI Tau j (r - j), ∃ x ∈ X.dom, domPt X hj κ x = z := by
  intro E _ _ _ r j X hj Tau _ κ hp z hz
  classical
  have hz' : ∀ t, z t ∈ hcDom j (r - j) := hz
  choose g hg hgz using fun t => exists_moeb_zero (hz' t)
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) with hD
  have hDJ : reindex (idx hj) (idx hj) D = -Jpq j (r - j) := by
    rw [hD, hp]
    exact reindex_diagonal_sgn_eq_neg_Jpq hj
  have hD' : D = reindex (idx hj).symm (idx hj).symm (-Jpq j (r - j)) := by
    rw [← hDJ]
    simp [reindex_apply, Matrix.submatrix_submatrix]
  have hDT : Dᵀ = D := by
    rw [hD]
    exact diagonal_transpose _
  have hx0 : ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ).det ≠ 0 ∧
      ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ) = D := fun τ => (X.signature τ).choose_spec
  have hgy : ∀ t, (reindex (idx hj).symm (idx hj).symm (g t))ᴴ * D * reindex (idx hj).symm (idx hj).symm (g t) = D := by
    intro t
    rw [hD']
    simp only [reindex_apply, Equiv.symm_symm, conjTranspose_submatrix, submatrix_mul_equiv]
    rw [Matrix.mul_neg, Matrix.neg_mul, hg t]
  have hT : ∀ y : Matrix (Fin r) (Fin r) ℂ,
      yᵀ * D * y.map (starRingEnd ℂ) = (yᴴ * Dᵀ * y)ᵀ := by
    intro y
    have h1 : (yᴴ)ᵀ = y.map (starRingEnd ℂ) := by
      ext a b
      simp
    rw [transpose_mul, transpose_mul, transpose_transpose, h1, Matrix.mul_assoc]
  let x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r := fun τ =>
    (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)) : Matrix (Fin r) (Fin r) ℂ)
  have hm : ∀ τ, ReciprocityTheory.ChartRestriction.G.FD.mat x τ = ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)) :=
    fun τ => rfl
  have hgram : ∀ τ : X.Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 X.Gm (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = D := by
    intro τ
    have h0 := (hx0 τ).2
    rw [hm, gram_eq_upper_bounds]
    rw [gram_eq_upper_bounds] at h0
    have hre : (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)))ᵀ * X.Gm.map τ.1 *
        (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ * reindex (idx hj).symm (idx hj).symm (g (κ.symm τ))).map (starRingEnd ℂ) =
        (reindex (idx hj).symm (idx hj).symm (g (κ.symm τ)))ᵀ * ((ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ)ᵀ * X.Gm.map τ.1 *
          (ReciprocityTheory.ChartRestriction.G.FD.mat (x0F X) τ).map (starRingEnd ℂ)) *
          (reindex (idx hj).symm (idx hj).symm (g (κ.symm τ))).map (starRingEnd ℂ) := by
      rw [transpose_mul, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    rw [hre, h0, hT, hDT, hgy, hDT]
  refine ⟨x, ?_, ?_⟩
  · show ∀ τ : X.Ψ, (ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i * (ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i).re
    intro τ
    have hsg : ∀ a : ℕ, ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a ≠ 0 := by
      intro a
      unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
      split_ifs <;> norm_num
    refine ⟨?_, ?_⟩
    · intro hdet
      have h := congrArg Matrix.det (hgram τ)
      rw [gram_eq_upper_bounds, det_mul, det_mul, det_transpose, hdet, zero_mul, zero_mul, hD,
        det_diagonal] at h
      exact (Finset.prod_ne_zero_iff.mpr fun (a : Fin r) _ => Complex.ofReal_ne_zero.mpr (hsg a)) h.symm
    · intro i
      have hl : ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i = ((ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i : ℝ) : ℂ) := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.dmin ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.psgn
        rw [hgram τ, hD, submatrix_diagonal _ _ (Fin.castLE_injective _), det_diagonal]
        simp only [Function.comp_apply, Fin.coe_castLE]
        rw [Fin.prod_univ_eq_prod_range (fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ)) (i : ℕ),
          Complex.ofReal_prod]
      have hps : ReciprocityTheory.ChartRestriction.G.FD.psgn X.p0 i ≠ 0 := by
        unfold ReciprocityTheory.ChartRestriction.G.FD.psgn
        exact Finset.prod_ne_zero_iff.mpr fun a _ => hsg a
      rw [hl, Complex.ofReal_re]
      exact mul_self_pos.mpr hps
  · funext t
    have hf : frameCo X hj x (κ t) = g t := by
      unfold frameCo
      rw [hm, ← Matrix.mul_assoc, nonsing_inv_mul _ (hx0 (κ t)).1.isUnit, Matrix.one_mul,
        Equiv.symm_apply_apply]
      simp [reindex_apply, Matrix.submatrix_submatrix]
    show moeb (frameCo X hj x (κ t)) 0 = z t
    rw [hf, hgz t]

end GlobalTheory.TrueCx.FrameOnto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BetaLowerAndSmul
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.PoincareLower

open Topology Filter

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end General

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually
    (fun v : ι × Fin p × Fin q → ℂ => 1 - (unflat v τ)ᴴ * unflat v τ) (fun i j => ?_)
    (fun v => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
  fun_prop

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

end GlobalTheory.PoincareLower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InertiaFix

open GlobalTheory.TorusExt GlobalTheory.UnramTorsion ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] gtGroup

theorem sigma_fixes_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  intro R _ _ D hB F _ _ O φ hφ k hk σ hσ p
  have memO : ∀ x : O, σ (x : F) ∈ O := fun x => by
    have h1 : σ (x : F) - x ∈ O := (O.valuation_le_one_iff _).1 (hσ x x.2).le
    have := O.add_mem _ _ h1 x.2
    simpa using this
  let σO : O →+* O := (σ.toRingHom.comp O.subtype).codRestrict O.toSubring memO
  have hσO : ∀ x : O, ((σO x : O) : F) = σ x := fun _ => rfl
  have hσφ : σO.comp φ = φ := RingHom.ext fun r => Subtype.ext (by
    show σ ((φ r : O) : F) = (φ r : F)
    rw [hφ]; exact σ.commutes _)
  have hres : (IsLocalRing.residue O).comp σO = IsLocalRing.residue O := RingHom.ext fun x => by
    show IsLocalRing.residue O (σO x) = IsLocalRing.residue O x
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply (ValuationSubring.valuation_lt_one_iff O _).2
    have : ((σO x - x : O) : F) = σ (x : F) - x := by push_cast; rfl
    rw [this]; exact hσ x x.2
  have hsub : σ.toRingHom.comp O.subtype = O.subtype.comp σO := rfl
  let ρ : TF (R := R) F ⟶ Over.mk (spMap φ) := Over.homMk (spMap O.subtype) (by
    show spMap O.subtype ≫ spMap φ = jFK (R := R) F ≫ jK R
    rw [jFK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ)
  obtain ⟨b', hb'⟩ := exists_extend O φ ρ rfl p.g.b
  let σ' : Over.mk (spMap φ) ⟶ Over.mk (spMap φ) := Over.homMk (spMap σO) (by
    show spMap σO ≫ spMap φ = spMap φ
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hσφ])
  have := D.P.isAb.proper
  have : D.P.A.left.IsSeparated := ⟨by rw [← terminal.comp_from D.P.A.hom]; infer_instance⟩
  haveI := D.P.isAb.comm
  have hd : IsDominant (spMap O.subtype) := by
    constructor
    exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical O.subtype).2
      (by rw [(RingHom.injective_iff_ker_eq_bot O.subtype).1 Subtype.val_injective]; exact bot_le)
  have hpk : p.g.b ^ k = cP D _ p.y := by
    rw [← nsmul_b, qk_nsmul hB, iota_b]
  have hpow : b' ^ k = cP D _ p.y := by
    have e : ρ ≫ b' ^ k = ρ ≫ cP D _ p.y := by
      rw [comp_cP, ← hpk, ← hb']; exact map_pow (preHom ρ) _ _
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk (spMap φ)).left := (inferInstance : IsReduced (Sp O))
    exact ext_of_isDominant (spMap O.subtype) (congrArg CommaMorphism.left e)
  have hpow' : b' ^ k = (σ' ≫ b') ^ k := by
    have e2 : σ' ≫ b' ^ k = (σ' ≫ b') ^ k := map_pow (preHom σ') b' k
    rw [← e2, hpow, comp_cP]
  have hcl : spMap (IsLocalRing.residue O) ≫ b'.left = spMap (IsLocalRing.residue O) ≫ (σ' ≫ b').left := by
    rw [Over.comp_left, ← Category.assoc]
    congr 1
    show _ = spMap (IsLocalRing.residue O) ≫ spMap σO
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hres]
  have heq : b' = σ' ≫ b' := GlobalTheory.T.smoothCommGroupScheme_eq_of_pow_eq_of_closedPoint (Sp R) D.P.A D.P.isAb.smooth O (spMap φ) k hk b' (σ' ≫ b') hpow'
    (IsLocalRing.ResidueField O) (IsLocalRing.residue O) inferInstance hcl
  rw [← hb', Over.comp_left]
  show spMap σ.toRingHom ≫ spMap O.subtype ≫ b'.left = spMap O.subtype ≫ b'.left
  conv_rhs => rw [heq]
  rw [← Category.assoc, Over.comp_left, ← Category.assoc]
  congr 1
  show spMap σ.toRingHom ≫ spMap O.subtype = spMap O.subtype ≫ spMap σO
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

end GlobalTheory.InertiaFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixes_abelianPart_of_torsionPoint : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R), D.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (O : ValuationSubring F) (φ : R →+* O),
    (∀ r, (φ r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) →
    ∀ (k : ℕ), IsUnit (k : O) → ∀ (σ : F →ₐ[FractionRing R] F), (∀ x ∈ O, O.valuation (σ x - x) < 1) →
    ∀ p : QkPt D F k, spMap σ.toRingHom ≫ p.g.b.left = p.g.b.left := by
  first | exact @GlobalTheory.InertiaFix.sigma_fixes_abelianPart | exact GlobalTheory.InertiaFix.sigma_fixes_abelianPart | (intros; apply GlobalTheory.InertiaFix.sigma_fixes_abelianPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem k_pins_of_fields {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hP : TC.Pins B X)
    (hX : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hSS : t.S = I.S) (hword : HEq t.word fun u : B.Word => u)
    (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst) (hglob : HEq t.glob I.glob) (hO : I.StdO l Z Y.Qp t.O)
    (hpi : ex.errX.piT = X.piT) : t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  have hU : t.MemSideU := by
    intro u
    refine ⟨?_, ?_, ?_⟩
    · show (t.O u I.mu0).mt = _
      rw [hO.mt u I.mu0, hOk.trueColumnChoices_heckeChar_reference_eq_one, tildeQ_one]
      funext j
      split_ifs
      · exact mul_one _
      · rfl
    · intro i c
      show (t.O u I.mu0).dt i c = _
      rw [hO.dt u I.mu0 i c]
      rfl
    · rw [hpi]
      exact memLatAt_std I hOk hP l Z u (t.memObj u) fun i c => hO.lat u I.mu0 i c
  have hPi : t.PiSide := by
    clear hU hO hglob hcst htup hSS hsel hCh
    cases t
    dsimp only at *
    subst hX
    cases hseam
    cases hPr
    cases hword
    intro u
    rw [hpi]
    rfl
  have hC : t.Ch.Ok ∧ MuValTie t.Ch t.glob ∧ ∀ a, (t.cst a).sharp = true := by
    clear hU hPi
    cases t
    dsimp only at *
    subst hX
    cases hPr
    cases hCh
    cases hsel
    subst hSS
    cases htup
    cases hcst
    cases hglob
    exact ⟨hOk.ch_ok, fun j v h => hOk.ch_tied.muVal j v h, fun a => hOk.sharp a⟩
  have hM : t.MtTwTie := by
    clear hU hPi hC
    cases t
    dsimp only at *
    subst hX
    cases hseam
    subst hSS
    cases htup
    refine ⟨(QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)), ⟨fun y => ?_, fun k z hz => ?_⟩,
      fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
      refine ⟨finAf B.host.F B.host.E a, ?_⟩
      exact mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)
    · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
      show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
      rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
      refine mk_eq_of_snd_eq B.host I.SQ ?_
      show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
      rw [afIso_tmul_one]
      rfl
    · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
        (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).2.2 μ).1
      show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
      exact Units.ext ((hOk.xi_reads μ).apply _ x rfl)
    · rw [hO.mt u μ]
      rfl
  exact ⟨⟨hC.1, hC.2.1, hPi, fun u _ => hU u⟩, hU, hM, hC.2.2⟩

theorem k_pins_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS hpi
  exact k_pins_of_fields I l Z t hOk hP hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.word hS.tup hS.cst hS.glob hS.O hpi

end GlobalTheory.Mem.Col2.TC

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelChoicesStandardTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelChoices_standard_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  first | exact @GlobalTheory.Mem.Col2.TC.k_pins_tie | exact GlobalTheory.Mem.Col2.TC.k_pins_tie | (intros; apply GlobalTheory.Mem.Col2.TC.k_pins_tie <;> assumption)
end
end
