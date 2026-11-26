module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiAtTransport
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemCosetInOfRes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrsFBaseEqSelf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.AdForm GlobalTheory.QTw
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QTw

theorem frsF_base_eq_self : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀), A.Is → I.Ok → ∀ (P : BadPr I a), P.1 ∉ (B.primes X).vGs → ∀ (i : ℕ), i ≤ B.R.m → ∀ (β : Ch₀ i), (∀ v : HeightOneSpectrum (𝓞 B.host.F), ((B.T u : ℕ) : 𝓞 B.host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) (A.kb i β) = 1) → ∀ (x : Formalism.L2.Col.Sp B.fields.E (B.R.N i)), Formalism.L2.Col.frsF I.sel (I.tup a) (A.p0 i β).1.1 P x = x := by
  intro B X I l Z u a Ch₀ A hA hI P hP i hi β hv x
  have hQ : P.1 ∈ I.Q a := by
    rcases Finset.mem_union.1 P.2 with h | h
    · exact absurd h hP
    · exact h
  have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
    intro hm
    apply GlobalTheory.KerT.T_notMem_rowSG (I.tup a) (GlobalTheory.BasePrimes.primes_ok B X).1 hI.sel_ok (hI.T_mem u) P.1 P.2
    have := Ideal.mem_comap.1 hm
    simpa [map_natCast] using this
  have hk := hv _ hT
  have hpt := (hA.base i hi β).1
  have hfr := hpt.fr ⟨P.1, hSQ⟩
  rw [frsF_eq_ptFr, ← extTo_fr I.SQ _ ⟨P.1, hSQ⟩]
  set f := (extTo I.SQ (A.p0 i β).1.1).fr ⟨P.1, hSQ⟩ with hf
  have key : ∀ j : Fin (B.R.N i), f (Pi.single j 1) = Pi.single j 1 := by
    intro j
    funext r
    have h1 := hfr r j
    rw [GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_one P.1 hk r j] at h1
    apply (algebraMap B.fields.E (P.1.adicCompletion B.fields.E)).injective
    rw [← h1, Pi.single_apply]
    split_ifs <;> simp
  have : (f : Formalism.L2.Col.Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Formalism.L2.Col.Sp B.fields.E (B.R.N i)) = LinearMap.id :=
    LinearMap.pi_ext' fun j => LinearMap.ext_ring (key j)
  exact congrArg (fun g => g x) this

end GlobalTheory.QTw
end

noncomputable section

namespace GlobalTheory.PenChart

theorem normal_rep {G D A : Type} [Group G] [MulAction G D] (f : D → A) (pref : D → Prop)
    (h : ∀ q, pref q ↔ f q = Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩))
    (d d' : D) (hd : ∀ g : G, f (g • d') = f (g • d)) :
    f (GlobalTheory.Mem.Col2.prefRep pref (Quotient.mk (MulAction.orbitRel G D) d')) =
      f (GlobalTheory.Mem.Col2.prefRep pref (Quotient.mk (MulAction.orbitRel G D) d)) := by
  have h1 : ∀ (q : D) (g₀ : G), (fun r => ∃ g : G, r = f (g • g₀ • q)) = fun r => ∃ g : G, r = f (g • q) := fun q g₀ => by
    funext r
    refine propext ⟨fun ⟨g, e⟩ => ⟨g * g₀, by rw [mul_smul]; exact e⟩, fun ⟨g, e⟩ => ⟨g * g₀⁻¹, by
      rw [mul_smul, inv_smul_smul]; exact e⟩⟩
  have h2 : ∀ q : D, f (GlobalTheory.Mem.Col2.prefRep pref (Quotient.mk (MulAction.orbitRel G D) q)) =
      Classical.epsilon (p := fun r => ∃ g : G, r = f (g • q)) (h := ⟨f q⟩) := fun q => by
    have hex : ∃ p, Quotient.mk (MulAction.orbitRel G D) p = Quotient.mk (MulAction.orbitRel G D) q ∧ pref p := by
      obtain ⟨g, hg⟩ := Classical.epsilon_spec (p := fun r => ∃ g : G, r = f (g • q)) ⟨f q, 1, by rw [one_smul]⟩
      refine ⟨g • q, Quotient.sound ⟨g, rfl⟩, (h _).2 ?_⟩
      rw [h1]
      exact hg.symm
    unfold GlobalTheory.Mem.Col2.prefRep
    rw [dite_eq_left hex]
    obtain ⟨g, hg⟩ : ∃ g : G, g • q = hex.choose := Quotient.exact hex.choose_spec.1
    have h3 := (h _).1 hex.choose_spec.2
    rw [h3, ← hg, h1]
  rw [h2, h2]
  simp only [hd]

section Local

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped Classical

section Vec

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_eN (k : ℕ) (l : Fin n) : IntAt P (Loc.eN E n k l) := by
  unfold Loc.eN
  split_ifs
  · simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P 1
  · simpa using GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.intAt_int P 0

theorem redV_eN (k : ℕ) : redV P (Loc.eN E n k) = Loc.eN (𝓞 E ⧸ P.asIdeal) n k := by
  funext l
  unfold redV Loc.eN
  split_ifs
  · exact redP_one
  · exact redP_zero

theorem inv_smul_sub_mem (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k : ℕ} {x : Sp E n} (hx : ∀ l, IntAt P (x l))
    (hr : redV P x = Loc.eN (𝓞 E ⧸ P.asIdeal) n k) : (qOf P : E)⁻¹ • (x - Loc.eN E n k) ∈ stdAt E n P := by
  refine TopStep.mem_stdAt.2 fun l => ?_
  have h := TopStep.intAt_div_of_redP hq (TopStep.intAt_sub (hx l) (intAt_eN k l))
    ((TopStep.reduction_sub (hx l) (intAt_eN k l)).trans (sub_eq_zero.2 (congrFun (hr.trans (redV_eN k).symm) l)))
  rwa [div_eq_inv_mul] at h

end Vec

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

def Good (p : PtAt R sel mu cst u j) : Prop :=
  ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs → (qOf P.1 : X.E)⁻¹ • Loc.eN X.E (R.N j) R.k ∈ cosetIn p P

theorem mem_cosetIn {p : PtAt R sel mu cst u j} {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs) {z : Sp X.E (R.N j)} :
    z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2, z - (frsF sel mu p.1.1 P).symm y ∈ stdAt X.E (R.N j) P.1 := by
  simp only [cosetIn, if_pos hP, pow_zero, inv_one, one_smul, Set.mem_setOf_eq]

theorem rep_mem (h : j + 1 = R.m) (p : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) :
    (frsF sel mu p.1.1 P).symm (repY p.1.2) ∈ cosetIn p P :=
  ⟨_, p.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩

theorem mem_of_sub {p : PtAt R sel mu cst u j} {P : rowSG Pr sel mu} {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P)
    (h : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (z' - z) ∈ stdAt X.E (R.N j) P.1) : z' ∈ cosetIn p P := by
  obtain ⟨y, hy, h2⟩ := hz
  refine ⟨y, hy, ?_⟩
  have := add_mem h h2
  rwa [← smul_add, sub_add_sub_cancel] at this

theorem sub_of_mem (h : j + 1 = R.m) {p : PtAt R sel mu cst u j} {P : rowSG Pr sel mu} {z z' : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P)
    (hz' : z' ∈ cosetIn p P) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (z' - z) ∈ stdAt X.E (R.N j) P.1 :=
  TopStep.mem_stdAt.2 fun l => GlobalTheory.TwU.AtTrue.Cl.sameCoset_of_mem_cosetIn p h P hz' hz l

theorem cosetIn_eq_of_mem (h : j + 1 = R.m) {p p' : PtAt R sel mu cst u j} {P : rowSG Pr sel mu}
    {z : Sp X.E (R.N j)} (hz : z ∈ cosetIn p P) (hz' : z ∈ cosetIn p' P) : cosetIn p P = cosetIn p' P :=
  Set.Subset.antisymm (fun _ hx => mem_of_sub hz' (sub_of_mem h hz hx)) fun _ hx => mem_of_sub hz (sub_of_mem h hz' hx)

theorem mem_cosetIn_of_res (h : j + 1 = R.m) (p : PtAt R sel mu cst u j) {P : rowSG Pr sel mu} (hP : P.1 ∈ Pr.vGs)
    (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hp : ∀ l, IntAt P.1 ((qOf P.1 : X.E) * (frsF sel mu p.1.1 P).symm (repY p.1.2) l) ∧
      redP P.1 ((qOf P.1 : X.E) * (frsF sel mu p.1.1 P).symm (repY p.1.2) l) = if l.1 = R.k then 1 else 0) :
    (qOf P.1 : X.E)⁻¹ • Loc.eN X.E (R.N j) R.k ∈ cosetIn p P := by
  have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  have h1 := inv_smul_sub_mem (x := (qOf P.1 : X.E) • (frsF sel mu p.1.1 P).symm (repY p.1.2)) (k := R.k) hq (fun l => (hp l).1)
    (funext fun l => (hp l).2)
  refine (mem_cosetIn hP).2 ⟨_, p.repY_mem h, ?_⟩
  rw [smul_sub, inv_smul_smul₀ hq0] at h1
  simpa using neg_mem h1

variable (Λ : LevFam X.E X.K (R.N j) Pr.vGs) (Θ : LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))

theorem good_smul (hq : ∀ P : rowSG Pr sel mu, ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hΛ : ∀ h ∈ Λ.grp, ∀ w : Pr.vGs, (h w).1.mulVec (Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k) =
      Loc.eN (𝓞 X.E ⧸ w.1.asIdeal) (R.N j) R.k) (g : FrmG Λ Θ) (p p' : PtAt R sel mu cst u j)
    (e1 : p'.1.1 = g • p.1.1) (e2 : p'.1.2 = (fun v => g.1.1 v) '' p.1.2) (hp : Good p) : Good p' := by
  intro P hP
  obtain ⟨y, hy, h1⟩ := (mem_cosetIn hP).1 (hp P hP)
  obtain ⟨κ, hκ, hr⟩ := frsF_smul sel mu p.1.1 Λ Θ g P hP
  have he : Loc.eN X.E (R.N j) R.k ∈ stdAt X.E (R.N j) P.1 := TopStep.mem_stdAt.2 (intAt_eN _)
  have h2 := inv_smul_sub_mem (x := κ.1 (Loc.eN X.E (R.N j) R.k)) (k := R.k) (hq P) (TopStep.mem_stdAt.1 ((κ.2 _).2 he)) (by
    rw [hr _ he, redV_eN]
    exact hΛ _ (inv_mem g.2.1.2) ⟨P.1, hP⟩)
  refine (mem_cosetIn hP).2 ⟨g.1.1 y, e2 ▸ ⟨y, hy, rfl⟩, (κ.2 _).1 ?_⟩
  have e : κ.1 ((frsF sel mu p'.1.1 P).symm (g.1.1 y)) = (frsF sel mu p.1.1 P).symm y := by
    rw [LinearEquiv.eq_symm_apply]
    apply g.1.1.injective
    have h3 := (frsF sel mu p'.1.1 P).apply_symm_apply (g.1.1 y)
    rw [e1] at h3 ⊢
    rw [hκ] at h3
    rw [hκ]
    exact h3
  rw [map_sub, e, map_smul]
  convert add_mem h2 h1 using 1
  rw [smul_sub]
  abel

theorem mem_cosetIn_smul (g : FrmG Λ Θ) (p p' : PtAt R sel mu cst u j)
    (e1 : p'.1.1 = g • p.1.1) (e2 : p'.1.2 = (fun v => g.1.1 v) '' p.1.2) (P : rowSG Pr sel mu) (hP : P.1 ∉ Pr.vGs)
    (hQ : P.1 ∈ QE sel (mu : Chr X.F X.E X.K)) (z : Sp X.E (R.N j)) :
    (g.2.2.1 ⟨P.1, hQ⟩).1 z ∈ cosetIn p' P ↔ z ∈ cosetIn p P := by
  set κ := g.2.2.1 ⟨P.1, hQ⟩ with hκ
  have hf : ∀ y, (frsF sel mu p'.1.1 P).symm (g.1.1 y) = κ.1 ((frsF sel mu p.1.1 P).symm y) := fun y => by
    rw [LinearEquiv.symm_apply_eq, e1]
    unfold frsF
    rw [dite_eq_right hP, dite_eq_right hP]
    show _ = g.1.1 (p.1.1.fr ⟨P.1, hQ⟩ (κ.1.symm (κ.1 ((p.1.1.fr ⟨P.1, hQ⟩).symm y))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
  simp only [cosetIn, Set.mem_setOf_eq, e2]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
    rw [hf, ← map_sub, ← map_smul] at h
    exact ⟨y, hy, (κ.2 _).1 h⟩
  · rintro ⟨y, hy, h⟩
    refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
    rw [hf, ← map_sub, ← map_smul]
    exact (κ.2 _).2 h

theorem exists_pt (h : j + 1 = R.m) (d : ChPt (R := R) sel mu u j) (z : rowSG Pr sel mu → Sp X.E (R.N j))
    (hz : ∀ P, P.1 ∉ Pr.vGs → (qOf P.1 : X.E) ^ cst.M • z P ∈ stdAt X.E (R.N j) P.1) :
    ∃ p : PtAt R sel mu cst u j, Good p ∧ ∀ P, P.1 ∉ Pr.vGs → z P ∈ cosetIn p P := by
  let z' : rowSG Pr sel mu → Sp X.E (R.N j) := fun P => if P.1 ∈ Pr.vGs then (qOf P.1 : X.E)⁻¹ • Loc.eN X.E (R.N j) R.k else z P
  obtain ⟨y, hy⟩ := GlobalTheory.CplCosetPt.exists_sameCoset_frames sel mu cst (fun P => frsF sel mu d P) z'
  have hd : ∀ P, ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • ((frsF sel mu d P).symm y - z' P) ∈
      stdAt X.E (R.N j) P.1 := fun P => TopStep.mem_stdAt.2 fun l => hy P l
  have hy' : y ∈ locLat (rowSG Pr sel mu) d.deco.1.N (fun P => if P.1 ∈ Pr.vGs then -1 else -(cst.M : ℤ)) := by
    refine (mem_locLat _ _ _ _).2 fun P => ?_
    have hq0 : (qOf P.1 : X.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
    have hn : ∀ (n : ℕ) v, v ∈ stdAt X.E (R.N j) P.1 → (qOf P.1 : X.E) ^ n • v ∈ stdAt X.E (R.N j) P.1 := fun n v hv => by
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
      exact nsmul_mem hv _
    have h0 := hd P
    by_cases hP : P.1 ∈ Pr.vGs
    · simp only [z', if_pos hP, pow_zero, inv_one, one_smul] at h0
      have h2 := GlobalTheory.BaseCosetPt.frsF_mem d P (add_mem (hn 1 _ h0) (TopStep.mem_stdAt.2 (intAt_eN R.k)))
      rw [pow_one, smul_sub, smul_inv_smul₀ hq0, sub_add_cancel, map_smul, LinearEquiv.apply_symm_apply] at h2
      simpa [hP] using h2
    · simp only [z', if_neg hP] at h0
      have h2 := GlobalTheory.BaseCosetPt.frsF_mem d P (add_mem (hn (cst.M + cst.M) _ h0) (hz P hP))
      rw [smul_smul, pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq0), mul_one, smul_sub, sub_add_cancel, map_smul,
        LinearEquiv.apply_symm_apply] at h2
      simpa [hP] using h2
  have key : ∀ p : PtAt R sel mu cst u j, p.1.1 = d → y ∈ p.1.2 → ∀ P, z' P ∈ cosetIn p P := by
    rintro p rfl hp P
    refine ⟨y, hp, ?_⟩
    have := neg_mem (hd P)
    rwa [← smul_neg, neg_sub] at this
  let p : PtAt R sel mu cst u j :=
    ⟨(d, {z | z - y ∈ locLat (rowSG Pr sel mu) d.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), by
      rw [ysAt_ys_of_eq sel mu cst h]
      exact ⟨y, hy', rfl⟩⟩
  have hp := key p rfl (by simp [p])
  refine ⟨p, fun P hP => ?_, fun P hP => ?_⟩
  · simpa only [z', if_pos hP] using hp P
  · simpa only [z', if_neg hP] using hp P

end Local

section True

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.AdForm
open scoped Classical
attribute [local instance] GlobalTheory.Mem.Col2.starE

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {a : I.ι} {j : ℕ}

theorem idx_eq (hI : I.Ok) (hj : j + 1 = B.R.m) (b b' : Idx I.sel (I.tup a) (I.idx a) j) : b = b' := by
  obtain rfl : j = B.R.m - 2 + 1 := by have := B.R.two_le_m; omega
  obtain ⟨b₀, hb⟩ := (hI.idx_ok a).last_uniq
  rw [← b.of_get (by omega) (by omega), ← b'.of_get (by omega) (by omega), hb (b.get _), hb (b'.get _)]

abbrev levQ (I : TC B X) (a : I.ι) (j : ℕ) (b : Idx I.sel (I.tup a) (I.idx a) j) :=
  levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b

theorem good_act (hI : I.Ok) (ht : TC.IsTw I) (hj : j + 1 = B.R.m) (b : (I.stp u a j).β) (g : (I.stp u a j).G b) (p : (I.stp u a j).D b)
    (hp : Good p) : Good ((I.stp u a j).act b g p) := by
  have hΛ : levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = colLevSym I.Ch j := by
    have e : ∀ al, (I.idx a).levG j al = colLevSym I.Ch j := by
      rw [(ht a).2]
      exact fun _ => rfl
    unfold levGAt
    rw [← b.some_get (by omega)]
    exact e _
  refine good_smul (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b) (levQ I a j b) (fun P => (degOne_of_ok hI a P).2) ?_ g p _ rfl rfl hp
  rw [hΛ]
  obtain ⟨m2, rfl⟩ : ∃ m2, j = m2 + 1 := ⟨j - 1, by have := B.R.two_le_m; omega⟩
  exact fixE_colLevSym I.Ch hj.symm

theorem mem_act (b : (I.stp u a j).β) (g : (I.stp u a j).G b) (p : (I.stp u a j).D b) (P : rowSG (B.primes X) I.sel (I.tup a))
    (hP : P.1 ∉ (B.primes X).vGs) (hQ : P.1 ∈ I.Q a) (z) :
    (g.2.2.1 ⟨P.1, hQ⟩).1 z ∈ cosetIn ((I.stp u a j).act b g p) P ↔ z ∈ cosetIn p P :=
  mem_cosetIn_smul (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b) (levQ I a j b) g p _ rfl rfl P hP hQ z

theorem rep_congr (hI : I.Ok) (ht : TC.IsTw I) (hj : j + 1 = B.R.m) (b : (I.stp u a j).β) (d d' : (I.stp u a j).D b) (hd : Good d)
    (hd' : Good d') (h : cosetIn d = cosetIn d') :
    cosetIn ((I.stp u a j).rep ((I.stp u a j).cl b d')) = cosetIn ((I.stp u a j).rep ((I.stp u a j).cl b d)) := by
  refine @normal_rep ((I.stp0 u a j).G b) ((I.stp0 u a j).D b) _ _ ((I.stp0 u a j).actD b) (fun q => cosetIn q) (I.pref u a j b)
      (fun q => ⟨fun hq => hq.2.1 hj, fun hq => ⟨fun h0 => by have := B.R.two_le_m; omega, fun _ => hq, fun h0 => by omega⟩⟩)
      d d' fun g => funext fun P => ?_
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · exact cosetIn_eq_of_mem hj (good_act hI ht hj b g d' hd' P hP) (good_act hI ht hj b g d hd P hP)
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
    have h1 := rep_mem hj d P
    exact cosetIn_eq_of_mem hj ((mem_act b g d' P hP hQ _).2 (h ▸ h1)) ((mem_act b g d P hP hQ _).2 h1)

variable {l : I.Laws} {Z : TC.Later B (I.cols l)} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}

theorem chart_ext (hI : I.Ok) (ht : TC.IsTw I) (hA : A.Is) (hj : j + 1 = B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) (β β' : Ch j)
    (hβ : Good (A.p0 j β)) (hβ' : Good (A.p0 j β'))
    (h : ∀ (P : rowSG (B.primes X) I.sel (I.tup a)) (hQ : P.1 ∈ I.Q a), ∃ κ ∈ (levQ I a j b ⟨P.1, hQ⟩).H,
      ∃ z ∈ cosetIn (A.p0 j β) P, κ.1 z ∈ cosetIn (A.p0 j β') P) : β = β' := by
  have hi : j ≤ B.R.m := by omega
  obtain ⟨⟨b₁, c⟩, rfl⟩ := hA.chOf_onto j hi β
  obtain ⟨⟨b₂, c'⟩, rfl⟩ := hA.chOf_onto j hi β'
  obtain rfl := idx_eq hI hj b b₁
  obtain rfl := idx_eq hI hj b b₂
  have h1 := (hA.rep j hi ⟨b, c⟩).2
  have h2 := (hA.rep j hi ⟨b, c'⟩).2
  unfold Good at hβ hβ'
  rw [← h1] at hβ h
  rw [← h2] at hβ' h
  choose κ hκ z hz hz' using fun P : I.Q a => h ⟨P.1, Finset.mem_union_right _ P.2⟩ P.2
  let g : (I.stp u a j).G b := (1, 1, ⟨κ, fun P _ => hκ P⟩)
  have hg := good_act hI ht hj b g _ hβ
  have e := rep_congr hI ht hj b _ _ hg hβ' (funext fun P => by
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · exact cosetIn_eq_of_mem hj (hg P hP) (hβ' P hP)
    · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.mp P.2).resolve_left hP
      exact cosetIn_eq_of_mem hj ((mem_act b g _ P hP hQ _).2 (hz ⟨P.1, hQ⟩)) (hz' ⟨P.1, hQ⟩))
  have e1 : (I.stp u a j).cl b ((I.stp u a j).act b g ((I.stp u a j).rep ⟨b, c⟩)) = ⟨b, c⟩ :=
    congrArg (Sigma.mk b) (Eq.trans (Quotient.sound (s := @MulAction.orbitRel _ _ _ ((I.stp u a j).actD b)) ⟨g, rfl⟩) ((I.stp u a j).rp_spec b c))
  have e2 : (I.stp u a j).cl b ((I.stp u a j).rep ⟨b, c'⟩) = ⟨b, c'⟩ := congrArg (Sigma.mk b) ((I.stp u a j).rp_spec b c')
  rw [e1, e2] at e
  exact ((hA.reads j hi).key _ _).2 ⟨rfl, e.symm⟩

theorem exists_chart (hI : I.Ok) (ht : TC.IsTw I) (hA : A.Is) (hj : j + 1 = B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j)
    (z : rowSG (B.primes X) I.sel (I.tup a) → Sp B.fields.E (B.R.N j))
    (hz : ∀ P, P.1 ∉ (B.primes X).vGs → (qOf P.1 : B.fields.E) ^ (I.cst a).M • z P ∈ stdAt B.fields.E (B.R.N j) P.1) :
    ∃ β : Ch j, Good (A.p0 j β) ∧ ∀ (P : rowSG (B.primes X) I.sel (I.tup a)) (hQ : P.1 ∈ I.Q a),
      ∃ κ ∈ (levQ I a j b ⟨P.1, hQ⟩).H, κ.1 (z P) ∈ cosetIn (A.p0 j β) P := by
  have hi : j ≤ B.R.m := by omega
  have : NeZero (B.R.N j) := ⟨(B.R.N_pos j).ne'⟩
  obtain ⟨p, hp, hp'⟩ := exists_pt (cst := I.cst a) (u := u) hj (DecoF.base _ _ _ _ _) z hz
  obtain ⟨g, hg⟩ := Quotient.exact ((I.stp u a j).rp_spec b (Quotient.mk _ p))
  have hg' : (I.stp u a j).act b g p = (I.stp u a j).rep ((I.stp u a j).cl b p) := hg
  have h1 := (hA.rep j hi ((I.stp u a j).cl b p)).2
  rw [← hg'] at h1
  refine ⟨A.chOf j ((I.stp u a j).cl b p), ?_, fun P hQ => ?_⟩
  · unfold Good
    rw [← h1]
    exact good_act hI ht hj b g p hp
  · have hP := Q_notMem_of_ok hI a _ hQ
    rw [← h1]
    exact ⟨g.2.2.1 ⟨P.1, hQ⟩, g.2.2.2 _ (Set.mem_univ _), (mem_act b g p P hP hQ _).2 (hp' P hP)⟩

theorem good_of_xi (hI : I.Ok) (ht : TC.IsTw I) {i : ℕ} (hi : i + 1 + 1 = B.R.m) (h : i + 1 ≤ B.R.m) (α : Ch i) (γ : Ch (i + 1)) (z)
    (hz : A.xi i h α γ z ≠ 0) : Good (A.p0 (i + 1) γ) := by
  have hh : ∀ (al : (I.idx a).β i) P, P.1 ∈ (B.primes X).vGs → (I.idx a).h i al P = 1 := by
    rw [(ht a).2]
    exact twSt_h_g _ _ _ _ _ i
  have hx : xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i (A.b0 i α) (A.b0 (i + 1) γ) (A.p0 i α) (A.p0 (i + 1) γ) ≠ 0 := fun e =>
    hz (by unfold TwDat.xi; rw [e]; exact map_zero _)
  exact fun P hP => mem_cosetIn_of_res hi _ hP (degOne_of_ok hI a P).2 (Keep.res_of_xiAt hi (hI.sharp _) hh hx P hP)


set_option maxHeartbeats 1600000 in
theorem repY_mem (hI : I.Ok) (hA : A.Is) (hj : j + 1 = B.R.m) (β : Ch j) (hk : A.kb j β = TC.kStd X u (B.R.N j))
    (P : rowSG (B.primes X) I.sel (I.tup a)) : repY (A.p0 j β).1.2 ∈ cosetIn (A.p0 j β) P := by
  have hi : j ≤ B.R.m := by omega
  have h0 := rep_mem hj (A.p0 j β) P
  have hv := (MemChart.kStd_spec l.pr u (B.R.N j)).2.1
  rw [← hk] at hv
  by_cases hP : P.1 ∈ (B.primes X).vGs
  swap
  · have e := GlobalTheory.QTw.frsF_base_eq_self A hA hI P hP j hi β hv
    have e' : (frsF I.sel (I.tup a) (A.p0 j β).1.1 P).symm (repY (A.p0 j β).1.2) = repY (A.p0 j β).1.2 := by
      rw [LinearEquiv.symm_apply_eq, e]
    rwa [e'] at h0
  have hT : ((B.T u : ℕ) : 𝓞 B.host.F) ∉ (P.1.under (𝓞 B.host.F)).asIdeal := by
    intro hm
    apply GlobalTheory.KerT.T_notMem_rowSG (I.tup a) (GlobalTheory.BasePrimes.primes_ok B X).1 hI.sel_ok (hI.T_mem u) P.1 P.2
    have := Ideal.mem_comap.1 hm
    simpa [map_natCast] using this
  obtain ⟨hpt, hN⟩ := hA.base j hi β
  set f := frsF I.sel (I.tup a) (A.p0 j β).1.1 P with hf
  have hl : TopStep.IsLiftFr (A.p0 j β).1.1.deco.1 ⟨P.1, hP⟩ f := by
    rw [hf]
    unfold frsF
    rw [dite_eq_left hP]
    exact TopStep.liftFr_spec (A.p0 j β).1.1.deco.2 _
  have hs : ∀ z, f z ∈ stdAt B.fields.E (B.R.N j) P.1 ↔ z ∈ stdAt B.fields.E (B.R.N j) P.1 := fun z => by
    have := hl.1 z; rwa [Deco.at, hN] at this
  have hc := GlobalTheory.Transport.Pen.lift_cong hpt ⟨P.1, hP⟩ hl
  have h1 : ColAd.locM P.1 (A.kb j β)⁻¹ = 1 := by
    refine Matrix.ext fun r s => ?_
    rw [Matrix.one_apply]
    exact ZeroMove.adAt_entry_one P.1 (by rw [map_inv, hv _ hT, inv_one]) r s
  rw [h1, Matrix.one_mul] at hc
  have h2 := ColAd.mem_prinCong_of_sm (c := 1) (⟨f, hs⟩ : GLint B.fields.E (B.R.N j) P.1) fun r s => by
    unfold ColAd.dep
    rw [pow_one]
    exact GlobalTheory.Transport.Pen.val_le_q (degOne_of_ok hI a P).2 (hc r s)
  have hq0 : (qOf P.1 : B.fields.E) ≠ 0 := GlobalTheory.Proof.NormalFormAtPrime.qOf_ne_zero P.1
  obtain ⟨y, hy, hY⟩ := (A.p0 j β).mem_ybSet hj
  have h3 := (A.p0 j β).repY_mem hj
  set z := repY (A.p0 j β).1.2 with hz
  rw [hY] at h3
  have h4 := (mem_locLat _ _ _ _).1 hy P
  have h5 := (mem_locLat _ _ _ _).1 h3 P
  simp only [if_pos hP, zpow_zero, inv_one, one_smul, _root_.zpow_neg_one, inv_inv, hN] at h4 h5
  have h6 : (qOf P.1 : B.fields.E) • f.symm z ∈ stdAt B.fields.E (B.R.N j) P.1 := by
    rw [← hs, map_smul, LinearEquiv.apply_symm_apply, ← add_sub_cancel y z, smul_add]
    refine add_mem h4 ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem h5 _
  have h7 := h2 _ h6
  refine mem_of_sub h0 ?_
  rw [if_pos hP, pow_zero, inv_one, one_smul]
  convert h7 using 1
  show _ = _ • (f _ - _)
  rw [map_smul, LinearEquiv.apply_symm_apply, ← smul_sub, pow_one, inv_smul_smul₀ hq0]

end True

end GlobalTheory.PenChart
end
end

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PenChart

section Orbits
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]

theorem corner_mul (g h : GL (n ⊕ Fin 0) k) : (g * h).val.toBlocks₁₁ = g.val.toBlocks₁₁ * h.val.toBlocks₁₁ := by
  ext i j
  rw [Units.val_mul]
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply]

theorem corner_one : (1 : GL (n ⊕ Fin 0) k).val.toBlocks₁₁ = 1 := by
  ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]

theorem box_stable {g : GL (n ⊕ Fin 0) k} (hg : g ∈ KO k _) (a : kˣ) {y : n → k} (hy : y ∈ box n a) :
    g.val.toBlocks₁₁ *ᵥ y ∈ box n a := fun i => by
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul]
  exact mul_le_of_le_one_of_le ((mem_KO.1 hg).1 (Sum.inl i) (Sum.inl j)) (hy j)

theorem sameOrb_equiv {J : Subgroup (GL (n ⊕ Fin 0) k)} (hJ : J ≤ KO k _) (c : kˣ) : Equivalence (SameOrb J (box n c)) := by
  refine ⟨fun yb => ?_, fun {yb yb'} H => ?_, fun {yb yb' yb''} H H' => ?_⟩
  · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ yb
    exact ⟨1, one_mem _, y, rfl, by rw [corner_one, one_mulVec]⟩
  · obtain ⟨g, hg, y, rfl, e⟩ := H
    refine ⟨g⁻¹, inv_mem hg, g.val.toBlocks₁₁ *ᵥ y, e, ?_⟩
    rw [mulVec_mulVec, ← corner_mul, inv_mul_cancel, corner_one, one_mulVec]
  · obtain ⟨g, hg, y, rfl, e1⟩ := H
    obtain ⟨h, hh, y', e2, e3⟩ := H'
    refine ⟨h * g, mul_mem hh hg, y, rfl, ?_⟩
    rw [← e3, corner_mul, ← mulVec_mulVec, Submodule.Quotient.eq, ← mulVec_sub]
    rw [← e1] at e2
    exact box_stable (hJ hh) _ ((Submodule.Quotient.eq _).1 e2.symm)

theorem box_le {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (M : ℕ) {y : n → k} (hy : y ∈ box n (ϖ ^ M)) : y ∈ box n (ϖ ^ M)⁻¹ := fun i => by
  have h1 : valuation k ((ϖ ^ M : kˣ) : k) ≤ 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' ((hϖ _).2 le_rfl).le _
  refine ((hy i).trans h1).trans ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀]
  exact (one_le_inv₀ ((Valuation.pos_iff _).2 (Units.ne_zero _))).2 h1

theorem mul_int_iff (c : kˣ) (x : k) : (c : k) * x ∈ 𝒪[k] ↔ valuation k x ≤ valuation k ((c⁻¹ : kˣ) : k) := by
  rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← mul_one (_⁻¹),
    le_inv_mul_iff₀ ((Valuation.pos_iff _).2 (Units.ne_zero _))]

theorem inv_sub_inv_int {ϖ : kˣ} (hϖ : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {q : k} (h : valuation k ((ϖ : k) - q) < valuation k (ϖ : k)) :
    q⁻¹ - ((ϖ⁻¹ : kˣ) : k) ∈ 𝒪[k] := by
  have h0 : 0 < valuation k (ϖ : k) := (Valuation.pos_iff _).2 (Units.ne_zero _)
  have hq : valuation k q = valuation k (ϖ : k) := Valuation.map_eq_of_sub_lt _ (by rwa [Valuation.map_sub_swap])
  have hq0 : q ≠ 0 := fun e => by rw [e, map_zero] at hq; exact h0.ne hq
  have h1 := (hϖ (((ϖ : k) - q) / ϖ)).1 (by rw [map_div₀]; exact (div_lt_one₀ h0).2 h)
  have e : q⁻¹ - ((ϖ⁻¹ : kˣ) : k) = ((ϖ : k) - q) / ϖ / q := by
    rw [Units.val_inv_eq_inv_val]
    have := ϖ.ne_zero
    field_simp
  rw [e, Valuation.mem_integer_iff, map_div₀, hq]
  exact (div_le_one₀ h0).2 h1

end Orbits

section Restr
variable {D : D7} {c : Comm D} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl D.host.E} {G : QGeo v Bs PP} {χ : ℕ → (AE D)ˣ →* Circle}

def InBox (E : QExt G χ) (j : ℕ) (y : E.Ch j) : Prop :=
  ∀ h : j = G.s + 1, ∃ z ∈ box _ (G.ϖ ^ E.M)⁻¹, E.cos (h ▸ y) = Submodule.Quotient.mk z

theorem inBox_of_orb (E : QExt G χ) {y : E.Ch (G.s + 1)} {z} (hz : z ∈ box _ (G.ϖ ^ E.M)⁻¹)
    (h : SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ E.M)) (E.cos y) (Submodule.Quotient.mk z)) :
    InBox E (G.s + 1) y := by
  obtain ⟨g, hg, y', e1, e2⟩ := (sameOrb_equiv (E.le _ _ _) _).symm h
  refine fun _ => ⟨_, box_stable (E.le _ _ _ hg) _ ?_, e2.symm⟩
  have := add_mem (box_le G.unif _ ((Submodule.Quotient.eq _).1 e1)) hz
  rwa [sub_add_cancel] at this


set_option maxHeartbeats 4000000 in
@[reducible] def restr (E : QExt G χ) : QExt G χ :=
  { E with
    Ch := fun j => {y : E.Ch j // InBox E j y}
    fC := fun _ => Subtype.fintype _
    rep := fun j d h y => E.rep j d h y.1
    rep_bij := fun j d h => (E.rep_bij j d h).comp
      (Equiv.subtypeUnivEquiv (p := InBox E j) fun _ _ => by omega).bijective.bijOn_univ
    cos := fun y => E.cos y.1
    cos_inj := fun _ _ h => Subtype.ext (E.cos_inj _ _ h)
    cos_all := fun z hz => (E.cos_all z hz).elim fun y hy => ⟨⟨y, inBox_of_orb E hz hy⟩, hy⟩
    one := (Fintype.card_congr (Equiv.subtypeUnivEquiv (p := InBox E (G.s + 1 + 1)) fun _ _ => by omega)).trans E.one
    dL := fun j α γ => E.dL j α.1 γ.1
    dL_mid := fun j d H α γ => E.dL_mid j d H α.1 γ.1
    dL_pen := fun α y => E.dL_pen α.1 y.1
    dL_top := fun y u => E.dL_top y.1 u.1
    εL := fun j α => E.εL j α.1
    εL_at := fun j ρ hρ d h α => E.εL_at j ρ hρ d h α.1
    εL_zero := fun α => E.εL_zero α.1
    wt := fun j α => E.wt j α.1
    wt_mid := fun j d h α => E.wt_mid j d h α.1
    wt_pen := fun y => E.wt_pen y.1
    wt_top := fun u => E.wt_top u.1 }

end Restr

section Place
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)
  {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E} {G : QGeo v Bs PP}
  {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ)

abbrev Orb := SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box (XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1)) (G.ϖ ^ E.M))


variable (G) in
abbrev locV (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))) (z : Formalism.L2.Col.Sp B.fields.E (B.R.N (G.s + 1))) :
    XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) → G.k := fun r => (ofSplit G.q).pr (z (e r))

def OrbAt (j : ℕ) (y : E.Ch j) (β : Ch₀ j) : Prop :=
  ∀ (h : j = G.s + 1) (e : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) ≃ Fin (B.R.N (G.s + 1))), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e →
    Orb E (E.cos (h ▸ y)) (Submodule.Quotient.mk (locV G e (Formalism.L2.Col.repY (A.p0 (G.s + 1) (h ▸ β)).1.2)))

variable {A E} {P : BadPr I a} {hψ : Continuous G.ψk} {sg : ℂ}


set_option maxHeartbeats 1000000 in
theorem orb_iff (hI : I.Ok)
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (hM : E.M = (I.cst a).M) (b : Idx I.sel (I.tup a) (I.idx a) (G.s + 1)) (hQ : P.1 ∈ I.Q a) {e}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e) (z z') :
    Orb E (Submodule.Quotient.mk (locV G e z)) (Submodule.Quotient.mk (locV G e z')) ↔
      ∃ κ ∈ (levQ I a (G.s + 1) b ⟨P.1, hQ⟩).H, ((Formalism.L2.Col.qOf P.1 : B.fields.E) ^ (I.cst a).M)⁻¹ • (κ.1 z - z') ∈
        Formalism.L2.Col.stdAt B.fields.E (B.R.N (G.s + 1)) P.1 := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  have hL := hI.idx_ok a
  rw [show B.R.m - 2 = G.s by omega] at hL
  have h := GlobalTheory.T.twistPrime_rational_coset_sameOrbit_iff_level B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) B.embLL P G.k _ G.s _ tw (I.idx a) I.glob hL
    (b.get (by omega)) hQ e he z z'
  have e1 : levQ I a (G.s + 1) b = (I.idx a).levQ (G.s + 1) (b.get (by omega)) := by
    unfold levQ levQAt
    rw [← b.some_get (by omega)]
    rfl
  rw [e1, ← h]
  unfold Orb
  rw [hM]
  rfl

theorem locV_mem_iff
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (M : ℕ) (e) (z) : locV G e z ∈ box _ (G.ϖ ^ M)⁻¹ ↔
      (Formalism.L2.Col.qOf P.1 : B.fields.E) ^ M • z ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N (G.s + 1)) P.1 := by
  letI := GlobalTheory.Mem.Col2.starE B
  rw [GlobalTheory.TopStep.mem_stdAt, mem_box, e.forall_congr_right.symm]
  refine forall_congr' fun r => ?_
  have hu : (G.ϖ : G.k) = _ := tw.compl.unif
  rw [← tw.compl.int, ← mul_int_iff, Pi.smul_apply, smul_eq_mul, map_mul, map_pow, ← hu, Units.val_pow_eq_pow_val]
  rfl

theorem orbAt_unique {j : ℕ} (hj : j + 1 = B.R.m) {y y' : E.Ch j} {β : Ch₀ j} (h : OrbAt A E j y β) (h' : OrbAt A E j y' β) : y = y' := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  obtain rfl : j = G.s + 1 := by omega
  obtain ⟨e, he⟩ := exists_xOrd B.R (G.s + 1)
  have H := sameOrb_equiv (E.le (G.s + 1) 0 rfl) (G.ϖ ^ E.M)
  exact E.cos_inj _ _ (H.trans (h rfl e he) (H.symm (h' rfl e he)))


set_option maxHeartbeats 1000000 in
theorem exists_orbAt (hI : I.Ok) (hA : A.Is)
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (hM : E.M = (I.cst a).M) {j : ℕ} (hj : j + 1 = B.R.m) (β : Ch₀ j) (hk : A.kb j β = TC.kStd X u (B.R.N j)) :
    ∃ y, InBox E j y ∧ OrbAt A E j y β := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  obtain rfl : j = G.s + 1 := by omega
  obtain ⟨e, he⟩ := exists_xOrd B.R (G.s + 1)
  have h0 := ownVec_mem A P tw.nmem tw.compl e β
  have hv := (MemChart.kStd_spec l.pr u (B.R.N (G.s + 1))).2.1
  rw [← hk] at hv
  have e1 := GlobalTheory.QTw.frsF_base_eq_self A hA hI P tw.nmem _ (by omega) β hv
  have e' : ownVec A G P e β = locV G e (Formalism.L2.Col.repY (A.p0 (G.s + 1) β).1.2) := by
    unfold ownVec
    rw [(LinearEquiv.symm_apply_eq _).2 (e1 _).symm]
  rw [e', ← hM] at h0
  obtain ⟨y, hy⟩ := E.cos_all _ h0
  refine ⟨y, inBox_of_orb E h0 hy, fun _ e' he' => ?_⟩
  obtain rfl : e' = e := Equiv.ext fun r => Fin.ext ((he' r).trans (he r).symm)
  exact hy


set_option maxHeartbeats 1000000 in
theorem lev_of_orbAt (hI : I.Ok) (hA : A.Is)
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (hM : E.M = (I.cst a).M) {j : ℕ} (hj : j + 1 = B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) (hQ : P.1 ∈ I.Q a) {y : E.Ch j}
    {β β' : Ch₀ j} (hk : A.kb j β = TC.kStd X u (B.R.N j)) (hk' : A.kb j β' = TC.kStd X u (B.R.N j))
    (h : OrbAt A E j y β) (h' : OrbAt A E j y β') :
    ∃ κ ∈ (levQ I a j b ⟨P.1, hQ⟩).H, ∃ z ∈ cosetIn (A.p0 j β) P, κ.1 z ∈ cosetIn (A.p0 j β') P := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  obtain rfl : j = G.s + 1 := by omega
  obtain ⟨e, he⟩ := exists_xOrd B.R (G.s + 1)
  have H := sameOrb_equiv (E.le (G.s + 1) 0 rfl) (G.ϖ ^ E.M)
  obtain ⟨κ, hκ, h1⟩ := (orb_iff hI tw hM b hQ he _ _).1 (H.trans (H.symm (h rfl e he)) (h' rfl e he))
  refine ⟨κ, hκ, _, repY_mem hI hA hj β hk P, mem_of_sub (repY_mem hI hA hj β' hk' P) ?_⟩
  rw [if_neg tw.nmem]
  exact h1


set_option maxHeartbeats 1000000 in
theorem exists_vec (hI : I.Ok) (hA : A.Is)
    (tw : GlobalTheory.TwBridge.AtTwist (R := B.R) (k := G.k) I.sel (I.tup a) (I.cst a) B.embLL P (G.q.pr.comp (incA (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G))) G.s (E.tw hψ sg))
    (hM : E.M = (I.cst a).M) {j : ℕ} (hj : j + 1 = B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) {y : E.Ch j} (hy : InBox E j y) :
    ∃ z : Formalism.L2.Col.Sp B.fields.E (B.R.N j),
      (Formalism.L2.Col.qOf P.1 : B.fields.E) ^ (I.cst a).M • z ∈ Formalism.L2.Col.stdAt B.fields.E (B.R.N j) P.1 ∧
      ∀ (hQ : P.1 ∈ I.Q a) (β : Ch₀ j), A.kb j β = TC.kStd X u (B.R.N j) →
        (∃ κ ∈ (levQ I a j b ⟨P.1, hQ⟩).H, κ.1 z ∈ cosetIn (A.p0 j β) P) → OrbAt A E j y β := by
  have hs : G.s + 1 + 1 = B.R.m := G.hs
  obtain rfl : j = G.s + 1 := by omega
  obtain ⟨e, he⟩ := exists_xOrd B.R (G.s + 1)
  obtain ⟨(w : XIx (Fin B.R.k) (Fin B.R.t) (G.s + 1) → G.k), hw, hc⟩ := hy rfl
  have hap : ∀ x : G.k, ∃ z : B.fields.E, valuation G.k ((ofSplit G.q).pr z - x) ≤ valuation G.k ((G.ϖ ^ E.M : G.kˣ) : G.k) := fun x => by
    have hn : {y : G.k | valuation G.k (y - x) < valuation G.k ((G.ϖ ^ E.M : G.kˣ) : G.k)} ∈ nhds x :=
      IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ ((Valuation.ne_zero_iff _).2 (G.ϖ ^ E.M).ne_zero), fun y hy => by simpa using hy⟩
    obtain ⟨_, hy, z, rfl⟩ := mem_closure_iff_nhds.1 (tw.compl.dense x) _ hn
    exact ⟨z, le_of_lt hy⟩
  choose f hf using hap
  have h1 : locV G e (fun r => f (w (e.symm r))) - w ∈ box _ (G.ϖ ^ E.M) := fun r => by
    have := hf (w r)
    simpa only [Pi.sub_apply, locV, Equiv.symm_apply_apply] using this
  have h2 := add_mem (box_le G.unif _ h1) hw
  rw [sub_add_cancel] at h2
  refine ⟨fun r => f (w (e.symm r)), hM ▸ (locV_mem_iff tw _ e _).1 h2, ?_⟩
  rintro hQ β hk ⟨κ, hκ, h3⟩ _ e' he'
  obtain rfl : e' = e := Equiv.ext fun r => Fin.ext ((he' r).trans (he r).symm)
  have h4 := sub_of_mem hj (repY_mem hI hA hj β hk P) h3
  rw [if_neg tw.nmem] at h4
  have h5 := (orb_iff hI tw hM b hQ he _ _).2 ⟨κ, hκ, h4⟩
  have h6 : Submodule.Quotient.mk (locV G e' fun r => f (w (e'.symm r))) = E.cos y := ((Submodule.Quotient.eq _).2 h1).trans hc.symm
  exact (congrArg (fun x => Orb E x _) h6).mp h5

end Place

section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem couplingCoset_sub_basePoint_integral_typePrime (hI : I.Ok) (hA : A.Is) {s : ℕ} (hs : s + 1 + 1 = B.R.m) (S : GlobalTheory.SymChain.SymData k s B.R.k) (ι : B.fields.E →+* k)
    (P : BadPr I a) (hP : P.1 ∈ (B.primes X).vGs) (hint : ∀ x, ι x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P.1 x)
    (hu : valuation k ((S.ϖ : k) - ((Formalism.L2.Col.qOf P.1 : ℕ) : k)) < valuation k (S.ϖ : k)) (β : Ch₀ (s + 1))
    (hk : A.kb (s + 1) β = TC.kStd X u (B.R.N (s + 1))) (hβ : Good (A.p0 (s + 1) β))
    (e : XIx (Fin B.R.k) (Fin B.R.t) (s + 1) ≃ Fin (B.R.N (s + 1))) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e) (r) :
    ι (Formalism.L2.Col.repY (A.p0 (s + 1) β).1.2 (e r)) - S.y0 (Fin B.R.t) r ∈ 𝒪[k] := by
  letI := GlobalTheory.Mem.Col2.starE B
  have h1 := sub_of_mem hs (hβ P hP) (repY_mem hI hA hs β hk P)
  rw [if_pos hP, pow_zero, inv_one, one_smul] at h1
  have h2 := (hint _).2 (GlobalTheory.TopStep.mem_stdAt.1 h1 (e r))
  rw [Pi.sub_apply, map_sub, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast] at h2
  have h3 : ((Formalism.L2.Col.qOf P.1 : ℕ) : k)⁻¹ * ι (Formalism.L2.Col.Loc.eN B.fields.E (B.R.N (s + 1)) B.R.k (e r)) - S.y0 (Fin B.R.t) r ∈ 𝒪[k] := by
    have h0 : (e (Sum.inl (Sum.inr 0))).val = B.R.k := he _
    unfold Formalism.L2.Col.Loc.eN GlobalTheory.SymChain.SymData.y0
    by_cases hr : r = Sum.inl (Sum.inr 0)
    · subst hr
      rw [if_pos h0, map_one, mul_one, Pi.single_eq_same]
      exact inv_sub_inv_int S.unif hu
    · rw [if_neg fun h => hr (e.injective (Fin.ext (h.trans h0.symm))), map_zero, mul_zero, Pi.single_eq_of_ne hr, sub_zero]
      exact zero_mem _
  have := add_mem h2 h3
  rwa [sub_add_sub_cancel] at this

end Level


end GlobalTheory.PenChart
