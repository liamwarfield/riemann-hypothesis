module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocAutHodgeTateWeightsLevelZeroDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FillPreservesIdempotent

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.LvProj

open GlobalTheory.LvT.Pts
open Formalism.HermitianLatticesTheory (localization₂ dual)

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {M A : Submodule (𝓞 E) (Fin n → E)} {P : HeightOneSpectrum (𝓞 E)}

theorem redL_osmul (r : 𝓞 E) {x : Fin n → E} (hx : x ∈ localization₂ P.asIdeal M) :
    redL M P (r • x) = (Ideal.Quotient.mk P.asIdeal r : Res P) • redL M P x := by
  obtain ⟨s, hs, hx⟩ := (mem_locP P M _).1 hx
  refine redL_eq hs (by rw [smul_comm]; exact M.smul_mem _ hx) ?_
  rw [smul_comm, redL_spec hs hx, mk_smul_mk]
  congr 1
  exact Subtype.ext (smul_comm _ _ _)

omit [StarRing E] in
theorem redL_zero : redL M P 0 = 0 := redL_coe (M := M) (P := P) 0

def proj (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) : A →+ TDat.Red M P where
  toFun z := redL M P z.1
  map_zero' := redL_zero
  map_add' x y := redL_add (h ▸ le_locP P A x.2) (h ▸ le_locP P A y.2)

theorem proj_mk (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) (z : A) (hz : z.1 ∈ M) :
    proj h z = Submodule.Quotient.mk ⟨z.1, hz⟩ := redL_coe (M := M) (P := P) ⟨z.1, hz⟩

theorem proj_smul (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) (a : 𝓞 E) (z : A) :
    proj h (a • z) = (Ideal.Quotient.mk P.asIdeal a : Res P) • proj h z :=
  redL_osmul a (h ▸ le_locP P A z.2)

theorem proj_surj (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) : Function.Surjective (proj h) := by
  intro y
  obtain ⟨x, hx, rfl⟩ := redL_surj y
  have hx' : x ∈ localization₂ P.asIdeal M := le_locP P M hx
  obtain ⟨s, hs, hsx⟩ := (mem_locP P A x).1 (h ▸ hx')
  obtain ⟨t, p, hp, e⟩ := P.isMaximal.exists_inv hs
  refine ⟨⟨(t * s) • x, by rw [mul_smul]; exact A.smul_mem _ hsx⟩, ?_⟩
  show redL M P ((t * s) • x) = _
  have e2 : (Ideal.Quotient.mk P.asIdeal (t * s) : Res P) = 1 := by
    rw [← map_one (Ideal.Quotient.mk P.asIdeal), ← e, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 hp, add_zero]
  rw [redL_osmul _ hx', e2, one_smul]

theorem proj_ker (h : localization₂ P.asIdeal A = localization₂ P.asIdeal M) {J : Ideal (𝓞 E)} (hJ : J = P.asIdeal) (z : A) :
    proj h z = 0 ↔ z.1 ∈ J • A := by
  subst hJ
  show redL M P z.1 = 0 ↔ _
  constructor
  · intro h0
    obtain ⟨s, hs, hx⟩ := (mem_locP P M _).1 (h ▸ le_locP P A z.2)
    have h1 := redL_spec hs hx
    rw [h0, smul_zero, eq_comm, Submodule.Quotient.mk_eq_zero] at h1
    have h2 := Submodule.mem_map_of_mem (f := M.subtype) h1
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype] at h2
    have key : P.asIdeal • M ≤ localization₂ P.asIdeal (P.asIdeal • A) := by
      rw [Submodule.smul_le]
      intro r hr y hy
      obtain ⟨t, ht, hty⟩ := (mem_locP P A y).1 (h ▸ le_locP P M hy)
      exact (mem_locP P _ _).2 ⟨t, ht, by rw [smul_comm]; exact Submodule.smul_mem_smul hr hty⟩
    obtain ⟨t, ht, h3⟩ := (mem_locP P _ _).1 (key h2)
    refine mem_smul_of_loc z.2 (s := t * s) (fun hm => (P.isPrime.mem_or_mem hm).elim ht hs) ?_
    rw [mul_smul]
    exact h3
  · intro hz
    have key : ∀ y ∈ P.asIdeal • A, y ∈ A ∧ redL M P y = 0 := by
      intro y hy
      refine Submodule.smul_induction_on hy (fun r hr w hw => ⟨A.smul_mem _ hw, ?_⟩) (fun y w hy hw => ⟨A.add_mem hy.1 hw.1, ?_⟩)
      · rw [redL_osmul r (h ▸ le_locP P A hw), Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_smul]
      · rw [redL_add (h ▸ le_locP P A hy.1) (h ▸ le_locP P A hw.1), hy.2, hw.2, add_zero]
    exact (key _ hz).2

end Red

section Dec

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem dualL_one (σ : E →+* E) (hσ : ∀ x, σ x = star x) {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    (L : Submodule (𝓞 E) (Fin n → E)) : Formalism.L2.Forms.dualL σ J L = dual (hStd E n) L := by
  subst hJ
  have : Formalism.BasicNotions.dualSet σ (1 : Matrix (Fin n) (Fin n) E) L = (dual (hStd E n) L : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, Formalism.L2.Col.mem_dual]
    refine forall₂_congr fun x _ => ?_
    have e : Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
      show _ = ∑ i, star (x i) * y i
      unfold Formalism.UG.hform
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [Matrix.one_apply, hσ]
    rw [e, Submodule.mem_one]
    rfl
  unfold Formalism.L2.Forms.dualL
  rw [this, Submodule.span_eq]

variable {d : Deco E n ST SG} {a : 𝓞 E}

theorem localization_L_eq_localization_dnN (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) : localization₂ P.1.asIdeal d.L = localization₂ P.1.asIdeal (d.dnN P) := by
  rw [(hd.dnN_spec P hne).2.2.2]
  apply le_antisymm
  · refine localization_le_of_smul_mem (one_notMem P.1) fun x hx => ?_
    rw [one_smul]
    obtain ⟨h1, h2⟩ := (hd.mem_L x).1 hx
    exact (hd.mem_kerAt P x).2 ⟨h1, h2 P⟩
  · refine localization_le_of_le_localization _ fun x hx => ?_
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P x).1 hx
    exact (hd.mem_locP_L P x).2 ⟨le_locP _ _ h1, h2⟩

theorem sup_le_locP (hd : d.Ok) (ha : SepElt ST a) (P : ST) : d.L ⊔ P.1.asIdeal • d.Lsh ≤ localization₂ P.1.asIdeal d.L := by
  refine sup_le (le_locP _ _) ?_
  rw [Submodule.smul_le]
  intro r hr y hy
  have hy' := hd.Lsh_le_at ha P hy
  exact (hd.mem_locP_L P _).2 ⟨Submodule.smul_mem _ _ hy', by
    rw [hd.f_smul P r y hy', Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_mul]⟩

theorem localization_Lsh_eq_localization_N (hd : d.Ok) (ha : SepElt ST a) (P : ST) {A : Submodule (𝓞 E) (Fin n → E)} (hA : A = d.Lsh) :
    localization₂ P.1.asIdeal A = localization₂ P.1.asIdeal d.N := hA ▸ hd.locP_Lsh ha P

theorem localization_sup_eq_localization_dnN (hd : d.Ok) (ha : SepElt ST a) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) {A : Submodule (𝓞 E) (Fin n → E)}
    (hA : A = d.L ⊔ P.1.asIdeal • d.Lsh) : localization₂ P.1.asIdeal A = localization₂ P.1.asIdeal (d.dnN P) := by
  subst hA
  rw [← localization_L_eq_localization_dnN hd P hne]
  exact le_antisymm (localization_le_of_le_localization _ (sup_le_locP hd ha P))
    (localization_le_of_smul_mem (one_notMem P.1) fun x hx => by rw [one_smul]; exact Submodule.mem_sup_left hx)

theorem f_eq_zero_iff (hd : d.Ok) (ha : SepElt ST a) (P : ST) {z : Fin n → E} (hz : z ∈ d.Lsh) :
    d.f P z = 0 ↔ z ∈ d.L ⊔ P.1.asIdeal • d.Lsh := by
  constructor
  · intro h0
    obtain ⟨s, hs, hsz⟩ := (mem_locP _ _ _).1 ((hd.mem_locP_L P z).2 ⟨hd.Lsh_le_at ha P hz, h0⟩)
    obtain ⟨t, p, hp, e⟩ := P.1.isMaximal.exists_inv hs
    have : z = t • (s • z) + p • z := by rw [← mul_smul, ← add_smul, e, one_smul]
    rw [this]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ t hsz) (Submodule.smul_mem_smul hp hz)
  · intro h
    exact ((hd.mem_locP_L P z).1 (sup_le_locP hd ha P h)).2

theorem reductionModPrime_levelPrime_smul_eq (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) {z e : Fin n → E}
    (hz : z ∈ d.at P.1) (hfz : d.f P z = 1) (he : e ∈ d.N) (hfe : d.f P e = 1) (t : d.dnN P) (ht : t.1 = q • e) :
    redL (d.dnN P) P.1 (q • z) = Submodule.Quotient.mk t := by
  have he' : e ∈ d.at P.1 := le_locP _ _ he
  have hn : (-1 : 𝓞 E) • e ∈ d.at P.1 := Submodule.smul_mem _ _ he'
  have m : z + (-1 : 𝓞 E) • e ∈ localization₂ P.1.asIdeal (d.dnN P) := by
    rw [← localization_L_eq_localization_dnN hd P hne]
    refine (hd.mem_locP_L P _).2 ⟨Submodule.add_mem _ hz hn, ?_⟩
    rw [hd.f_add P _ hz _ hn, hd.f_smul P _ _ he', hfz, hfe, map_neg, map_one]
    ring
  have e1 : q • z = q • (z + (-1 : 𝓞 E) • e) + t.1 := by
    rw [ht, neg_one_smul, ← smul_add, neg_add_cancel_right]
  rw [e1, redL_add (Submodule.smul_mem _ _ m) (le_locP _ _ t.2), redL_osmul _ m,
    Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_smul, zero_add, redL_coe]

end Dec

section TD

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem fv_mk (hl : A.Laws T) (P : ST) (c : S.Cl) (x : A.N c.1 (S.rep c)) :
    A.fv P c (Submodule.Quotient.mk x) = A.f c.1 (S.rep c) P x := by
  have h0 := hl.fv_ne P c
  unfold TDat.fv at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact h1.choose_spec x
  · exact absurd rfl h0

theorem te_mk (hl : A.Laws T) (P : ST) (c : S.Cl) :
    ∃ t : A.dnN c.1 (S.rep c) P, (∃ e ∈ A.N c.1 (S.rep c), A.f c.1 (S.rep c) P e = 1 ∧ (t : Fin n → E) = (T : 𝓞 E) • e) ∧
      Submodule.Quotient.mk t = A.te T P c := by
  have h0 := hl.te_ne P c
  unfold TDat.te at h0 ⊢
  split_ifs at h0 ⊢ with h1
  · exact ⟨h1.choose, h1.choose_spec, rfl⟩
  · exact absurd rfl h0

end TD

end GlobalTheory.Mem.Col2.LvProj

end


open GlobalTheory.Mem.Col2.LvProj GlobalTheory.LvT.Pts in
set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mem.Col2.TC.exists_level_projections : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∃ (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.IdL l Z u a i hi L := by
  intro B X I hI hP l Z u a i hi
  obtain ⟨-, -, -, hc⟩ := TC.spaces_in_coordinates I hI hP l Z
  obtain ⟨hg, -, hc⟩ := hc i hi
  have hL := (hc u a).1
  clear hc
  have ha := sepElt_of_ok l.pr u
  have hne : ∀ v : (B.primes X).vT u, conjPrime₂ v.1 ≠ v.1 := fun v => (moveHyp_of_ok l.pr u v).ne
  have hT : ∀ v : (B.primes X).vT u, ((B.T u : ℕ) : 𝓞 B.fields.E) ∈ v.1.asIdeal := fun v => Formalism.L2.Col.T_mem l.pr u v
  have hl := (l.fmL u a).lev i
  let d : (I.stp u a i).Cl → Deco B.fields.E (B.R.N i) ((B.primes X).vT u) (B.primes X).vGs :=
    fun c => ((I.stp u a i).rep c).1.1.deco.1
  have hd : ∀ c, (d c).Ok := fun c => ((I.stp u a i).rep c).1.1.deco.2
  have hs : ∀ x : B.fields.E, (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) x = star x := fun _ => rfl
  have hD0 := fun L => @dualL_one B.fields.E B.fields.fieldE B.fields.nfE B.fields.starE _ _ hs _ hg L
  have hD : ∀ c, LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = (d c).Lsh := fun c =>
    (hD0 _).trans (congrArg _ (hL c))
  have hPv : ∀ v : (B.primes X).vT u, PvG (D := I.rec7 l Z) (I.resT l u a) v = v.1.asIdeal := fun v =>
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem (I := (v.1.asIdeal : Ideal (𝓞 B.fields.E)))
  have hK : ∀ (v : (B.primes X).vT u) c, LkG (I.rec7 l Z) i hi (PvG (D := I.rec7 l Z) (I.resT l u a) v)
      (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) = (d c).L ⊔ v.1.asIdeal • (d c).Lsh := fun v c =>
    congrArg₂ (· ⊔ ·) (hL c) (congrArg₂ (· • ·) (hPv v) (hD c))
  have h1 := fun v c => localization_Lsh_eq_localization_N (hd c) ha v (hD c)
  have h2 := fun v c => localization_sup_eq_localization_dnN (hd c) ha v (hne v) (hK v c)
  have hf : ∀ v c z, (I.fm l u a).fv i v c (proj (h1 v c) z) = (d c).f v z.1 := fun v c z =>
    dual_redL ((hd c).f_smul v) _ (fv_mk hl v c) (h1 v c ▸ le_locP v.1 _ z.2)
  refine ⟨⟨fun v c => proj (h1 v c), fun v c => proj_surj (h1 v c), fun v c => proj_smul (h1 v c),
    fun v c => proj_ker (h1 v c) (hPv v), fun v c z => ?_, fun v c => proj (h2 v c), fun v c => proj_surj (h2 v c),
    fun v c => proj_smul (h2 v c), fun v c => proj_ker (h2 v c) (hPv v), fun v c z hz h => ?_⟩,
    fun v c z h => proj_mk (h1 v c) z h, fun v c z h => proj_mk (h2 v c) z h⟩
  · have e := f_eq_zero_iff (hd c) ha v (z := z.1) (hD c ▸ z.2)
    rw [← hK v c, ← hf v c z] at e
    exact e
  · obtain ⟨t, ⟨e, he, hfe, ht⟩, hte⟩ := te_mk hl v c
    exact (reductionModPrime_levelPrime_smul_eq (hd c) v (hne v) (hT v) ((hd c).Lsh_le_at ha v (hD c ▸ z.2)) ((hf v c z).symm.trans hz) he hfe t ht).trans hte
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulMemOfSpan
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulEqInteger
universe u_1 u_2

namespace GlobalTheory.NatMulIntegerMultiple

open NumberField

theorem exists_nat_mul_eq_integer {K : Type*} [Field K] [NumberField K] (k : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, (n : K) * k = algebraMap (𝓞 K) K a := by
  have halg : IsAlgebraic ℤ k :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = (n : ℤ) • k := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact hint
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = -((-(n : ℤ)) • k) := by rw [zsmul_eq_mul]; push_cast; ring
    rw [this]; exact hint.neg

theorem exists_nsmul_mem {K : Type*} {V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    ∀ x ∈ Submodule.span K (L : Set V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_ne_zero, by simpa using h⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    have e1 : (m * n) • x = n • (m • x) := by rw [mul_nsmul]
    have e2 : (m * n) • y = m • (n • y) := by rw [mul_comm, mul_nsmul]
    rw [e1, e2]
    exact L.add_mem (L.nsmul_mem hmx n) (L.nsmul_mem hny m)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_integer c
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have : (m * n) • (c • x) = a • (n • x) := by
      calc (m * n) • (c • x) = ((m : K) * c) • (n • x) := by
            rw [← Nat.cast_smul_eq_nsmul K (m * n), ← Nat.cast_smul_eq_nsmul K n, smul_smul, smul_smul]
            push_cast; ring_nf
        _ = algebraMap (𝓞 K) K a • (n • x) := by rw [ha]
        _ = a • (n • x) := algebraMap_smul K a (n • x)
    rw [this]; exact L.smul_mem a hnx

theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑L : Set V), ∃ (n : ℕ), n ≠ (0 : ℕ) ∧ n • x ∈ L :=
  fun L => exists_nsmul_mem L

end GlobalTheory.NatMulIntegerMultiple
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Full

theorem exists_nsmul_mem_of_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) (x : V) (hx : x ∈ Submodule.span K (L : Set V)) :
    ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegerMultiple.main
  | exact _root_.GlobalTheory.NatMulIntegerMultiple.main
  | (apply _root_.GlobalTheory.NatMulIntegerMultiple.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegerMultiple.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegerMultiple.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegerMultiple.main ..)

theorem dgam_pos_and_full : ∀ D : D7, (∀ u, 0 < (D.mem u).C.DGam) ∧
    ∀ u (x : (D.div.Nu u).V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ DV.MramL D u := by
  intro D
  refine ⟨fun u => (D.mem u).C.DGam_pos, fun u x => ?_⟩
  obtain ⟨n, hn, h⟩ := exists_nsmul_mem_of_span ((D.fm u).lat 0).L (D.nuIn u x)
    (by rw [((D.fm u).lat_good 0).2.2]; trivial)
  refine ⟨n, hn, ?_⟩
  show D.nuIn u (n • x) ∈ ((D.fm u).lat 0).L
  rw [map_nsmul]
  exact h

end GlobalTheory.Mem.Full
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiagSpacesOfOver
noncomputable section

namespace GlobalTheory.Mem.HostFrames

open Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top NumberField

section Coord

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def SignFrame (S : HSpace E) : Prop :=
  (∃ neg : Fin S.rank → Bool, ∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then (Examples₂.sgn (neg a) : E) else 0) ∧
    S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

def UnitFrame (S : HSpace E) : Prop :=
  (∀ a b, S.hT (S.frame a) (S.frame b) = if a = b then 1 else 0) ∧ S.L0 = Submodule.span (𝓞 E) (Set.range S.frame)

theorem UnitFrame.signFrame {S : HSpace E} (h : UnitFrame S) : SignFrame S :=
  ⟨⟨fun _ => false, fun a b => by rw [h.1]; simp [Examples₂.sgn]⟩, h.2⟩

variable (hstar : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))

theorem signFrame_stdSpace (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) : SignFrame (Examples₂.stdSpace hstar N neg p q) :=
  ⟨⟨neg, Examples₂.stdSpace_gram_apply hstar N neg p q⟩, rfl⟩

theorem unitFrame_stdSpace (N p q : ℕ) : UnitFrame (Examples₂.stdSpace hstar N (fun _ => false) p q) :=
  ⟨fun a b => (Examples₂.stdSpace_gram_apply hstar N (fun _ => false) p q a b).trans (by simp [Examples₂.sgn]; rfl), rfl⟩

theorem SignFrame.gram_eq {S : HSpace E} (h : SignFrame S) (F : Type) [Field F] [Algebra F E] :
    ∃ d : Fin S.rank → F, (∀ a, d a = 1 ∨ d a = -1) ∧ S.gram = Matrix.diagonal fun a => algebraMap F E (d a) := by
  obtain ⟨neg, hn⟩ := h.1
  refine ⟨fun a => Examples₂.sgn (neg a), fun a => by cases hh : neg a <;> simp [Examples₂.sgn, hh], ?_⟩
  ext a b
  rw [HSpace.gram, hn, Matrix.diagonal_apply, Examples₂.map_sgn]

end Coord

section Diag

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {S : Spaces R F E}

theorem signFrame_Y (h : DiagSpaces S) (j : ℕ) : SignFrame (S.Y j) := by
  obtain ⟨hs, -, -, hY, -, -⟩ := h
  rw [hY]; exact signFrame_stdSpace hs _ _ _ _

theorem signFrame_V (h : DiagSpaces S) (j : ℕ) : SignFrame (S.V j) := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  rw [hV]; exact signFrame_stdSpace hs _ _ _ _

theorem signFrame_W_of_one_le_of_le (h : DiagSpaces S) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ R.m) : SignFrame (S.W j) := by
  obtain ⟨hs, -, -, -, hW, -⟩ := h
  rw [hW j h1 h2]; exact signFrame_stdSpace hs _ _ _ _

theorem unitFrame_X' (h : DiagSpaces S) : UnitFrame S.X' := by
  obtain ⟨hs, -, hX, -, -, -⟩ := h
  rw [hX]; exact unitFrame_stdSpace hs _ _ _

theorem unitFrame_V (h : DiagSpaces S) {j : ℕ} (hn : S.Vneg j = false) : UnitFrame (S.V j) ∧ (S.V j).IsPosDef := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  rw [hV, hn]; exact ⟨unitFrame_stdSpace hs _ _ _, fun _ => rfl⟩

end Diag

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem diagSpaces_of_over {K : Ctx} {B : Pre} (h : K.Over B) : DiagSpaces B.sp := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, hd⟩ := h
  exact hd

theorem val_of_over {K : Ctx} {B : Pre} (h : K.Over B) :
    RankVal K.s B.R ∧ ∃ bT, ∀ u, HCVal K.s K.cD K.ch B.host (fun τ : Tau B.R => (τ : B.R.GG)) (B.hcW u) bT := by
  obtain ⟨sp, hT, hY, hA, hV, hz, rfl, hd⟩ := h
  exact ⟨K.ok.rank, _, K.ok.hc⟩

theorem frames_of_over (K : Ctx) (X : Stages) (h : K.Over X.B.toPre) :
    X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧
    (∀ i, SignFrame (Wc X.toD7 i) ∧ SignFrame (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧
    (∀ j, SignFrame (X.toD7.sp.Y j) ∧ SignFrame (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → SignFrame (X.toD7.sp.W j))) ∧
    SignFrame X.toD7.sp.X' ∧
    (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧
      (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧
    ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧
      X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame)) := by
  have hd : DiagSpaces X.toD7.sp := diagSpaces_of_over h
  have hV : ∀ i : Fin X.toD7.R.m, X.toD7.sp.Vneg ((i : ℕ) + 1) = false := fun i => X.B.V_pos _ (by omega) i.2
  exact ⟨rfl, fun i => ⟨signFrame_W_of_one_le_of_le hd (by omega) i.2, signFrame_V hd _⟩, fun i => (unitFrame_V hd (hV i)).2,
    fun j => ⟨signFrame_Y hd j, signFrame_V hd j, signFrame_W_of_one_le_of_le hd⟩, (unitFrame_X' hd).signFrame,
    fun i => (unitFrame_V hd (hV i)).1, unitFrame_X' hd⟩

theorem size_le (eps c : ℝ) (A : ℕ) (he : 0 < eps) (he' : eps < 1 / 52) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (y : ℝ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 402 * (A : ℝ) + 2 ≤ y → c * s.L * (R.N R.m : ℝ) ^ A ≤ (⌈s.x ^ y⌉₊ : ℝ) := by
  obtain ⟨x1, h1⟩ := rank_basic_bounds eps he he'
  refine ⟨max x1 c, fun s R y hs hx hR hy => ?_⟩
  obtain ⟨-, -, -, -, -, hL, hL1, -, -, -, -, -, -, -, hN, -, -⟩ := h1 s R hs ((le_max_left _ _).trans hx) hR
  have hc : c ≤ s.x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ s.x := s.one_lt_alt.le
  have hx0 : 0 < s.x := by linarith
  have a1 : (R.N R.m : ℝ) ^ A ≤ s.x ^ (402 * (A : ℝ)) := by
    rw [Real.rpow_mul hx0.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hN A
  have a2 : c * s.L ≤ s.x * s.x := mul_le_mul hc hL (by linarith) hx0.le
  calc c * s.L * (R.N R.m : ℝ) ^ A ≤ s.x * s.x * s.x ^ (402 * (A : ℝ)) :=
        mul_le_mul a2 a1 (by positivity) (by positivity)
    _ = s.x ^ (402 * (A : ℝ) + 2) := by rw [Real.rpow_add hx0, Real.rpow_two]; ring
    _ ≤ s.x ^ y := Real.rpow_le_rpow_of_exponent_le hx1 hy
    _ ≤ _ := Nat.le_ceil _

end GlobalTheory.Mem.HostFrames

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTameQuotientJointPowersTameGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTameQuotientJointPowersTameGenerator
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem isClosed_singleton_of_isAdic {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [TopologicalSpace O] [IsTopologicalRing O] (had : IsAdic (IsLocalRing.maximalIdeal O)) (c : O) :
    IsClosed ({c} : Set O) := by
  have e : ({c} : Set O) = ⋂ M : ℕ, (fun x => x - c) ⁻¹'
      ((IsLocalRing.maximalIdeal O ^ M : Ideal O) : Set O) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro rfl M
      simp
    · intro h
      have h2 := Ideal.mem_iInf.2 h
      rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top] at h2
      simpa [sub_eq_zero] using h2
  rw [e]
  refine isClosed_iInter fun M => IsClosed.preimage (continuous_id.sub continuous_const) ?_
  exact AddSubgroup.isClosed_of_isOpen (IsLocalRing.maximalIdeal O ^ M : Ideal O).toAddSubgroup
    ((isAdic_iff.1 had).1 M)

theorem joint_pow_of_tameGen : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ : G E Ω), TameGenAt A γ → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ¬ A.valuation (m : Ω) < 1 → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (e : E) (π : Ω), π ≠ 0 → π ^ m = algebraMap E Ω e → ∀ σ ∈ Ine (F := E) A, ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = (γ π / π) ^ n := by
  intro E Ω _ _ _ _ _ A γ hγ O _ _ _ _ _ had χ hχ m hm0 hm hI e π hπ he
  set q : Ω := γ π / π with hqdef
  have hroot : ∀ τ : G E Ω, (τ π / π) ^ m = 1 := by
    intro τ
    rw [div_pow, ← map_pow, he, AlgEquiv.commutes, ← he, div_self (pow_ne_zero _ hπ)]
  have hq : q ^ m = 1 := hroot γ
  have hc : χ γ ^ m = 1 := hI γ hγ.1
  have hinv : ∀ {M : Type} [Group M] (x : M), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1)) := by
    intro M _ x hx n
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← pow_add, show n * (m - 1) + n = n * m by
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp [Nat.mul_add]]
    rw [pow_mul', hx, one_pow]
  have hinv0 : ∀ (x : Ω), x ^ m = 1 → ∀ n : ℕ, (x ^ n)⁻¹ = x ^ (n * (m - 1)) := by
    intro x hx n
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow hm0.ne'] at hx
      exact zero_ne_one hx
    have := hinv (Units.mk0 x hx0) (by ext; simpa using hx) n
    have := congrArg (fun u : Ωˣ => (u : Ω)) this
    simpa using this
  let H : Subgroup (G E Ω) :=
    { carrier := {σ | σ ∈ Ine (F := E) A ∧ ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = q ^ n}
      mul_mem' := by
        rintro σ τ ⟨hσ, n₁, h₁, h₁'⟩ ⟨hτ, n₂, h₂, h₂'⟩
        refine ⟨mul_mem hσ hτ, n₁ + n₂, ?_, ?_⟩
        · rw [map_mul, h₁, h₂, pow_add]
        · rw [quot_mul hσ m hm hπ he, h₁', h₂', pow_add]
      one_mem' := ⟨one_mem _, 0, by simp, by simp [div_self hπ]⟩
      inv_mem' := by
        rintro σ ⟨hσ, n, h₁, h₁'⟩
        have hσi : σ⁻¹ ∈ Ine (F := E) A := inv_mem hσ
        refine ⟨hσi, n * (m - 1), ?_, ?_⟩
        · rw [map_inv, h₁, hinv _ hc]
        · have h3 := quot_mul hσi m hm hπ he (τ := σ)
          rw [inv_mul_cancel, AlgEquiv.one_apply, div_self hπ, h₁'] at h3
          rw [← hinv0 q hq, eq_inv_of_mul_eq_one_left h3.symm] }
  have hclosed : IsClosed (H : Set (G E Ω)) := by
    have e : (H : Set (G E Ω)) = (Ine (F := E) A : Set (G E Ω)) ∩
        ⋃ n ∈ Finset.range m, ({σ : G E Ω | ((χ σ : Oˣ) : O) = ((χ γ ^ n : Oˣ) : O)} ∩
          {σ : G E Ω | σ π = q ^ n * π}) := by
      ext σ
      simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_range, exists_prop,
        SetLike.mem_coe]
      constructor
      · rintro ⟨hσ, n, h₁, h₁'⟩
        refine ⟨hσ, n % m, Nat.mod_lt _ hm0, ?_, ?_⟩
        · rw [h₁, ← pow_mod_orderOf, ← pow_mod_orderOf (χ γ) (n % m)]
          congr 2
          have hd := orderOf_dvd_of_pow_eq_one hc
          rw [Nat.mod_mod_of_dvd _ hd]
        · rw [← pow_mod_orderOf, ← div_eq_iff hπ, h₁']
          rw [← pow_mod_orderOf q n]
          congr 1
          rw [Nat.mod_mod_of_dvd _ (orderOf_dvd_of_pow_eq_one hq)]
      · rintro ⟨hσ, n, -, h₁, h₁'⟩
        exact ⟨hσ, n, Units.ext h₁, by rw [h₁', mul_div_cancel_right₀ _ hπ]⟩
    rw [e]
    refine (isClosed_Ine A).inter (isClosed_biUnion_finset fun n _ => IsClosed.inter ?_ ?_)
    · exact (isClosed_singleton_of_isAdic had _).preimage hχ
    · exact isClosed_setOf_apply π (fun y => y = q ^ n * π)
  intro σ hσ
  have hle : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) ≤ H := by
    refine (Subgroup.closure_le _).2 ?_
    rintro τ (rfl | hτ)
    · exact ⟨hγ.1, 1, by simp, by simp [hqdef]⟩
    · have hτI : τ ∈ Ine (F := E) A := GlobalTheory.TameGenPowers.wild_mem_Ine hτ
      refine ⟨hτI, 0, ?_, ?_⟩
      · rw [pow_zero]
        exact GlobalTheory.WildSetSQ.char_eq_one_of_wild A had χ hχ τ hτ m hm (hI τ hτI)
      · rw [pow_zero]
        exact eq_one_of_pow_eq_one A hm (hroot τ) (hτ π hπ)
  have hmem := closure_minimal (SetLike.coe_subset_coe.2 hle) hclosed (hγ.2 hσ)
  exact hmem.2

end GlobalTheory.TameTau
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTameQuotientJointPowersTameGeneratorStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_tameQuotient_jointPowers_tameGenerator : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (γ : G E Ω), TameGenAt A γ → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ¬ A.valuation (m : Ω) < 1 → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (e : E) (π : Ω), π ≠ 0 → π ^ m = algebraMap E Ω e → ∀ σ ∈ Ine (F := E) A, ∃ n : ℕ, χ σ = χ γ ^ n ∧ σ π / π = (γ π / π) ^ n := by
  first | exact @GlobalTheory.TameTau.joint_pow_of_tameGen | exact GlobalTheory.TameTau.joint_pow_of_tameGen | (intros; apply GlobalTheory.TameTau.joint_pow_of_tameGen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1000000

theorem inner_eq_of_norm_sq {K V E M : Type} [Field K] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup M] [Module K M] (σ : K →+* ℂ) (j : M →ₛₗ[σ] V) (hspan : Submodule.span ℂ (Set.range j) = ⊤) (k : K)
    (hk : (σ k).im ≠ 0) (e : V →ₗ[ℂ] E) (q : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hn : ∀ m, ((‖e (j m)‖ ^ 2 : ℝ) : ℂ) = q (j m) (j m))
    (y y' : V) : inner ℂ (e y) (e y') = q y y' := by
  let D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun y y' => inner ℂ (e y) (e y') - q y y')
    (fun y z y' => by simp only [map_add (f := _), inner_add_left, LinearMap.add_apply]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_left, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun y y' z => by simp only [map_add (f := _), inner_add_right]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]; ring)
  have hDapp : ∀ y y', D y y' = inner ℂ (e y) (e y') - q y y' := fun y y' => rfl
  have h0 : ∀ m, D (j m) (j m) = 0 := by
    intro m
    rw [hDapp, ← hn m, inner_self_eq_norm_sq_to_K]
    simp
  have hsym : ∀ m m', D (j m) (j m') + D (j m') (j m) = 0 := by
    intro m m'
    have h := h0 (m + m')
    simp only [map_add (f := _), LinearMap.add_apply, h0 m, h0 m'] at h
    linear_combination h
  have hpair : ∀ m m', D (j m) (j m') = 0 := by
    intro m m'
    have h1 := hsym m (k • m')
    rw [j.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
    have h2 := hsym m m'
    have h3 : (σ k - starRingEnd ℂ (σ k)) * D (j m) (j m') = 0 := by linear_combination h1 - starRingEnd ℂ (σ k) * h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exfalso
      rw [Complex.sub_conj] at h4
      simp [hk] at h4
    · exact h4
  have h1 : ∀ m, D (j m) = 0 := fun m => LinearMap.ext_on_range hspan fun m' => by rw [hpair m m']; rfl
  have hall : D = 0 := LinearMap.ext_on_range hspan fun m => by rw [h1 m]; rfl
  have h := congrArg (fun D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => D y y') hall
  simp only [hDapp, LinearMap.zero_apply] at h
  exact sub_eq_zero.1 h

theorem exists_embLL_im_ne {B : Base} (hX : B.fields.Ok) : ∃ k : B.LL, (B.embLL k).im ≠ 0 := by
  have hc : (InfinitePlace.mk (B.embLL : B.fields.K →+* ℂ)).IsComplex := hX.cplxK.isComplex _
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  by_contra hne
  push_neg at hne
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hne x)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def cjPol (ι : Type) (n : ℕ) : Pol ℂ ι n →ₗ⋆[ℂ] Pol ℂ ι n where
  toFun p := MvPolynomial.map (starRingEnd ℂ) p
  map_add' p q := map_add _ p q
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, RingHom.id_apply]

theorem map_conj_smul {ι : Type} {n : ℕ} (r : ℂ) (p : Pol ℂ ι n) :
    MvPolynomial.map (starRingEnd ℂ) (r • p) = starRingEnd ℂ r • MvPolynomial.map (starRingEnd ℂ) p :=
  (cjPol ι n).map_smulₛₗ r p

abbrev rowS (a : I.ι) : GSD B.fields.K := mtildeGSD (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps

theorem rowS_ok (hX : B.fields.Ok) (a : I.ι) : (rowS I a).Ok :=
  mtildeOk (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) hX I.Ps

def cTerm (a : I.ι) (c : (rowS I a).Cl) (F G : MtCx I a) : ℂ :=
  ((Nat.card (@MulAction.stabilizer (rowS I a).G (rowS I a).D _ (rowS I a).actD ((rowS I a).outSec.rep c)) : ℕ) : ℂ)⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 ((rowS I a).outSec.rep c))) (G.1 ((rowS I a).outSec.rep c))

theorem cTerm_add_left (a : I.ι) (c : (rowS I a).Cl) (F F' G : MtCx I a) :
    cTerm I a c (F + F') G = cTerm I a c F G + cTerm I a c F' G := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply, mul_add]

theorem cTerm_smul_left (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c (r • F) G = starRingEnd ℂ r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_conj_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem cTerm_add_right (a : I.ι) (c : (rowS I a).Cl) (F G G' : MtCx I a) :
    cTerm I a c F (G + G') = cTerm I a c F G + cTerm I a c F G' := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]

theorem cTerm_smul_right (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c F (r • G) = r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_smul, smul_eq_mul]
  ring

def cSum (hX : B.fields.Ok) (a : I.ι) : MtCx I a →ₗ⋆[ℂ] MtCx I a →ₗ[ℂ] ℂ :=
  letI := (rowS_ok I hX a).fintypeCl
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun F G => ∑ c : (rowS I a).Cl, cTerm I a c F G)
    (fun F F' G => by simp only [cTerm_add_left, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_left, Finset.mul_sum, smul_eq_mul])
    (fun F G G' => by simp only [cTerm_add_right, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_right, Finset.mul_sum, smul_eq_mul, RingHom.id_apply])

theorem cSum_apply (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) :
    cSum I hX a F G = letI := (rowS_ok I hX a).fintypeCl; ∑ c : (rowS I a).Cl, cTerm I a c F G := rfl

end GlobalTheory.Mem.Df

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TrueTheta

open GlobalTheory.NormSum.UnramHecke GlobalTheory.VacuumScalar

theorem exists_family_of_curve : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ ∧ vec22 D (tor0 D cc δ) e ∧ eq22 D (tor0 D cc δ) χ e := by
  intro D cc δ hc
  obtain ⟨t0, ht0⟩ := (GlobalTheory.TwoTorsionPt.exists_point D cc δ hc).1
  obtain ⟨κ, k1, k2, k3⟩ := exists_kappa D
  obtain ⟨χ, hχ, hdet⟩ := exists_chi D κ k1 k2
  have hv : ∀ N N' : ℕ, ∃ e0 : VC D N N' → ℂ, Even (N * N') → oddE0 D cc δ t0 N N' e0 ∧ e0 ≠ 0 := by
    intro N N'
    by_cases h : Even (N * N')
    · obtain ⟨e0, he⟩ := GlobalTheory.Vacuum.exists_vacuum D cc δ hc t0 ht0 N N' h
      exact ⟨e0, fun _ => he⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose e0 he0 using hv
  let e : FamE D := fun N N' L L' =>
    (χ (detId D (stdL D N) L) ^ ((N' / 2 : ℕ) : ℤ) * χ (detId D (stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ))) •
      Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') (e0 N N')
  have hsc : ∀ {N N' : ℕ} (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L →
      Moves D (g' : GL (Fin N') (AE D)) L' → e N N' L L' = ((scal κ g g' : ℂˣ) : ℂ) •
        Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (La D (tor0 D cc δ) L L') (e0 N N') := by
    intro N N' g g' L L' hL hL'
    simp only [e]
    rw [hdet N 1 g _ _ (moves_one D N) hL, hdet N' 1 g' _ _ (moves_one D N') hL', inv_one, inv_one, one_mul, one_mul,
      scal, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val]
  have hW : ∀ N N', Even N → Even N' → ∃ W : WeilO D cc δ N N' (e0 N N'),
      (∀ τ, 2 * (0 : ℤ) = W.ep * W.chV.n τ + (N : ℤ)) ∧ (∀ τ, 2 * (0 : ℤ) = W.ep' * W.chV'.n τ - (N' : ℤ)) ∧
      ∀ (g : GA D N) (g' : GA D N') L L', Moves D (g : GL (Fin N) (AE D)) L → Moves D (g' : GL (Fin N') (AE D)) L' →
        ((scal κ g g' : ℂˣ) : ℂ) ∈ Qbar ∧ W.Om g g' (e0 N N') = e N N' L L' := by
    intro N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    obtain ⟨W, w1, w2, w3⟩ := k3 cc δ hc N N' hN hN' _ a.1 b
    exact ⟨W, w1, w2, fun g g' L L' hL hL' =>
      ⟨(w3 g g' L L' hL hL').1, by rw [(w3 g g' L L' hL hL').2, hsc g g' L L' hL hL']⟩⟩
  have hTT := fun N N' => (GlobalTheory.ThetaLevels.levels_closed D cc δ hc N N').1
  have hmove : ∀ N N', Even N → Even N' → ∀ (g h : GA D N) (g' h' : GA D N') L L₁ L' L₁',
      Moves D (g : GL (Fin N) (AE D)) L → Moves D (h : GL (Fin N) (AE D)) L₁ →
      Moves D (g' : GL (Fin N') (AE D)) L' → Moves D (h' : GL (Fin N') (AE D)) L₁' →
      e N N' L₁ L₁' = ((scal κ (g⁻¹ * h) (g'⁻¹ * h') : ℂˣ) : ℂ) •
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (La D (tor0 D cc δ) L₁ L₁') (e N N' L L') := by
    intro N N' hN hN' g h g' h' L L₁ L' L₁' m1 m2 m3 m4
    obtain ⟨W, -, -, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    obtain ⟨M, hM⟩ := exists_moves (g⁻¹ * h)
    obtain ⟨M', hM'⟩ := exists_moves (g'⁻¹ * h')
    have s0 := sd_of_moves (moves_one D N)
    have s0' := sd_of_moves (moves_one D N')
    have hI := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _ (Or.inr ⟨_, _, s0, s0', rfl⟩)
      (Or.inr ⟨_, _, sd_of_moves hM, sd_of_moves hM', rfl⟩) _ a.1).2.1
    have hio := GlobalTheory.WeilInter.om_iop D cc δ hc (GlobalTheory.InertSign.delta_ne_zero hc) N N' _ W g 1 (g⁻¹ * h) g' 1 (g'⁻¹ * h')
      _ L M L₁ _ L' M' L₁' (moves_one D N) (moves_one D N') (by rwa [mul_one]) (by rwa [mul_one]) hM hM'
      (by rwa [mul_inv_cancel_left]) (by rwa [mul_inv_cancel_left]) _ a.1
    rw [← (w h h' _ _ m2 m4).2, ← (w g g' _ _ m1 m3).2, ← hio]
    conv_lhs => rw [← mul_inv_cancel_left g h, ← mul_inv_cancel_left g' h', W.mul _ _ _ _ _ (hTT N N' _ _ s0 s0' _ a.1),
      (w _ _ _ _ hM hM').2, hsc _ _ _ _ hM hM']
    exact W.smul _ _ _ _ (hTT N N' _ _ (sd_of_moves hM) (sd_of_moves hM') _ hI)
  refine ⟨χ, e, hχ, fun N N' L L' ⟨hN, hN', hL, hL'⟩ => ?_, fun N N' L L' hN hN' γ γ' => ?_,
    fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L hL
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L' hL'
    obtain ⟨W, -, -, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    have hI := (GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' _ _
      (Or.inr ⟨_, _, sd_of_moves (moves_one D N), sd_of_moves (moves_one D N'), rfl⟩)
      (Or.inr ⟨_, _, hL, hL', rfl⟩) _ a.1).2.1
    change e N N' L L' ∈ Th D (tor0 D cc δ) L L' ∧ e N N' L L' ≠ 0 ∧ ∃ M : IntermediateField ℚ ℂ,
      FiniteDimensional ℚ M ∧ CoefIn D (e N N' L L') M
    rw [hsc g g' L L' hg hg']
    exact ⟨GlobalTheory.InertSign.ThSp_smul _ hI, smul_ne_zero (Units.ne_zero _) (lattice_facts hc a.1 b hg hg').1,
      exists_coef_field D cc δ hc t0 ht0 N N' (hN.mul_right _) _ a L L' hL hL' _ (w g g' L L' hg hg').1⟩
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨γA, hγ⟩ := exists_rat γ
    obtain ⟨γA', hγ'⟩ := exists_rat γ'
    obtain ⟨W, w1, w2, w⟩ := hW N N' hN hN'
    obtain ⟨a, b⟩ := he0 N N' (hN.mul_right _)
    have hT := hTT N N' _ _ (sd_of_moves (moves_one D N)) (sd_of_moves (moves_one D N')) _ a.1
    have := GlobalTheory.RatEqui.oddEq_of_even D cc δ hc t0 ht0 N N' hN hN' _ a W γA γA' _ _ (fun _ => 0) (fun _ => 0) hγ hγ' w1 w2
      _ (W.maps g g' _ hT)
    change pull D (tor0 D cc δ) _ _ (e N N' _ _) = e N N' _ _
    rw [← (w _ _ _ _ (moves_smulLat hγ hg) (moves_smulLat hγ' hg')).2, W.mul _ _ _ _ _ hT, this, (w _ _ _ _ hg hg').2]
    funext z
    simp
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨h', hh'⟩ := exists_moves_of_selfDual D N' L''.1 L''.2
    change e N N' _ _ = fun z => χ _ ^ _ * Iop D (tor0 D cc δ) _ _ (e N N' _ _) z
    rw [hmove N N' hN hN' g g g' h' _ _ _ _ hg hg hg' hh', hdet _ _ _ _ _ hg' hh', scal, inv_mul_cancel g]
    funext z
    simp
  · obtain ⟨g, hg⟩ := exists_moves_of_selfDual D N L.1 L.2
    obtain ⟨g', hg'⟩ := exists_moves_of_selfDual D N' L'.1 L'.2
    obtain ⟨h, hh⟩ := exists_moves_of_selfDual D N L₁.1 L₁.2
    change e N N' _ _ = fun z => χ _ ^ _ * Iop D (tor0 D cc δ) _ _ (e N N' _ _) z
    rw [hmove N N' hN hN' g h g' g' _ _ _ _ hg hh hg' hg', hdet _ _ _ _ _ hg hh, scal, inv_mul_cancel g']
    funext z
    simp

end GlobalTheory.TrueTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatumStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaVectorFamily_of_curveDatum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ ∧ vec22 D (tor0 D cc δ) e ∧ eq22 D (tor0 D cc δ) χ e := by
  first | exact @GlobalTheory.TrueTheta.exists_family_of_curve | exact GlobalTheory.TrueTheta.exists_family_of_curve | (intros; apply GlobalTheory.TrueTheta.exists_family_of_curve <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesEqMassesOfUnfold
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

namespace GlobalTheory.Mem.VolMass

theorem volumes_eq_masses_of_unfold :
    (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D :=
  fun hU D hV =>
    have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie hV
    StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
      (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
        (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D))

end GlobalTheory.Mem.VolMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelsSeed
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainModels

theorem models_seed : GlobalTheory.Published.DiscreteSeriesExists → ∀ D : D7, HostHyp D → Formalism.IndefR.Seed.ModY D ∧
    ∀ (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x : D.host.E, ∃ y : Ks, algebraMap Ks D.what₂.LL y = D.embE x) →
      ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ),
        Formalism.IndefR.Seed.ModWAt D.what₂.embLL MW ∧ GlobalTheory.RealGeo.FrameKs Ks MW := by
  intro h D _
  exact exists_models h D

end GlobalTheory.ChainModels
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemisimplificationMatrixRepSameCharpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemisimplificationMatrixRepSameCharpoly
noncomputable section

namespace GlobalTheory.SemisimplificationExists

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem exists_semisimplification : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k),
    ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧
      ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly :=
  fun ρ => GlobalTheory.RowPar.exists_ss ρ

end GlobalTheory.SemisimplificationExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemisimplificationMatrixRepSameCharpolyStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semisimplification_matrix_rep_same_charpoly : ∀ {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k), ∃ ρ' : Γ →* GL (Fin a) k, IsSSRep ρ' ∧ ρ.ker ≤ ρ'.ker ∧ ∀ g, (ρ' g : Matrix (Fin a) (Fin a) k).charpoly = (ρ g : Matrix (Fin a) (Fin a) k).charpoly := by
  first | exact @GlobalTheory.SemisimplificationExists.exists_semisimplification | exact GlobalTheory.SemisimplificationExists.exists_semisimplification | (intros; apply GlobalTheory.SemisimplificationExists.exists_semisimplification <;> assumption)
end
end
