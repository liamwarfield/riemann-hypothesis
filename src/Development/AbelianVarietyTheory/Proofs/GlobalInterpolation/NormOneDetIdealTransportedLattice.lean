module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationOperatorsActionOnRowWeight
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneDetIdealTransportedLattice
open NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

namespace GlobalTheory.CharValCompare

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.IndefiniteRowSideFullHecke

section Pull

variable {E E' : Type} [Field E] [Field E'] (e : E ≃+* E')

theorem map_osmul (c : 𝓞 E) (a : E) : e (c • a) = RingOfIntegers.mapRingEquiv e c • e a := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  rfl

def pull (I : Submodule (𝓞 E') E') : Submodule (𝓞 E) E where
  carrier := {x | e x ∈ I}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show e (a + b) ∈ I
    rw [e.map_add]
    exact I.add_mem ha hb
  smul_mem' := fun c a ha => by
    show e (c • a) ∈ I
    rw [map_osmul]
    exact I.smul_mem _ ha

theorem mem_pull (I : Submodule (𝓞 E') E') (x : E) : x ∈ pull e I ↔ e x ∈ I := Iff.rfl

theorem pull_one : pull e 1 = 1 := by
  ext x
  rw [mem_pull, Submodule.mem_one, Submodule.mem_one]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨RingOfIntegers.mapRingEquiv e.symm r, by rw [← e.symm_apply_apply x, ← hr]; rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨RingOfIntegers.mapRingEquiv e r, rfl⟩

theorem pull_norm (c : E → E) (c' : E' → E') (h : ∀ x, e (c x) = c' (e x)) {I : Submodule (𝓞 E') E'}
    (hI : ∃ J : Submodule (𝓞 E') E', (∀ x, x ∈ J ↔ c' x ∈ I) ∧ I * J = 1) :
    ∃ J : Submodule (𝓞 E) E, (∀ x, x ∈ J ↔ c x ∈ pull e I) ∧ pull e I * J = 1 := by
  obtain ⟨J, hJ, hIJ⟩ := hI
  refine ⟨pull e J, fun x => by rw [mem_pull, mem_pull, hJ, h], le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro x hx y hy
    rw [← pull_one e, mem_pull, map_mul, ← hIJ]
    exact Submodule.mul_mem_mul hx hy
  · rw [Submodule.one_le]
    have h1 : ∀ z ∈ I * J, e.symm z ∈ pull e I * pull e J := by
      intro z hz
      refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) fun a b ha hb => ?_
      · rw [map_mul]
        exact Submodule.mul_mem_mul (by simpa [mem_pull] using ha) (by simpa [mem_pull] using hb)
      · rw [e.symm.map_add]
        exact add_mem ha hb
    simpa using h1 1 (hIJ ▸ Submodule.mem_one.2 ⟨1, map_one _⟩)

end Pull

section Vp

variable {E : Type} [Field E] [NumberField E] [StarRing E]


end Vp

section Val

variable {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ)



end Val

section Chi

variable {D : D7} {X : Fields} (s : Seam D X) {χ : TaylorLogMetric.IdE D → ℂ}

theorem mem_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (y : Fin n → D.host.E) :
    y ∈ s.lat N ↔ (fun i => s.iE.symm (y i)) ∈ N := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      simpa using hx
    | zero =>
      convert N.zero_mem using 1
      funext i
      exact map_zero _
    | add a b _ _ ha hb =>
      convert N.add_mem ha hb using 1
      funext i
      exact map_add _ _ _
    | smul c a _ ha =>
      convert N.smul_mem (RingOfIntegers.mapRingEquiv s.iE.symm c) ha using 1
      funext i
      exact map_osmul s.iE.symm c (a i)
  · intro hy
    exact Submodule.subset_span ⟨_, hy, funext fun i => s.iE.apply_symm_apply _⟩

theorem detId_lat {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) :
    TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N) = pull s.iE.symm (detI N) := by
  apply le_antisymm
  · rw [TaylorLogMetric.detId, Submodule.span_le]
    rintro _ ⟨A, hA, rfl⟩
    refine Submodule.subset_span ⟨A.map s.iE.symm, fun v hv => ?_, (s.iE.symm : D.host.E →+* X.E).map_det A⟩
    have h1 := (mem_lat s N _).1 (hA (fun i => s.iE (v i)) fun i _ => by
      have := hv i (Set.mem_univ _)
      rw [← pull_one s.iE] at this
      exact this)
    convert h1 using 1
    funext i
    simp [Matrix.mulVec, dotProduct]
  · have : detI N ≤ pull s.iE (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
      rw [detI, Submodule.span_le]
      rintro _ ⟨A, hA, rfl⟩
      refine Submodule.subset_span ⟨A.map s.iE, fun v hv => (mem_lat s N _).2 ?_, (s.iE : X.E →+* D.host.E).map_det A⟩
      have h1 := hA (fun i => s.iE.symm (v i)) fun i _ => by
        have := hv i (Set.mem_univ _)
        rw [← pull_one s.iE.symm] at this
        exact this
      convert h1 using 1
      funext i
      simp [Matrix.mulVec, dotProduct]
    intro y hy
    simpa [mem_pull] using this hy

variable {s}

theorem normOne_idealPreimageUnderRingEquiv (hs : s.Ok) {I : Submodule (𝓞 X.E) X.E} (h : NormOne I) : TaylorLogMetric.N1 D (pull s.iE.symm I) :=
  pull_norm s.iE.symm D.host.conj star (fun x => by rw [RingEquiv.symm_apply_eq, hs.2, s.iE.apply_symm_apply]) h

theorem normOne_detIdeal_transportedLattice (hs : s.Ok) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    TaylorLogMetric.N1 D (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) := by
  rw [detId_lat]
  exact normOne_idealPreimageUnderRingEquiv hs (normOne_detI hN)

end Chi

section Parts

variable {D : D7} {Z : Dat} {s : Seam D Z.X} {χ : TaylorLogMetric.IdE D → ℂ}
  {sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)} {S : Set ℕ}
  {mu : Tup Z.X.F Z.X.E Z.X.K S} {cst : LocCst Z.X (rowSG Z.Pr sel mu)}

theorem T_mem (hZ : Z.Ok) {u : Z.Pr.Word} {P : HeightOneSpectrum (𝓞 Z.X.E)} (hP : P ∈ Z.Pr.vT u) :
    ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ P.asIdeal := by
  rw [← hZ.primes.piT_norm u]
  exact Ideal.mul_mem_right _ _ (decoFin_mem_of_mem_divs hP)

end Parts

end GlobalTheory.CharValCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsFamPOfKits
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX


open Classical in
def cutScale {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y) (x : ℝ) : Scale :=
  S.scale (if x1 < x ∧ x ∈ S.Win then x else y) eps (by split_ifs with h; exacts [hx.trans h.1, hx.trans_le hy]) h0 h1

private theorem cutScale_alt {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (x : ℝ) (h : x1 < x) (hw : x ∈ S.Win) : (cutScale S h0 h1 hx hy x).x = x := if_pos ⟨h, hw⟩

private theorem cutScale_ge {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (x : ℝ) : x1 ≤ (cutScale S h0 h1 hx hy x).x := by
  unfold cutScale Scales.scale
  dsimp only
  split_ifs with h
  exacts [h.1.le, hy]

private theorem cutScale_mem {eps x1 la y : ℝ} (S : Scales la) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hx : 1 < x1) (hy : x1 ≤ y)
    (hw : y ∈ S.Win) (x : ℝ) : S.Mem (cutScale S h0 h1 hx hy x) := by
  refine ⟨rfl, ?_⟩
  unfold cutScale Scales.scale
  dsimp only
  split_ifs with h
  exacts [h.2, hw]

theorem Kit.bTopOf_eq {C : FC} {cD ch : ℝ} {s : Scale} (k : Kit C cD ch s) (i i' : k.Ix) :
    bTopOf (k.pt i).L = bTopOf (k.pt i').L := by
  unfold bTopOf
  rw [(k.val i).La_eq, (k.val i').La_eq, k.sc_eq i, k.sc_eq i', (k.same i i').1]

theorem bTopOf_ge {D : D7} (L : SizeData₂ D) (h : L.sc.x ^ L.sc.eps ≤ L.LaG) :
    L.sc.b' + 2 * (D.R.n : ℝ) * L.sc.delta1 * L.sc.x ^ (2 * L.sc.eps) * L.sc.b' / (D.R.k : ℝ) ≤ bTopOf L := by
  have hsx : (0 : ℝ) < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a Scale.b Scale.X'
    positivity
  have hd : 0 ≤ L.sc.delta1 := by
    unfold Scale.delta1
    positivity
  have e : L.sc.x ^ (2 * L.sc.eps) = L.sc.x ^ L.sc.eps * L.sc.x ^ L.sc.eps := by
    rw [two_mul, Real.rpow_add hsx]
  unfold bTopOf
  rw [e, ← mul_assoc]
  gcongr

def famOfKits {eps : ℝ} (C : FC) (cD ch x1 : ℝ) (hx1 : 1 < x1) (hS : Std C) (hG : C.GK.Nonneg)
    (J : ℝ) (Wn : Set ℝ) (hW : ∀ y : ℝ, ∃ x ∈ Wn, y ≤ x)
    (s : ℝ → Scale) (he : ∀ x, (s x).eps = eps) (hJ : ∀ x, (s x).J = J) (hs : ∀ x, x1 < x → x ∈ Wn → (s x).x = x)
    (k : ∀ x, Kit C cD ch (s x)) (nu : ∀ x i, NumAt C ((k x).pt i).L) : FamP eps where
  x1 := x1
  one_lt_family_threshold := hx1
  Ix x := {_i : (k x).Ix // x ≤ x1 ∨ x ∈ Wn}
  Win := Wn
  Win_unb := hW
  Ix_win x hx := ⟨⟨(k x).ne.some, Or.inr hx⟩⟩
  Ix_zero := ⟨⟨(k 0).ne.some, Or.inl (zero_le_one.trans hx1.le)⟩⟩
  D x i := ((k x).pt i.1).D
  L x i := ((k x).pt i.1).L
  L_x x i hx := by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)]
  L_eps x i := by rw [(k x).sc_eq i.1, he x]
  J := J
  L_J x i := by rw [(k x).sc_eq i.1, hJ x]
  R_eq x i i' := ((k x).same i.1 i'.1).1
  TTn x := ((k x).pt (k x).ne.some).D.host.TT.image Formalism.HC.Frame.A.val
  TT_eq x i := ((k x).same i.1 _).2.1
  realisedChain_torus_eq x i i' := ((k x).same i.1 i'.1).2.2.1
  q_eq x i i' := ((k x).same i.1 i'.1).2.2.2.1
  d_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.1
  QS_eq x i i' := ((k x).same i.1 i'.1).QS_eq
  art_eq x i i' := ((k x).same i.1 i'.1).art_eq
  rd_eq x i i' := ((k x).same i.1 i'.1).rd_eq
  Co := C.P.Cpde
  o_le_Co x i _ := ((k x).val i.1).host.o_le
  QS_le_Co x i _ := ((k x).val i.1).host.QS_le
  g_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.1
  pde_eq x i i' := ⟨((k x).same i.1 i'.1).2.2.2.2.2.2.1, ((k x).same i.1 i'.1).2.2.2.2.2.2.2.1⟩
  W x := (k x).W
  eW x i := (k x).eW i.1
  eW_code x i i' := (k x).eW_code i.1 i'.1
  CGam := C.CGam
  CGam_eq x i := (nu x i.1).CGam_eq
  Cc := C.Cc
  Cc_eq x i := (nu x i.1).Cc_eq
  Ct := C.Ct
  Ct_eq x i := (nu x i.1).Ct_eq
  CT2 := C.CT2
  secondConstant_eq x i := (nu x i.1).secondConstant_eq
  bTop x := bTopOf ((k x).pt (k x).ne.some).L
  bTop_eq x hx i := by
    rw [(k x).bTopOf_eq _ i.1]
    unfold bTopOf
    rw [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)],
      show ((k x).pt i.1).L.sc.eps = eps by rw [(k x).sc_eq i.1, he x]]
  bTop_ge x hx i := by
    rw [(k x).bTopOf_eq _ i.1]
    have h := bTopOf_ge _ (nu x i.1).LaG_ge
    rwa [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)],
      show ((k x).pt i.1).L.sc.eps = eps by rw [(k x).sc_eq i.1, he x]] at h
  bT_le x _ i t := by
    rw [(k x).bTopOf_eq _ i.1]
    exact (nu x i.1).bT_le t
  coverS x _ i0 u0 hu := by
    obtain ⟨i, hi⟩ := (k x).cover_weights i0.1 u0 hu
    exact ⟨⟨i, i0.2⟩, hi⟩
  params x _ i := (nu x i.1).params
  PK := C.PK
  params_K x _ i := (nu x i.1).params_K
  parT x _ i := (nu x i.1).parT
  PT := C.PT
  parT_K x _ i := (nu x i.1).parT_K
  CTu := C.CTu
  sizes x _ i := (nu x i.1).sizes
  ties x i := ((k x).pt i.1).xa.ties
  gatT x i := ((k x).pt i.1).gatT
  X x i := ((k x).pt i.1).xa.X
  Gx x i := ((k x).pt i.1).ta.Gx
  Gy x i := ((k x).pt i.1).ta.Gy
  GK := C.GK
  GK_nonneg := hG
  supp_sat x _ i := ((k x).pt i.1).ta.supp_sat
  tw_supp x _ i := ((k x).pt i.1).ta.tw_supp
  fills x _ i := ((k x).pt i.1).ta.fills
  lats0 x _ i := ((k x).pt i.1).ta.lats0
  latTied x _ i := ((k x).pt i.1).ta.latTied
  Csz := C.Csz
  nuDef x _ i := ((k x).pt i.1).xa.nuDef
  nprimeDef x _ i := ((k x).pt i.1).xa.nprimeDef
  rrDef x _ i := ((k x).pt i.1).xa.rrDef
  h_eq x _ i := ((k x).pt i.1).xa.h_eq
  cX := C.cX
  ex x _ i := ((k x).pt i.1).xa.ex
  rho_le x hx i := by
    have h := (nu x i.1).rho_le
    rwa [show ((k x).pt i.1).L.sc.x = x by rw [(k x).sc_eq i.1, hs x hx (i.2.resolve_left hx.not_ge)]] at h
  Cr := C.Cr
  one_le_Cr := hS.1.2.2.2.2.2.2.1.ge
  drop_iff x _ i := ((k x).pt i.1).ta.drop_iff
  fixed := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, _⟩ := hS.1
    exact ⟨a1, a2, a3, a4, a5, a6, a7, fun x _ i => ⟨(nu x i.1).CnW_eq.trans a8, (nu x i.1).eP_eq ▸ a9⟩⟩
  eta_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.1
  Sc_shared x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.1
  hP_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.1
  bs_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.1
  off_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.1
  kapI_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  ep_eq x i i' := ((k x).same i.1 i'.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exists_famP_of_kits : ∀ (eps : ℝ) (C : FC) (cD ch x1 la : ℝ) (S : Scales la), 0 < eps → eps < 1 / 52 → 1 < x1 → 1 ≤ la → Std C → C.GK.Nonneg → ∀ k : ∀ s : Scale, s.eps = eps → x1 ≤ s.x → S.Mem s → Kit C cD ch s, (∀ s h h' h'' i, Nonempty (NumAt C ((k s h h' h'').pt i).L)) → ∃ Fm : FamP eps, Fm.x1 = x1 ∧ Fm.cPre = C.cPre ∧ Fm.cOut = C.cOut.set 15 C.P.Cpde ∧ Fm.cMid = C.cMid ∧ Fm.cLast = C.cLast ∧ Fm.CTu = C.CTu ∧ (∀ Q : PtProp, (∀ s h h' h'' i, ((k s h h' h'').pt i).Has Q) → classOf Q Fm) ∧ (∀ Rr : ∀ (D : D7) (L : SizeData₂ D), G.Inst D L → Prop, (∀ s h h' h'' i, Rr ((k s h h' h'').pt i).D ((k s h h' h'').pt i).L ((k s h h' h'').pt i).ta.Gx) → ∀ x, ∀ i : Fm.Ix x, Rr (Fm.D x i) (Fm.L x i) (Fm.Gx x i)) ∧ Fm.J = S.J ∧ Fm.Win = S.Win ∧ Fm.Co = C.P.Cpde := by
  intro eps C cD ch x1 la S h0 h1 hx hla hS hG k hN
  obtain ⟨y, hw, hy⟩ := S.unb hla x1
  have hJ : S.J ≤ C.P.Cpde := by
    have k0 := k (cutScale S h0 h1 hx hy 0) rfl (cutScale_ge S h0 h1 hx hy 0) (cutScale_mem S h0 h1 hx hy hw 0)
    have h := (k0.val k0.ne.some).host.J_le
    rwa [k0.sc_eq] at h
  refine ⟨famOfKits C cD ch x1 hx hS hG S.J S.Win (S.unb hla) (cutScale S h0 h1 hx hy) (fun _ => rfl) (fun _ => rfl)
    (cutScale_alt S h0 h1 hx hy)
    (fun x => k (cutScale S h0 h1 hx hy x) rfl (cutScale_ge S h0 h1 hx hy x) (cutScale_mem S h0 h1 hx hy hw x))
    (fun x i => (hN _ _ _ _ i).some),
    rfl, rfl, ?_, rfl, rfl, rfl, fun Q hQ x _ i => hQ _ _ _ _ i.1, fun Rr hR x i => hR _ _ _ _ i.1, rfl, rfl, rfl⟩
  rw [← congrArg (C.cOut.set 15) (max_eq_left hJ)]
  rfl

end GlobalTheory.EX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGap
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGap
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem nodeGap_poly {x Y n f m k r t N M L S c₁ c₂ H : ℝ} (hx : 200 ≤ x) (hY : 1 ≤ Y)
    (hn0 : 0 ≤ n) (hf0 : 0 ≤ f) (hm1 : 1 ≤ m) (hk0 : 0 ≤ k) (hr0 : 0 ≤ r) (ht0 : 0 ≤ t) (hN0 : 0 ≤ N) (hM0 : 0 ≤ M)
    (hL0 : 0 ≤ L) (hS0 : 0 ≤ S)
    (hn : n ≤ x ^ 3) (hf : f ≤ x ^ 3) (hm : m ≤ x) (hk : k ≤ x ^ 5) (hr : r ≤ x ^ 5) (ht : t ≤ x ^ 401)
    (hN : N ≤ x ^ 402) (hM : M ≤ x ^ 402) (hL : L ≤ x) (hS : S ≤ x ^ 6 * Y) (h₁ : c₁ ≤ x) (h₂ : c₂ ≤ x)
    (hH : x ^ 1300 * Y ≤ H) :
    12 * ((n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L)) / m) + 2 * t + 8 ≤ H ∧ k * t * L ≤ H ∧
      c₁ * r ^ 19 * f ^ 5 * L ≤ H ∧ 4 * N ^ 3 + 2 * t + 6 ≤ H ∧ c₂ * k * m ^ ((9 : ℝ) / 2) ≤ H ∧
      2 * M ^ 3 + t + 3 ≤ H ∧ 120 * r * m ^ ((3 : ℝ) / 2) ≤ H ∧ N * m ^ 10 ≤ H ∧ 16 * m * N ≤ H := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have mono : ∀ a b : ℕ, a ≤ b → x ^ a ≤ x ^ b := fun a b h => pow_le_pow_right₀ hx1 h
  have hP : 0 ≤ x ^ 1299 := by positivity
  have hQ : x ^ 1299 ≤ x ^ 1299 * Y := le_mul_of_one_le_right hP hY
  have hH' : 200 * (x ^ 1299 * Y) ≤ H := by
    refine le_trans ?_ hH
    have : x ^ 1300 * Y = x * (x ^ 1299 * Y) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  have h1 : 1 ≤ x ^ 1299 := one_le_pow₀ hx1
  have ht' : t ≤ x ^ 1299 := ht.trans (mono _ _ (by norm_num))
  have hm92 : m ^ ((9 : ℝ) / 2) ≤ x ^ 5 := by
    calc m ^ ((9 : ℝ) / 2) ≤ m ^ ((5 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = m ^ 5 := Real.rpow_natCast _ _
      _ ≤ x ^ 5 := by gcongr
  have hm32 : m ^ ((3 : ℝ) / 2) ≤ x ^ 2 := by
    calc m ^ ((3 : ℝ) / 2) ≤ m ^ ((2 : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = m ^ 2 := Real.rpow_natCast _ _
      _ ≤ x ^ 2 := by gcongr
  have hm0 : 0 ≤ m := by linarith
  have hN3 : N ^ 3 ≤ x ^ 1299 := by
    calc N ^ 3 ≤ (x ^ 402) ^ 3 := by gcongr
      _ = x ^ 1206 := by ring
      _ ≤ _ := mono _ _ (by norm_num)
  have hM3 : M ^ 3 ≤ x ^ 1299 := by
    calc M ^ 3 ≤ (x ^ 402) ^ 3 := by gcongr
      _ = x ^ 1206 := by ring
      _ ≤ _ := mono _ _ (by norm_num)
  refine ⟨?_, ?_, ?_, by linarith, ?_, by linarith, ?_, ?_, ?_⟩
  · have hA : n * t ^ 2 * (N + t) * L ^ 2 ≤ 2 * x ^ 1299 := by
      have ht2 : t ≤ x ^ 402 := ht.trans (mono _ _ (by norm_num))
      calc n * t ^ 2 * (N + t) * L ^ 2 ≤ x ^ 3 * (x ^ 401) ^ 2 * (x ^ 402 + x ^ 402) * x ^ 2 := by gcongr
        _ = 2 * x ^ 1209 := by ring
        _ ≤ _ := by have := mono 1209 1299 (by norm_num); linarith
    have hB : k * n ^ 2 * (S + t + L) ≤ 3 * (x ^ 1299 * Y) := by
      have hY0 : 0 ≤ Y := by linarith
      have hW : x ^ 401 ≤ x ^ 401 * Y := le_mul_of_one_le_right (by positivity) hY
      have hS' : S ≤ x ^ 401 * Y := hS.trans (mul_le_mul_of_nonneg_right (mono _ _ (by norm_num)) hY0)
      have ht2 : t ≤ x ^ 401 * Y := ht.trans hW
      have hL2 : L ≤ x ^ 401 * Y := by
        have := mono 1 401 (by norm_num)
        rw [pow_one] at this
        exact hL.trans (this.trans hW)
      calc k * n ^ 2 * (S + t + L) ≤ x ^ 5 * (x ^ 3) ^ 2 * (x ^ 401 * Y + x ^ 401 * Y + x ^ 401 * Y) := by gcongr
        _ = 3 * (x ^ 412 * Y) := by ring
        _ ≤ _ := by
          have := mul_le_mul_of_nonneg_right (mono 412 1299 (by norm_num)) hY0
          linarith
    have hD : (n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L)) / m ≤
        n * t ^ 2 * (N + t) * L ^ 2 + k * n ^ 2 * (S + t + L) := div_le_self (by positivity) hm1
    linarith
  · have : k * t * L ≤ x ^ 1299 := by
      calc k * t * L ≤ x ^ 5 * x ^ 401 * x := by gcongr
        _ = x ^ 407 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : c₁ * r ^ 19 * f ^ 5 * L ≤ x ^ 1299 := by
      calc c₁ * r ^ 19 * f ^ 5 * L ≤ x * (x ^ 5) ^ 19 * (x ^ 3) ^ 5 * x := by gcongr
        _ = x ^ 112 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : c₂ * k * m ^ ((9 : ℝ) / 2) ≤ x ^ 1299 := by
      calc c₂ * k * m ^ ((9 : ℝ) / 2) ≤ x * x ^ 5 * x ^ 5 := by gcongr
        _ = x ^ 11 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : r * m ^ ((3 : ℝ) / 2) ≤ x ^ 1299 := by
      calc r * m ^ ((3 : ℝ) / 2) ≤ x ^ 5 * x ^ 2 := by gcongr
        _ = x ^ 7 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : N * m ^ 10 ≤ x ^ 1299 := by
      calc N * m ^ 10 ≤ x ^ 402 * x ^ 10 := by gcongr
        _ = x ^ 412 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith
  · have : m * N ≤ x ^ 1299 := by
      calc m * N ≤ x * x ^ 402 := by gcongr
        _ = x ^ 403 := by ring
        _ ≤ _ := mono _ _ (by norm_num)
    linarith

theorem szRow_nodeGap : SzRow (fun C D L => (12 * L.sc.b / lStar L + 2 * D.R.t + 8 ≤ h0 L ∧ (D.R.k : ℝ) * D.R.t * L.sc.L ≤ h0 L ∧ C.P.Ch0r * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ h0 L ∧ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ h0 L ∧ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ h0 L ∧ C.P.Ch0k * D.R.k * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) ≤ h0 L ∧ 2 * (Mrt D : ℝ) ^ 3 + D.R.t + 3 ≤ h0 L ∧ 120 * (D.R.r : ℝ) * (qSig D : ℝ) ^ ((3 : ℝ) / 2) ≤ h0 L ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ h0 L ∧ 16 * (qSig D : ℝ) * D.R.N D.R.m ≤ h0 L)) := by
  intro eps he0 he1 C _
  obtain ⟨x1, hx1⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps he0 he1
  refine ⟨0, fun cD hcD => ⟨max (1300 + cD) (406 * |C.P.CCount|), fun ch hch =>
    ⟨max (max x1 200) (max C.P.Ch0r C.P.Ch0k), fun D L hε hx hV => ?_⟩⟩⟩
  simp only [max_le_iff, ge_iff_le] at hx hch
  obtain ⟨⟨hxa, hxb⟩, hxc, hxd⟩ := hx
  obtain ⟨hf, hm, hr, hkr, -, hL, hL1, -, -, -, -, -, -, ht, hN, -, -⟩ := hx1 L.sc D.R hε hxa hV.ranks
  have hxone : 1 ≤ L.sc.x := by linarith
  have hxpos : 0 < L.sc.x := by linarith
  have cast : ∀ a : ℕ, L.sc.x ^ (a : ℝ) = L.sc.x ^ a := fun a => Real.rpow_natCast _ _
  have hf' : (D.R.f : ℝ) ≤ L.sc.x ^ 3 := by rw [← cast]; exact_mod_cast hf
  have hr' : (D.R.r : ℝ) ≤ L.sc.x ^ 5 := by rw [← cast]; exact_mod_cast hr
  have ht' : (D.R.t : ℝ) ≤ L.sc.x ^ 401 := by rw [← cast]; exact_mod_cast ht
  have hN' : (D.R.N D.R.m : ℝ) ≤ L.sc.x ^ 402 := by rw [← cast]; exact_mod_cast hN
  have hk' : (D.R.k : ℝ) ≤ L.sc.x ^ 5 := le_trans (by exact_mod_cast hkr) hr'
  have hnf : (D.R.n : ℝ) ≤ D.R.f := by
    have : D.R.n ≤ D.R.f := by unfold Ranks.f; omega
    exact_mod_cast this
  have hm2 := D.R.two_le_m
  have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hMN : (Mrt D : ℝ) ≤ D.R.N D.R.m := by
    have : Mrt D ≤ D.R.N D.R.m := by
      unfold Mrt Ranks.N Ranks.r
      rw [Nat.mul_add, Nat.mul_one]; omega
    exact_mod_cast this
  have hY : 1 ≤ L.sc.x ^ cD := Real.one_le_rpow hxone hcD
  have hDel : ((Delv L.sc cD : ℕ) : ℝ) ≤ 2 * L.sc.x ^ cD := by
    have := Nat.ceil_lt_add_one (a := L.sc.x ^ cD) (by linarith)
    unfold Delv; linarith
  have hSc : L.Sc = (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) := by
    rw [L.Sc_eq, hV.Del_eq]; push_cast; ring
  have hS0 : 0 ≤ L.Sc := by rw [hSc]; positivity
  have hS : L.Sc ≤ L.sc.x ^ 6 * L.sc.x ^ cD := by
    rw [hSc]
    calc (D.R.k : ℝ) * (4 * ((Delv L.sc cD : ℕ) : ℝ)) ≤ L.sc.x ^ 5 * (4 * (2 * L.sc.x ^ cD)) := by gcongr
      _ = L.sc.x ^ 5 * 8 * L.sc.x ^ cD := by ring
      _ ≤ L.sc.x ^ 5 * L.sc.x * L.sc.x ^ cD := by gcongr; linarith
      _ = _ := by ring
  have hh0 : L.sc.x ^ ch ≤ h0 L := by
    have e : h0 L = (h0v L.sc ch : ℝ) := by
      unfold h0; rw [hV.eta_eq]; field_simp
    have := Nat.le_ceil (L.sc.x ^ ch)
    have h0' : (0 : ℝ) ≤ (⌈L.sc.x ^ ch⌉₊ : ℕ) := Nat.cast_nonneg _
    rw [e]; unfold h0v; push_cast; linarith
  have hH : L.sc.x ^ 1300 * L.sc.x ^ cD ≤ h0 L := by
    refine le_trans ?_ hh0
    rw [← cast, ← Real.rpow_add hxpos]
    exact Real.rpow_le_rpow_of_exponent_le hxone (by exact_mod_cast hch.1)
  obtain ⟨a1, a2, a3, a5, a6, a7, a8, a9, a10⟩ := nodeGap_poly (c₁ := C.P.Ch0r) (c₂ := C.P.Ch0k) hxb hY
    (Nat.cast_nonneg D.R.n) (Nat.cast_nonneg D.R.f) hm1 (Nat.cast_nonneg D.R.k) (Nat.cast_nonneg D.R.r)
    (Nat.cast_nonneg D.R.t) (Nat.cast_nonneg (D.R.N D.R.m)) (Nat.cast_nonneg (Mrt D)) (by linarith : 0 ≤ L.sc.L) hS0
    (hnf.trans hf') hf' hm hk' hr' ht' hN' (hMN.trans hN') hL hS hxc hxd hH
  refine ⟨?_, a2, a3, ?_, a5, a6, a7, a8, a9, a10⟩
  · have hb : 0 < L.sc.b := by unfold Scale.b; positivity
    refine le_trans (le_of_eq ?_) a1
    unfold lStar
    rw [div_div_eq_mul_div]
    field_simp
  · have hf1 : (1 : ℝ) ≤ D.R.f := by
      have : 1 ≤ D.R.f := le_trans (by omega) D.R.m_le_f
      exact_mod_cast this
    have hN1 : (1 : ℝ) ≤ D.R.N D.R.m := by
      have := D.R.m_add_three_le_k
      have : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; omega
      exact_mod_cast this
    have hB1 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hN1 hf1) hL1
    have hB : (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L ≤ L.sc.x ^ (406 : ℝ) := by
      calc (D.R.N D.R.m : ℝ) * D.R.f * L.sc.L ≤ L.sc.x ^ 402 * L.sc.x ^ 3 * L.sc.x := by gcongr
        _ = L.sc.x ^ 406 := by ring
        _ = _ := by rw [← cast]; norm_num
    calc _ ≤ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ |C.P.CCount| :=
          Real.rpow_le_rpow_of_exponent_le hB1 (le_abs_self _)
      _ ≤ (L.sc.x ^ (406 : ℝ)) ^ |C.P.CCount| := Real.rpow_le_rpow (by linarith) hB (abs_nonneg _)
      _ = L.sc.x ^ (406 * |C.P.CCount|) := (Real.rpow_mul hxpos.le _ _).symm
      _ ≤ L.sc.x ^ ch := Real.rpow_le_rpow_of_exponent_le hxone hch.2
      _ ≤ _ := hh0

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGapStatement
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_node_bounds_le_h0 : SzRow (fun C D L => (12 * L.sc.b / lStar L + 2 * D.R.t + 8 ≤ h0 L ∧ (D.R.k : ℝ) * D.R.t * L.sc.L ≤ h0 L ∧ C.P.Ch0r * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * L.sc.L ≤ h0 L ∧ ((D.R.N D.R.m : ℝ) * D.R.f * L.sc.L) ^ C.P.CCount ≤ h0 L ∧ 4 * (D.R.N D.R.m : ℝ) ^ 3 + 2 * D.R.t + 6 ≤ h0 L ∧ C.P.Ch0k * D.R.k * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) ≤ h0 L ∧ 2 * (Mrt D : ℝ) ^ 3 + D.R.t + 3 ≤ h0 L ∧ 120 * (D.R.r : ℝ) * (qSig D : ℝ) ^ ((3 : ℝ) / 2) ≤ h0 L ∧ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 ≤ h0 L ∧ 16 * (qSig D : ℝ) * D.R.N D.R.m ≤ h0 L)) := by
  first | exact @GlobalTheory.EX.szRow_nodeGap | exact GlobalTheory.EX.szRow_nodeGap | (intros; apply GlobalTheory.EX.szRow_nodeGap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsHcParamOfCode
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem exists_hcParam_of_code (R : Ranks) (D h : ℕ) (hD : 1 ≤ D) (hh : ((R.t : ℚ) + 3) / 2 ≤ h)
    (U0 UL B : ℤ) (h0 : ((R.k - 2 : ℕ) : ℚ) * (4 * (D : ℚ)) ≤ U0) (hL : UL < 0) (hB : -B ≤ UL)
    (w : Fin (R.k - 2) → Bool) :
    ∃ p : HCParam R, (∀ i : Fin (R.k - 1), p.v i = ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (D : ℚ))) ∧
      (∀ hk : 0 < R.k, p.u ⟨0, hk⟩ = U0 + 1 / 2 ∧ p.u ⟨R.k - 1, by omega⟩ = UL + 1 / 2) ∧
      (∀ (l : ℕ) (hl : l < R.k - 2), p.u ⟨l + 1, by omega⟩ =
        ((R.k - 2 - l : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨l, hl⟩ then (D : ℚ) else 0)) ∧
      ∀ j : Fin R.m, p.b j = B + (j.1 : ℚ) * (2 * h) ∧ p.e j = p.b j + h := by
  have hk5 : 5 ≤ R.k := by have := R.two_le_m; have := R.m_add_three_le_k; omega
  have hD' : (1 : ℚ) ≤ D := by exact_mod_cast hD
  let u : Fin R.k → ℚ := fun i =>
    if i.1 = 0 then U0 + 1 / 2 else
      if hi : i.1 - 1 < R.k - 2 then
        ((R.k - 2 - (i.1 - 1) : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨i.1 - 1, hi⟩ then (D : ℚ) else 0)
      else UL + 1 / 2
  have u0 : ∀ hk : 0 < R.k, u ⟨0, hk⟩ = U0 + 1 / 2 := fun hk => by simp [u]
  have uL : ∀ hk : R.k - 1 < R.k, u ⟨R.k - 1, hk⟩ = UL + 1 / 2 := fun hk => by
    have h1 : ¬ (R.k - 1 = 0) := by omega
    have h2 : ¬ (R.k - 1 - 1 < R.k - 2) := by omega
    simp only [u, h1, h2, if_false, dite_false]
  have um : ∀ (l : ℕ) (hl : l < R.k - 2) (hk : l + 1 < R.k), u ⟨l + 1, hk⟩ =
      ((R.k - 2 - l : ℕ) : ℚ) * (4 * (D : ℚ)) - 1 / 2 - (if w ⟨l, hl⟩ then (D : ℚ) else 0) := fun l hl hk => by
    simp only [u, Nat.add_one_ne_zero, Nat.add_sub_cancel, hl, if_false, dite_true]
  have hLq : (UL : ℚ) ≤ -1 := by exact_mod_cast (by omega : UL ≤ -1)
  have hBq : -(B : ℚ) ≤ UL := by exact_mod_cast hB
  refine ⟨⟨u, fun i => ((R.k - 2 - i.1 : ℕ) : ℚ) * (4 * (D : ℚ)), fun j => B + (j.1 : ℚ) * (2 * h),
    fun j => B + (j.1 : ℚ) * (2 * h) + h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun i => rfl, fun hk => ⟨u0 hk, uL _⟩, fun l hl => um l hl _, fun j => ⟨rfl, rfl⟩⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · rw [u0]; simp only [Nat.sub_zero]; linarith
    · have hl : l < R.k - 2 := by omega
      rw [um l hl]
      have : R.k - 2 - l = (R.k - 2 - (l + 1)) + 1 := by omega
      rw [this]; push_cast
      split_ifs <;> linarith
  · rintro ⟨l, hi⟩
    by_cases hl : l < R.k - 2
    · rw [um l hl]
      split_ifs <;> linarith
    · have e1 : l + 1 = R.k - 1 := by omega
      have e2 : R.k - 2 - l = 0 := by omega
      have : u ⟨l + 1, by omega⟩ = UL + 1 / 2 := by
        rw [← uL (by omega)]; congr 2
      simp only [this, e2]
      push_cast; linarith
  · intro hk hm
    rw [uL]; simp only [Nat.cast_zero]; linarith
  · intro j; linarith
  · intro j hj; push_cast; linarith
  · intro j; exact ⟨B + j.1 * (2 * h) + h, by push_cast; ring⟩
  · rintro ⟨i, hi⟩
    rcases i with _ | l
    · exact ⟨U0, u0 _⟩
    · by_cases hl : l < R.k - 2
      · rw [um l hl]
        split_ifs
        · exact ⟨((R.k - 2 - l : ℕ) : ℤ) * (4 * D) - 1 - D, by push_cast; ring⟩
        · exact ⟨((R.k - 2 - l : ℕ) : ℤ) * (4 * D) - 1, by push_cast; ring⟩
      · have e1 : l + 1 = R.k - 1 := by omega
        refine ⟨UL, ?_⟩
        rw [← uL (by omega)]; congr 2
  · intro i; exact ⟨((R.k - 2 - i.1 : ℕ) : ℤ) * (4 * D), by push_cast; ring⟩
  · intro j; exact ⟨B + j.1 * (2 * h), by push_cast; ring⟩

theorem hc_sizes (eps cD ch : ℝ) (h0 : 0 < eps) (h1 : eps < 1 / 52) (hcD : 0 ≤ cD) (hch : 402 ≤ ch) :
    ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R →
      1 ≤ Delv s cD ∧ ((R.t : ℚ) + 3) / 2 ≤ (⌈s.x ^ ch⌉₊ : ℕ) ∧
      (R.k : ℝ) * (4 * (Delv s cD : ℝ)) ≤ s.a ∧ (R.k : ℝ) ≤ s.b' / s.x ∧ 0 < s.b' ∧ 0 < s.b ∧ 0 < s.w'' R.n := by
  obtain ⟨x1, H1⟩ := GlobalTheory.T.scale_polynomial_quantities_comparison eps (cD + 6) 1 h0 one_pos
  obtain ⟨x2, H2⟩ := GlobalTheory.T.explicitRanks_basic_bounds_large_scale eps h0 h1
  refine ⟨max 8 (max x1 x2), fun s R he hx hR => ?_⟩
  have hx8 : 8 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx1 : x1 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, hS, -⟩ := H1 s he hx1
  obtain ⟨-, -, hr, hkr, -, -, -, -, -, -, -, -, -, ht, -⟩ := H2 s R he hx2 hR
  have hxp : 0 < s.x := by linarith
  have hx1' : 1 ≤ s.x := by linarith
  rw [Real.rpow_one] at hS
  have hb : 0 < s.b := Real.exp_pos _
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hxp.le _)
  have hXp : 0 < s.X' := by linarith
  have hk : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hD1 : 1 ≤ s.x ^ cD := Real.one_le_rpow hx1' hcD
  have h5 : 1 ≤ s.x ^ (5 : ℝ) := Real.one_le_rpow hx1' (by norm_num)
  have hsplit : s.x ^ (cD + 6) = s.x ^ cD * s.x ^ (5 : ℝ) * s.x := by
    rw [show cD + 6 = cD + 5 + 1 by ring, Real.rpow_add hxp, Real.rpow_add hxp, Real.rpow_one]
  have hDle : (Delv s cD : ℝ) ≤ 2 * s.x ^ cD := by
    have := Nat.ceil_lt_add_one (show 0 ≤ s.x ^ cD by linarith)
    unfold Delv; linarith
  have hb' : 0 < s.b' := div_pos (mul_pos hxp hb) hXp
  have hn : (0 : ℝ) < R.n := by
    have hnNat : 0 < R.n := by
      unfold Ranks.n
      have := R.two_le_m
      have := R.m_le_f
      omega
    exact_mod_cast hnNat
  refine ⟨?_, ?_, ?_, ?_, hb', hb, div_pos hb' (mul_pos hxp hn)⟩
  · exact Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 (by linarith)).ne'
  · have h401 : 1 ≤ s.x ^ (401 : ℝ) := Real.one_le_rpow hx1' (by norm_num)
    have h402 : s.x ^ (401 : ℝ) * s.x ≤ s.x ^ ch := by
      rw [← Real.rpow_add_one hxp.ne']
      exact Real.rpow_le_rpow_of_exponent_le hx1' (by linarith)
    have hc := Nat.le_ceil (s.x ^ ch)
    have : ((R.t : ℝ) + 3) / 2 ≤ (⌈s.x ^ ch⌉₊ : ℕ) := by nlinarith
    have h' : ((((R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((⌈s.x ^ ch⌉₊ : ℕ) : ℚ) : ℝ) := by push_cast; exact this
    exact_mod_cast h'
  · have hP : 0 ≤ s.x ^ cD * s.x ^ (5 : ℝ) := by positivity
    have e1 : (R.k : ℝ) * (4 * (Delv s cD : ℝ)) ≤ s.x ^ (5 : ℝ) * (4 * (2 * s.x ^ cD)) := by gcongr
    have e2 : s.x ^ (cD + 6) ≤ s.x ^ (cD + 6) * s.X' := le_mul_of_one_le_right (by positivity) hX
    have e3 : s.b ≤ s.a := le_mul_of_one_le_left hb.le hx1'
    have e4 : s.x ^ cD * s.x ^ (5 : ℝ) * 8 ≤ s.x ^ cD * s.x ^ (5 : ℝ) * s.x := by gcongr
    linarith
  · have e : s.b' / s.x = s.b / s.X' := by
      unfold Scale.b' Scale.a; field_simp
    rw [e, le_div_iff₀ hXp]
    refine le_trans ?_ hS
    gcongr
    exact le_trans hk (Real.rpow_le_rpow_of_exponent_le hx1' (by linarith))

theorem exists_hc_family : ∀ eps cD ch C8 : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (aT bT : H.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H → (∀ t, s.a ≤ (aT t : ℝ) ∧ s.b' ≤ (bT t : ℝ)) → ∀ (Tau : Type) [Fintype Tau] (eTau : Tau ≃ R.Psi), ∃ hcw : (Fin (R.k - 2) → Bool) → Tau → HCParam R, (∀ w, HCVal s cD ch H (fun τ => (eTau τ : R.GG)) (hcw w) bT) ∧ (∀ w w' τ, (hcw w τ).v = (hcw w' τ).v ∧ (hcw w τ).b = (hcw w' τ).b ∧ (hcw w τ).e = (hcw w' τ).e ∧ ∀ h : 0 < R.k, (hcw w τ).u ⟨0, h⟩ = (hcw w' τ).u ⟨0, h⟩ ∧ (hcw w τ).u ⟨R.k - 1, by omega⟩ = (hcw w' τ).u ⟨R.k - 1, by omega⟩) ∧ (∀ w τ (l : ℕ) (h : l < R.k - 2), (hcw w τ).u ⟨l + 1, by omega⟩ = (hcw w τ).v ⟨l, by omega⟩ - 1 / 2 - (if w ⟨l, h⟩ then (Delv s cD : ℚ) else 0)) ∧ ∀ w τ (t : H.TT) (h : 0 < R.k), (eTau τ : R.GG) = R.tau1 t → (hcw w τ).u ⟨0, h⟩ = (aT t : ℚ) + ((R.k : ℚ) - 1) / 2 ∧ (hcw w τ).u ⟨R.k - 1, by omega⟩ = -(bT t : ℚ) - ((R.k : ℚ) - 1) / 2 := by
  intro eps cD ch C8 he0 he1 hcD hch
  obtain ⟨x0, Hs⟩ := hc_sizes eps cD ch he0 he1 hcD hch
  refine ⟨x0, fun s R H aT bT he hx hR hH hab Tau _ eTau => ?_⟩
  classical
  obtain ⟨hD, hh, hka, hkb, hb', hb, hw⟩ := Hs s R he hx hR
  have hk5 : 5 ≤ R.k := by have := R.two_le_m; have := R.m_add_three_le_k; omega
  obtain ⟨κ, hκ⟩ := R.k_even
  have hκq : (R.k : ℚ) = 2 * κ := by rw [hκ]; push_cast; ring
  obtain ⟨-, hthP, hdisj, -, hcard⟩ := factTopsThick R H
  have hinj : ∀ t t' : H.TT, R.tau1 t = R.tau1 t' → t = t' := fun t t' h =>
    Subtype.ext (R.iota_bijective.1 (congrArg Prod.snd h))
  have htop : ∀ g, g ∈ H.topPlaces ↔ ∃ t : H.TT, g = R.tau1 t := fun g => by
    unfold Host.topPlaces
    rw [Finset.mem_image]
    exact ⟨fun ⟨t, ht, e⟩ => ⟨⟨t, ht⟩, e.symm⟩, fun ⟨t, e⟩ => ⟨t.1, t.2, e.symm⟩⟩
  have hne : H.thickPlaces.Nonempty := by
    rw [← Finset.card_pos, hcard]
    have h1 := hH.2.2.1
    have hxp : 0 < s.x := by linarith [s.one_lt_alt]
    have hn : (0 : ℝ) < R.n := by
      have hnNat : 0 < R.n := by
        unfold Ranks.n
        have := R.two_le_m
        have := R.m_le_f
        omega
      exact_mod_cast hnNat
    have : (0 : ℝ) < H.T2.card := lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hxp _) hn) h1
    exact_mod_cast this
  obtain ⟨g0, hg0⟩ := hne
  let τ0 : Tau := eTau.symm ⟨g0, hthP g0 hg0⟩
  have hτ0 : (eTau τ0 : R.GG) = g0 := by simp [τ0]
  let base : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then bT h.choose + ⌊s.b' / s.x⌋
    else if (eTau τ : R.GG) ∈ H.thickPlaces then ⌈s.b⌉ else ⌈s.w'' R.n⌉
  obtain ⟨sh, hsh, hMU⟩ := UpperTheory.Mu.exists_shift H eTau base τ0
  let ε : ℤ := (sh : ℤ)
  have hε : 0 ≤ ε ∧ ε < (NumberField.Units.torsionOrder H.E : ℤ) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.2 hsh⟩
  let b1 : Tau → ℤ := fun τ => base τ + if τ = τ0 then ε else 0
  let U0 : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then aT h.choose + κ - 1
    else ((R.k - 2 : ℕ) : ℤ) * (4 * Delv s cD) + R.k * (4 * Delv s cD)
  let UL : Tau → ℤ := fun τ =>
    if h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t then -bT h.choose - κ else -1
  have hT : ∀ τ (t : H.TT), (eTau τ : R.GG) = R.tau1 t →
      b1 τ = bT t + ⌊s.b' / s.x⌋ ∧ U0 τ = aT t + κ - 1 ∧ UL τ = -bT t - κ := fun τ t ht => by
    have h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := ⟨t, ht⟩
    have hc : h.choose = t := hinj _ _ (h.choose_spec.symm.trans ht)
    have hτ : τ ≠ τ0 := by
      rintro rfl
      exact Finset.disjoint_left.1 hdisj ((htop _).2 h) (hτ0 ▸ hg0)
    simp only [b1, base, U0, UL, dif_pos h, hc, if_neg hτ, add_zero, and_self]
  have hN : ∀ τ, (¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t) →
      1 ≤ b1 τ ∧ U0 τ = ((R.k - 2 : ℕ) : ℤ) * (4 * Delv s cD) + R.k * (4 * Delv s cD) ∧ UL τ = -1 := fun τ h => by
    have c1 : 0 < ⌈s.b⌉ := Int.ceil_pos.2 hb
    have c2 : 0 < ⌈s.w'' R.n⌉ := Int.ceil_pos.2 hw
    simp only [b1, base, U0, UL, dif_neg h, and_self, and_true]
    split_ifs <;> omega
  have hcond : ∀ τ, ((R.k - 2 : ℕ) : ℚ) * (4 * (Delv s cD : ℚ)) ≤ U0 τ ∧ UL τ < 0 ∧ -b1 τ ≤ UL τ := fun τ => by
    by_cases h : ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t
    · obtain ⟨t, ht⟩ := h
      obtain ⟨e1, e2, e3⟩ := hT τ t ht
      have a1 : (R.k : ℤ) * (4 * (Delv s cD : ℤ)) ≤ aT t := by
        have := hka.trans (hab t).1
        exact_mod_cast this
      have a2 : 0 < bT t := by
        have := hb'.trans_le (hab t).2
        exact_mod_cast this
      have a3 : (R.k : ℤ) ≤ ⌊s.b' / s.x⌋ := Int.le_floor.2 (by exact_mod_cast hkb)
      rw [e1, e2, e3]
      refine ⟨?_, by omega, by omega⟩
      have a4 : ((R.k - 2 : ℕ) : ℤ) * (4 * (Delv s cD : ℤ)) ≤ (R.k : ℤ) * (4 * (Delv s cD : ℤ)) := by
        gcongr; omega
      have : ((R.k - 2 : ℕ) : ℤ) * (4 * (Delv s cD : ℤ)) ≤ aT t + κ - 1 := by omega
      exact_mod_cast this
    · obtain ⟨e1, e2, e3⟩ := hN τ h
      rw [e2, e3]
      refine ⟨?_, by omega, by omega⟩
      push_cast
      have : (0 : ℚ) ≤ (R.k : ℚ) * (4 * (Delv s cD : ℚ)) := by positivity
      linarith
  choose p hv hu hm hbe using fun (w : Fin (R.k - 2) → Bool) (τ : Tau) =>
    exists_hcParam_of_code R (Delv s cD) ⌈s.x ^ ch⌉₊ hD hh (U0 τ) (UL τ) (b1 τ)
      (hcond τ).1 (hcond τ).2.1 (hcond τ).2.2 w
  have hh0 : (h0v s ch : ℚ) = 2 * (⌈s.x ^ ch⌉₊ : ℕ) := by unfold h0v; push_cast; ring
  refine ⟨p, fun w => ⟨fun τ i => hv w τ i, fun τ hk hτ => ?_, ⟨b1, fun τ j => ?_, fun τ t ht => (hT τ t ht).1,
    fun τ hτ => ?_, fun τ hτ => ?_⟩, fun j => ?_⟩, fun w w' τ => ⟨?_, ?_, ?_, fun h => ?_⟩, fun w τ l h => ?_,
    fun w τ t h ht => ?_⟩
  · obtain ⟨-, e2, e3⟩ := hN τ (fun h => hτ ((htop _).2 h))
    rw [(hu w τ hk).1, (hu w τ hk).2, e2, e3]
    constructor
    · push_cast; ring
    · norm_num
  · rw [(hbe w τ j).2, (hbe w τ j).1, hh0]
    constructor <;> ring
  · have h : ¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := fun h =>
      Finset.disjoint_left.1 hdisj ((htop _).2 h) hτ
    have hτ' : (eTau τ : R.GG) ∈ H.thickPlaces := hτ
    simp only [b1, base, dif_neg h, if_pos hτ']
    split_ifs <;> omega
  · have h : ¬ ∃ t : H.TT, (eTau τ : R.GG) = R.tau1 t := fun h => hτ.2.1 ((htop _).2 h)
    have hτ' : (eTau τ : R.GG) ∉ H.thickPlaces := hτ.2.2
    have hτ1 : τ ≠ τ0 := by
      rintro rfl
      exact hτ' (hτ0 ▸ hg0)
    simp only [b1, base, dif_neg h, if_neg hτ', if_neg hτ1, add_zero]
  · refine UpperTheory.Mu.muq_of_parallel H eTau hMU (j.1 * (2 * (⌈s.x ^ ch⌉₊ : ℕ)) + (⌈s.x ^ ch⌉₊ : ℕ)) (fun τ => ?_)
    rw [(hbe w τ j).2, (hbe w τ j).1]
    change _ = ((b1 τ : ℤ) : ℚ) + _
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
    ring
  · funext i; rw [hv, hv]
  · funext j; rw [(hbe w τ j).1, (hbe w' τ j).1]
  · funext j; rw [(hbe w τ j).2, (hbe w' τ j).2, (hbe w τ j).1, (hbe w' τ j).1]
  · rw [(hu w τ h).1, (hu w τ h).2, (hu w' τ h).1, (hu w' τ h).2]; exact ⟨rfl, rfl⟩
  · rw [hm w τ l h, hv]
  · obtain ⟨-, e2, e3⟩ := hT τ t ht
    rw [(hu w τ h).1, (hu w τ h).2, e2, e3, hκq]
    constructor <;> (push_cast; ring)

end GlobalTheory.EX
end
