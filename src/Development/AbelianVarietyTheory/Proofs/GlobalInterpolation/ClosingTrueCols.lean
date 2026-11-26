module

public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevelPrimePointModelRealisation
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCoordinatesValueLatticesEqWeylLattices
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FivePointLawsTrueChains

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SharpBoundStabilityLatticeColumnChain
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntPOfKerP
noncomputable section

namespace GlobalTheory.LvT.Built.IntPPass

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem ev_smul {D : D7} {u : D.what₂.Word} (B : Built.Dat D u) (i : ℕ) (c : D.what₂.LL) (F : B.V i) :
    B.ev i (c • F) = D.what₂.embLL c • B.ev i F := by
  unfold Built.Dat.ev
  exact map_smulₛₗ _ _ _

theorem intP_of_kerP : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (Co : M.Coord) (Co' : M'.Coord) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Co.Ok → Co'.Ok → R.ValIs Co → R'.ValIs Co' → Built.Dat.KerP k → K.IntP Co Co' := by
  intro D u B i sp sp' M M' R R' k Co Co' K hT hK hCo hCo' hV hV' hP w hw hs p p' y hy
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  set g := R.zeta ζ with hg
  set g' := R'.zeta ζ' with hg'
  have h0 := (GlobalTheory.LvT.ValEq.valB_laws D u B.ch i M Co hCo w hw ∅ (g • R.pt b d)).2.2.2 g⁻¹ y hy
  rw [inv_smul_smul] at h0
  set y₀ := M.act g⁻¹ y with hy₀
  have hyy : y = M.act g y₀ := by
    rw [hy₀, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨F, hF, hFy⟩ := (hV.dual w hw b d y₀).1 h0
  have h1 := hP w hw hs b b' d d' F hF
  have h2 := hK b b' d d' F y₀ hFy
  rw [hT, hyy, K.src, ← map_smul]
  refine (GlobalTheory.LvT.ValEq.valB_laws D u B.ch (i + 1) M' Co' hCo' w hw Finset.univ (R'.pt b' d')).2.2.2 g' _ ?_
  refine (hV'.ker w hw hs b' d' _).2 ⟨_, h1, ?_⟩
  rw [ev_smul, ← h2, map_zpow₀, map_natCast]
  rfl

end GlobalTheory.LvT.Built.IntPPass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeLawPointKernelOfCoefficientKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeLawPointKernelOfCoefficientKernel
noncomputable section

namespace GlobalTheory.LvT.Built.UK

open NumberField IsDedekindDomain Matrix
open Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Pts
open Formalism.HermitianLatticesTheory (localization₂)

section Corr

variable {q : ℕ} {F : Type} [Field F] {Lc Lc' : LocF q F} {n : ℕ} (e : Lc'.K ≃+* Lc.K)

def Corr (p : LocF.PP Lc n) (r : LocF.PP Lc' n) : Prop :=
  ∀ x : Fin n → Lc'.K, ((fun a => e (x a)) ∈ p.1.L ↔ x ∈ r.1.L) ∧ p.1.f (fun a => e (x a)) = r.1.f x

variable {e}

theorem vec_surj (e : Lc'.K ≃+* Lc.K) (y : Fin n → Lc.K) : ∃ x : Fin n → Lc'.K, y = fun a => e (x a) :=
  ⟨fun a => e.symm (y a), funext fun a => (e.apply_symm_apply _).symm⟩

theorem Corr.eq_iff {p p' : LocF.PP Lc n} {r r' : LocF.PP Lc' n} (h : Corr e p r) (h' : Corr e p' r') : p = p' ↔ r = r' := by
  constructor
  · rintro rfl
    exact pp_ext (fun x => (h x).1.symm.trans (h' x).1) fun x _ => (h x).2.symm.trans (h' x).2
  · rintro rfl
    refine pp_ext (fun y => ?_) fun y _ => ?_
    · obtain ⟨x, rfl⟩ := vec_surj e y
      exact (h x).1.trans (h' x).1.symm
    · obtain ⟨x, rfl⟩ := vec_surj e y
      exact (h x).2.trans (h' x).2.symm

theorem Corr.inc_iff {p p' : LocF.PP Lc n} {r r' : LocF.PP Lc' n} (h : Corr e p r) (h' : Corr e p' r') :
    p.Inc p' ↔ r.Inc r' := by
  have hk : ∀ x : Fin n → Lc'.K, (fun a => e (x a)) ∈ p'.ker ↔ x ∈ r'.ker := fun x =>
    and_congr (h' x).1 (by rw [(h' x).2])
  have hs : ∀ x : Fin n → Lc'.K, ((q : Lc.K)⁻¹ • fun a => e (x a)) = fun a => e (((q : Lc'.K)⁻¹ • x) a) := fun x => by
    funext a
    simp
  have key : ∀ x : Fin n → Lc'.K, (p.1.f (fun a => e (x a)) = 1 ∧ p.IsUp (fun a => e (x a)) p') ↔ (r.1.f x = 1 ∧ r.IsUp x r') := by
    intro x
    unfold LocF.PP.IsUp
    rw [(h x).2, (h x).1, hs, (h' _).2]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ Iff.rfl))
    constructor
    · intro hh
      ext z
      rw [← hk, hh]
      exact (h z).1
    · intro hh
      ext y
      obtain ⟨z, rfl⟩ := vec_surj e y
      rw [hk, hh]
      exact (h z).1.symm
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := vec_surj e y
    exact ⟨x, (key x).1 hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, (key x).2 hx⟩

end Corr

section Step

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem tAt (sp : Split A T) : TAt T ST :=
  ⟨fun P => ⟨sp.T_mem P.1 P.2, sp.T_nsq P.1 P.2⟩, fun P Q => sp.nonconj P.1 P.2 Q.1 Q.2⟩

theorem eq_of_pair (sp : Split A T) (ht : A.Tied T) {b : S.β} {d d' : S.D b} (ho : (sp.off b).r d d')
    (hp : ∀ P, pair ((tAt sp).unif P) _ (ht.ok b d) = pair ((tAt sp).unif P) _ (ht.ok b d')) : d = d' :=
  sp.ext b d d' ho (deco_ext (tAt sp) (ht.ok b d) (ht.ok b d')
    (fun w hw => sp.off_lat b d d' ho w fun P hP => hw ⟨P, hP⟩) hp)

theorem pair_eq_of_deco {P : ST} (h : Unif T P.1) {d d' : Deco E n ST ∅} (hd : d.Ok) (e : d = d') :
    pair h d hd = pair h d' (e ▸ hd) := by subst e; rfl

theorem above_off (sp : Split A T) {b : S.β} {P : ST} {d d₁ : S.D b} (h : Above A b P d d₁) : (sp.off b).r d d₁ := by
  obtain ⟨x, hx, hf, rfl⟩ := h
  exact sp.off_up b d P x hx hf

theorem above_iff (sp : Split A T) (ht : A.Tied T) {b : S.β} (P : ST) {d d₁ : S.D b} (ho : (sp.off b).r d d₁) :
    Above A b P d d₁ ↔
      (∀ Q, Q ≠ P → pair ((tAt sp).unif Q) _ (ht.ok b d₁) = pair ((tAt sp).unif Q) _ (ht.ok b d)) ∧
      (pair ((tAt sp).unif P) _ (ht.ok b d)).Inc (pair ((tAt sp).unif P) _ (ht.ok b d₁)) := by
  have h := tAt sp
  have hd := ht.ok b d
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    have e := ht.up_deco b d P x hx hf
    refine ⟨fun Q hQ => ?_, ?_⟩
    · rw [pair_eq_of_deco _ _ e]
      exact pair_up_ne h hd hQ hx _
    · rw [pair_eq_of_deco _ (ht.ok b (A.up b d P x)) e]
      refine ⟨x, hf, le_locP _ _ hx, ?_, ?_⟩
      · ext y
        rw [mem_pair_ker _ (h.ne P), hd.dnN_up P (h.move P) (h.unif P).mem (h.unif P).nsq hx hf]
        rfl
      · have := hd.up_f_inv P (h.move P) (h.unif P).mem (h.unif P).nsq hx hf
        rw [map_natCast] at this
        exact this
  · rintro ⟨h1, x, hf, hp⟩
    have hx : x ∈ localization₂ P.1.asIdeal (A.N b d) := hp.1
    obtain ⟨x', hx', hr⟩ := redL_surj (redL (A.N b d) P.1 x)
    have hx'' : x' ∈ localization₂ P.1.asIdeal (A.N b d) := le_locP _ _ hx'
    have hf' : A.f b d P x' = 1 := by
      have hneg : (-1 : GlobalTheory.LvT.Inh.valO P.1) • x ∈ localization₂ P.1.asIdeal (A.N b d) := (locO P.1 _).smul_mem _ hx
      have h0 : redL (A.N b d) P.1 (x' + (-1 : GlobalTheory.LvT.Inh.valO P.1) • x) = 0 := by
        rw [redL_add hx'' hneg, redL_smul _ hx, hr, map_neg, map_one, neg_one_smul, add_neg_cancel]
      have h2 := inv_smul_mem_of_redL (h.unif P) ((localization₂ _ _).add_mem hx'' hneg) h0
      have h3 := hd.f_smul P (T : 𝓞 E) _ h2
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (h.unif P).mem, zero_mul, ← algebraMap_smul E (T : 𝓞 E), map_natCast,
        smul_inv_smul₀ (h.unif P).ne_zero] at h3
      have e : x' = (x' + (-1 : GlobalTheory.LvT.Inh.valO P.1) • x) + x := by rw [neg_one_smul]; abel
      have h4 := hd.f_add P _ ((localization₂ _ _).add_mem hx'' hneg) _ hx
      rw [← e, h3, zero_add] at h4
      exact h4.trans hf
    refine ⟨x', hx', hf', ?_⟩
    have e := ht.up_deco b d P x' hx' hf'
    refine eq_of_pair sp ht ((sp.off b).trans ((sp.off b).symm ho) (sp.off_up b d P x' hx' hf')) fun Q => ?_
    rw [pair_eq_of_deco _ (ht.ok b (A.up b d P x')) e]
    by_cases hQ : Q = P
    · subst hQ
      exact (pair_up h hd Q hx' hf' hr hp _).symm
    · rw [h1 Q hQ]
      exact (pair_up_ne h hd hQ hx' _).symm

end Step

section Real

variable {D : D7} {u : D.what₂.Word} {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}
  (R : B.Real i sp M)

theorem corr_pt (b : (B.I.S i).β) (d : (B.I.S i).D b) (P : B.ch.A.vT) :
    Corr (Lc := M.Lc P) (Lc' := locF ((tAt sp).unif (B.pr P))) (R.iK P) ((R.pt b d).2 P)
      (pair ((tAt sp).unif (B.pr P)) _ ((B.hJ.tied i).ok b d)) :=
  fun x => ⟨R.pt_L b d P x, R.pt_f b d P x⟩

theorem fst_of_off {b : (B.I.S i).β} {d d' : (B.I.S i).D b} (h : (sp.off b).r d d') : (R.pt b d).1 = (R.pt b d').1 := by
  have := (R.fst 1 b d d').2 ⟨1, map_one _, map_one _, by rwa [one_smul]⟩
  rwa [map_one, one_smul] at this

theorem exists_pt {b : (B.I.S i).β} (d : (B.I.S i).D b) {p : M.Pt} (h : p.1 = (R.pt b d).1) :
    ∃ d', (sp.off b).r d' d ∧ p = R.pt b d' := by
  obtain ⟨ζ, b₁, d₁, rfl⟩ := R.surj p
  obtain rfl := R.idx ζ b₁ b d₁ d h
  obtain ⟨g, h1, h2, h3⟩ := (R.fst ζ b₁ d₁ d).1 h
  exact ⟨_, h3, (R.inj ζ b₁ d₁ _).2 ⟨g, h1, h2, rfl⟩⟩

theorem pt_inj {b : (B.I.S i).β} {d d' : (B.I.S i).D b} (ho : (sp.off b).r d d') (h : R.pt b d = R.pt b d') : d = d' :=
  eq_of_pair sp (B.hJ.tied i) ho fun (P : B.ch.A.vT) =>
    ((corr_pt R b d P).eq_iff (corr_pt R b d' P)).1 (by rw [h])

theorem inc_iff {b : (B.I.S i).β} (v : B.ch.A.vT) {d d' : (B.I.S i).D b} (ho : (sp.off b).r d d') :
    M.Inc v (R.pt b d) (R.pt b d') ↔ Above (B.J.A i) b (B.pr v) d d' := by
  rw [above_iff sp (B.hJ.tied i) (B.pr v) ho]
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨fun (Q : B.ch.A.vT) hQ => ((corr_pt R b d' Q).eq_iff (corr_pt R b d Q)).1 (h2 Q hQ),
      ((corr_pt R b d v).inc_iff (corr_pt R b d' v)).1 h3⟩
  · rintro ⟨h2, h3⟩
    exact ⟨(fst_of_off R ho).symm, fun Q hQ => ((corr_pt R b d' Q).eq_iff (corr_pt R b d Q)).2 (h2 Q hQ),
      ((corr_pt R b d v).inc_iff (corr_pt R b d' v)).2 h3⟩

theorem above_image (g : M.G) {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    {p₁ | M.Inc v (g • R.pt b d) p₁} = (fun d₁ => g • R.pt b d₁) '' {d₁ | Above (B.J.A i) b (B.pr v) d d₁} := by
  have hs := (inc_finite_stable D u _ i M v).2.1
  ext p₁
  constructor
  · intro h
    have h' := (hs g⁻¹ _ _).1 h
    rw [inv_smul_smul] at h'
    obtain ⟨d', ho, e⟩ := exists_pt R d h'.1
    rw [e] at h'
    exact ⟨d', (inc_iff R v ((sp.off b).symm ho)).1 h', by beta_reduce; rw [← e, smul_inv_smul]⟩
  · rintro ⟨d', h, rfl⟩
    exact (hs g _ _).1 ((inc_iff R v (above_off sp h)).2 h)

theorem below_image (g : M.G) {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    {p₀ | M.Inc v p₀ (g • R.pt b d)} = (fun d₀ => g • R.pt b d₀) '' {d₀ | Above (B.J.A i) b (B.pr v) d₀ d} := by
  have hs := (inc_finite_stable D u _ i M v).2.1
  ext p₀
  constructor
  · intro h
    have h' := (hs g⁻¹ _ _).1 h
    rw [inv_smul_smul] at h'
    obtain ⟨d', ho, e⟩ := exists_pt R d h'.1.symm
    rw [e] at h'
    exact ⟨d', (inc_iff R v ho).1 h', by beta_reduce; rw [← e, smul_inv_smul]⟩
  · rintro ⟨d', h, rfl⟩
    exact (hs g _ _).1 ((inc_iff R v (above_off sp h)).2 h)

theorem above_injOn (g : M.G) {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    Set.InjOn (fun d₁ => g • R.pt b d₁) {d₁ | Above (B.J.A i) b (B.pr v) d d₁} := fun _ h _ h' e =>
  pt_inj R ((sp.off b).trans ((sp.off b).symm (above_off sp h)) (above_off sp h')) (MulAction.injective g e)

theorem below_injOn (g : M.G) {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    Set.InjOn (fun d₀ => g • R.pt b d₀) {d₀ | Above (B.J.A i) b (B.pr v) d₀ d} := fun _ h _ h' e =>
  pt_inj R ((sp.off b).trans (above_off sp h) ((sp.off b).symm (above_off sp h'))) (MulAction.injective g e)

include R in
theorem above_finite {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    {d₁ | Above (B.J.A i) b (B.pr v) d d₁}.Finite :=
  Set.Finite.of_finite_image (above_image R 1 v d ▸ ((inc_finite_stable D u _ i M v).1 _).1) (above_injOn R 1 v d)

include R in
theorem below_finite {b : (B.I.S i).β} (v : B.ch.A.vT) (d : (B.I.S i).D b) :
    {d₀ | Above (B.J.A i) b (B.pr v) d₀ d}.Finite :=
  Set.Finite.of_finite_image (below_image R 1 v d ▸ ((inc_finite_stable D u _ i M v).1 _).2) (below_injOn R 1 v d)

include R in
theorem val_ext {W : Type} [AddCommGroup W] [Module ℂ W] (f g : M.Val →ₗ[ℂ] W)
    (h : ∀ (F : B.V i) (y : M.Val), y.1 = B.ev i F → f y = g y) : f = g := by
  have hv : M.Val = Submodule.span ℂ (Set.range (B.ev i)) :=
    R.val_eq.trans (span_evV B.emb 1 (B.lam i) D.what₂.embLL).symm
  ext ⟨y, hy⟩
  have key : ∀ y ∈ Submodule.span ℂ (Set.range (B.ev i)), ∀ hy : y ∈ M.Val, f ⟨y, hy⟩ = g ⟨y, hy⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨F, rfl⟩ := hx
      exact fun hy => h F _ rfl
    | zero => exact fun hy => (map_zero f).trans (map_zero g).symm
    | add x y hx hy ihx ihy =>
      intro hxy
      have hx' : x ∈ M.Val := hv ▸ hx
      have hy' : y ∈ M.Val := hv ▸ hy
      exact (map_add f ⟨x, hx'⟩ ⟨y, hy'⟩).trans ((congrArg₂ (· + ·) (ihx hx') (ihy hy')).trans (map_add g _ _).symm)
    | smul c x hx ih =>
      intro hc
      have hx' : x ∈ M.Val := hv ▸ hx
      exact (map_smul f c ⟨x, hx'⟩).trans ((congrArg (c • ·) (ih hx')).trans (map_smul g c _).symm)
  exact key y (hv ▸ hy) hy

end Real

theorem ukLaw_of_kerUK (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T)
    (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M)
    (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M') (ht : K.TgtEq) (hk : Built.Dat.KerIs R R' K k)
    (hu : Built.Dat.KerUK k) : K.UKLaw := by
  intro v p p' y
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  generalize R.zeta ζ = g
  generalize R'.zeta ζ' = g'
  obtain ⟨y, rfl⟩ : ∃ y₀, y = M.act g y₀ :=
    ⟨M.act g⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]⟩
  have f1 := above_finite R' v d'
  have f0 := below_finite R v d
  rw [above_image R' g' v d', below_image R g v d, finsum_mem_image (above_injOn R' g' v d'),
    finsum_mem_image (below_injOn R g v d), finsum_mem_eq_finite_toFinset_sum _ f1, finsum_mem_eq_finite_toFinset_sum _ f0]
  simp only [K.src, ht g']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_sum, ← map_smul]
  congr 1
  have := val_ext R (∑ d₁ ∈ f1.toFinset, K.k (R.pt b d) (R'.pt b' d₁))
    (((B.ch.A.T : ℂ) ^ ((D.R.t + 1) / 2)) • ∑ d₀ ∈ f0.toFinset, K.k (R.pt b d₀) (R'.pt b' d')) (fun F y hy => ?_)
  · simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using LinearMap.congr_fun this y
  have h := hu b b' d d' (B.pr v) F
  rw [finsum_mem_eq_finite_toFinset_sum _ f1, finsum_mem_eq_finite_toFinset_sum _ f0] at h
  have h2 := congrArg (evV B.emb (1 : Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) B.E) (B.lam (i + 1)) D.what₂.embLL) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.map_smulₛₗ, map_sum, map_sum, map_pow, map_natCast] at h2
  apply Subtype.ext
  rw [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply, Submodule.coe_smul, Submodule.coe_sum, Submodule.coe_sum,
    Finset.sum_congr rfl fun d₁ _ => hk b b' d d₁ F y hy, Finset.sum_congr rfl fun d₀ _ => hk b b' d₀ d' F y hy]
  exact h2

end GlobalTheory.LvT.Built.UK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeLawPointKernelOfCoefficientKernelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeLaw_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerUK k → K.UKLaw := by
  first | exact @GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK | exact GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK | (intros; apply GlobalTheory.LvT.Built.UK.ukLaw_of_kerUK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPointKernelRealisedModels
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPointKernelRealisedModels
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.KerExt

theorem exists_ext {G P T β X : Type} [Group G] [MulAction G P] [Group T] {H D : β → Type} [∀ b, Group (H b)]
    [∀ b, MulAction (H b) (D b)] (ρ : G → X → X) (ρ1 : ∀ x, ρ 1 x = x) (ρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x))
    (pt : ∀ b, D b → P) (hom : ∀ b, H b →* G) (zeta : T →* G)
    (pt_smul : ∀ b g d, pt b (g • d) = hom b g • pt b d)
    (gen : ∀ b (g : G), ∃ ζ g', g = zeta ζ * hom b g')
    (comm : ∀ ζ (g : G), zeta ζ * g = g * zeta ζ)
    (surj : ∀ p : P, ∃ ζ b d, p = zeta ζ • pt b d)
    (idx : ∀ ζ b b' d d', zeta ζ • pt b d = pt b' d' → b = b')
    (inj : ∀ ζ b d d', zeta ζ • pt b d = pt b d' → ∃ g : H b, g • d = d' ∧ ∀ x, ρ (hom b g) x = ρ (zeta ζ) x)
    (φ : ∀ b, D b → X) (hφ : ∀ b g d, φ b (g • d) = ρ (hom b g) (φ b d)) :
    ∃ Φ : P → X, (∀ b d, Φ (pt b d) = φ b d) ∧ ∀ g p, Φ (g • p) = ρ g (Φ p) := by
  have key : ∀ g ζ b d ζ' b' d', g • zeta ζ • pt b d = zeta ζ' • pt b' d' →
      ρ (zeta ζ') (φ b' d') = ρ g (ρ (zeta ζ) (φ b d)) := by
    intro g ζ b d ζ' b' d' h
    obtain ⟨ζ₀, g₀, rfl⟩ := gen b g
    have e : zeta (ζ'⁻¹ * ζ₀ * ζ) * hom b g₀ = (zeta ζ')⁻¹ * (zeta ζ₀ * hom b g₀ * zeta ζ) := by
      rw [map_mul, map_mul, map_inv, mul_assoc, comm ζ]
      simp only [mul_assoc]
    have h1 : zeta (ζ'⁻¹ * ζ₀ * ζ) • pt b (g₀ • d) = pt b' d' := by
      rw [pt_smul, ← mul_smul, e, mul_smul, mul_smul, h, inv_smul_smul]
    obtain rfl := idx _ _ _ _ _ h1
    obtain ⟨g₁, rfl, hg⟩ := inj _ _ _ _ h1
    rw [hφ, hg, hφ, ← ρm, ← ρm, ← ρm, mul_assoc, e, mul_inv_cancel_left]
  choose z i d hp using surj
  refine ⟨fun p => ρ (zeta (z p)) (φ (i p) (d p)), fun b x => ?_, fun g p => ?_⟩
  · have := key 1 1 b x (z (pt b x)) (i (pt b x)) (d (pt b x)) (by rw [← hp, map_one, one_smul, one_smul])
    exact this.trans (by rw [map_one, ρ1, ρ1])
  · exact key g (z p) (i p) (d p) _ _ _ (by rw [← hp, ← hp])

theorem exists_cplx {K V V' W W' : Type} [Field K] (σ : K →+* ℂ) [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (e : V →ₛₗ[σ] W) (e' : V' →ₛₗ[σ] W')
    (li : LinearIndependent ℂ fun j => e (Module.Basis.ofVectorSpace K V j))
    (sp : Submodule.span ℂ (Set.range e) = ⊤) (f : V →ₗ[K] V') :
    ∃ fC : W →ₗ[ℂ] W', ∀ F, fC (e F) = e' (f F) := by
  set b := Module.Basis.ofVectorSpace K V
  have hmem : ∀ F, e F ∈ Submodule.span ℂ (Set.range fun j => e (b j)) := by
    intro F
    have hF : F ∈ Submodule.span K (Set.range b) := by rw [b.span_eq]; trivial
    induction hF using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact Submodule.subset_span ⟨j, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  have sp' : ⊤ ≤ Submodule.span ℂ (Set.range fun j => e (b j)) := by
    rw [← sp, Submodule.span_le]
    rintro _ ⟨F, rfl⟩
    exact hmem F
  let c := Module.Basis.mk li sp'
  refine ⟨c.constr ℂ fun j => e' (f (b j)), fun F => ?_⟩
  have h : (c.constr ℂ fun j => e' (f (b j))).comp e = e'.comp f := by
    refine b.ext fun j => ?_
    have : e (b j) = c j := by simp [c]
    simp only [LinearMap.comp_apply, this, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h F

section Real

variable {D : D7} {u : D.what₂.Word} {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}
  (R : B.Real i sp M)

def evM : B.V i →ₛₗ[D.what₂.embLL] M.Val :=
  LinearMap.codRestrict M.Val (evV B.emb (1 : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) B.E) (B.lam i) D.what₂.embLL)
    fun F => by rw [R.val_eq]; exact evV_mem_ValC _ _ _ _ F

theorem evM_li : LinearIndependent ℂ fun j => evM R (Module.Basis.ofVectorSpace D.what₂.LL (B.V i) j) :=
  LinearIndependent.of_comp M.Val.subtype
    (evV_linearIndependent B.emb 1 (B.lam i) D.what₂.embLL (fr0 B.emb D.what₂.embLL _) _
      (Module.Basis.ofVectorSpace D.what₂.LL (B.V i)).linearIndependent)

theorem evM_span : Submodule.span ℂ (Set.range (evM R)) = ⊤ := by
  apply Submodule.map_injective_of_injective M.Val.subtype_injective
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
  exact (span_evV B.emb 1 (B.lam i) D.what₂.embLL).trans R.val_eq.symm

theorem evM_rho (b) (g : (B.I.S i).G b) (F : B.V i) :
    evM R ((B.I.S i).rho B.emb (B.lam i) b g F) = M.act (R.hom b g) (evM R F) := by
  apply Subtype.ext
  rw [R.act_hom]
  exact GStep.evV_rho_eq_tr _ _ _ _ b g F

theorem inj_act (ζ b d d') (h : R.zeta ζ • R.pt b d = R.pt b d') :
    ∃ g : (B.I.S i).G b, g • d = d' ∧ M.act (R.hom b g) = M.act (R.zeta ζ) := by
  obtain ⟨g, h1, h2, h3⟩ := (R.inj ζ b d d').1 h
  refine ⟨g, h3, LinearMap.ext fun y => Subtype.ext ?_⟩
  rw [R.act_hom, R.act_zeta]
  funext x
  refine (trFr_apply B.emb D.what₂.embLL ((B.I.S i).gam b g) ((B.I.S i).chr b g) y.1 x).trans ?_
  rw [h1, h2, inv_one, GlobalTheory.Mem.Col2.frMul_one]
  rfl

theorem inj_act_inv (ζ b) (g : (B.I.S i).G b) (h : M.act (R.hom b g) = M.act (R.zeta ζ)) :
    M.act (R.hom b g)⁻¹ = M.act (R.zeta ζ)⁻¹ := by
  calc M.act (R.hom b g)⁻¹ = M.act (R.hom b g)⁻¹ * (M.act (R.zeta ζ) * M.act (R.zeta ζ)⁻¹) := by
        rw [← map_mul, mul_inv_cancel, map_one, mul_one]
    _ = _ := by rw [← h, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

theorem ext_evM {W : Type} [AddCommGroup W] [Module ℂ W] {f g : M.Val →ₗ[ℂ] W} (h : ∀ F, f (evM R F) = g (evM R F)) :
    f = g :=
  LinearMap.ext_on_range (evM_span R) h

end Real

theorem exists_kerPt : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) , Built.Dat.KerEq k → ∃ K : KerPt M M', K.TgtEq ∧ Built.Dat.KerIs R R' K k := by
  intro D u B i sp sp' M M' R R' k hk
  choose kC hkC using fun b b' d d' =>
    exists_cplx D.what₂.embLL (evM R) (evM R') (evM_li R) (evM_span R) (k b b' d d')
  have hequiv : ∀ b b' (g : (B.I.S i).G b) (g' : (B.I.S (i + 1)).G b') d d',
      kC b b' (g • d) (g' • d') = M'.act (R'.hom b' g') ∘ₗ kC b b' d d' ∘ₗ M.act (R.hom b g)⁻¹ := by
    intro b b' g g' d d'
    refine ext_evM R fun F => ?_
    rw [hkC, hk.equiv, ← map_inv]
    simp only [LinearMap.comp_apply]
    rw [evM_rho, ← evM_rho R, hkC]

  have h1 : ∀ b d, ∃ Φ : M'.Pt → (M.Val →ₗ[ℂ] M'.Val), (∀ b' d', Φ (R'.pt b' d') = kC b b' d d') ∧
      ∀ (g : M'.G) p, Φ (g • p) = M'.act g ∘ₗ Φ p := by
    intro b d
    refine exists_ext (fun (g : M'.G) (x : M.Val →ₗ[ℂ] M'.Val) => M'.act g ∘ₗ x) ?_ ?_ R'.pt R'.hom R'.zeta R'.pt_smul
      R'.gen R'.comm R'.surj (fun ζ b b' d d' h => R'.idx ζ b b' d d' (congrArg Prod.fst h)) ?_
      (fun b' d' => kC b b' d d') ?_
    · intro x
      simp only [map_one]
      rfl
    · intro g h x
      simp only [map_mul]
      rfl
    · intro ζ b' d₁ d₂ h
      obtain ⟨g, h1, h2⟩ := inj_act R' ζ b' d₁ d₂ h
      exact ⟨g, h1, fun x => by simp only [h2]⟩
    · intro b' g d'
      have := hequiv b b' 1 g d d'
      rw [one_smul, map_one, inv_one, map_one] at this
      exact this
  choose Φ hΦ hΦe using h1

  obtain ⟨Ψ, hΨ, hΨe⟩ : ∃ Ψ : M.Pt → M'.Pt → (M.Val →ₗ[ℂ] M'.Val), (∀ b d, Ψ (R.pt b d) = Φ b d) ∧
      ∀ (g : M.G) p, Ψ (g • p) = fun p' => Ψ p p' ∘ₗ M.act g⁻¹ := by
    refine exists_ext (fun (g : M.G) (x : M'.Pt → (M.Val →ₗ[ℂ] M'.Val)) p' => x p' ∘ₗ M.act g⁻¹) ?_ ?_ R.pt R.hom R.zeta
      R.pt_smul R.gen R.comm R.surj (fun ζ b b' d d' h => R.idx ζ b b' d d' (congrArg Prod.fst h)) ?_ Φ ?_
    · intro x
      simp only [inv_one, map_one]
      rfl
    · intro g h x
      simp only [mul_inv_rev, map_mul]
      rfl
    · intro ζ b d₁ d₂ h
      obtain ⟨g, h1, h2⟩ := inj_act R ζ b d₁ d₂ h
      exact ⟨g, h1, fun x => by simp only [inj_act_inv R ζ b g h2]⟩
    · intro b g d
      funext p'
      obtain ⟨ζ, b', d', rfl⟩ := R'.surj p'
      have := hequiv b b' g 1 d d'
      rw [one_smul, map_one, map_one] at this
      simp only [hΦe, hΦ, this]
      rfl
  have hpt : ∀ b b' d d', Ψ (R.pt b d) (R'.pt b' d') = kC b b' d d' := fun b b' d d' => by rw [hΨ, hΦ]
  refine ⟨⟨Ψ, fun g p p' y => ?_, fun c c' y => ?_⟩, fun g' p p' y => ?_, fun b b' d d' F y hy => ?_⟩
  · rw [hΨe]
    show Ψ p p' ((M.act g⁻¹ * M.act g) y) = _
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl
  · rw [R.rep_eq, R'.rep_eq, hpt]
    have : B.ch.C.Kmap i c c' ∘ₗ M.Val.subtype =
        M'.Val.subtype ∘ₗ kC c.1 c'.1 ((B.I.S i).rep c) ((B.I.S (i + 1)).rep c') := by
      refine ext_evM R fun F => ?_
      simp only [LinearMap.comp_apply]
      rw [hkC]
      exact hk.kmap c c' F
    exact LinearMap.congr_fun this y
  · obtain ⟨ζ, b, d, rfl⟩ := R.surj p
    show Ψ _ _ y = M'.act g' (Ψ _ _ y)
    simp only [hΨe, hΨ, hΦe]
    rfl
  · obtain rfl : y = evM R F := Subtype.ext hy
    show (Ψ _ _ _).1 = _
    rw [hpt, hkC]
    rfl

end GlobalTheory.LvT.Built.KerExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPointKernelRealisedModelsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pointKernel_realised_models : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) , Built.Dat.KerEq k → ∃ K : KerPt M M', K.TgtEq ∧ Built.Dat.KerIs R R' K k := by
  first | exact @GlobalTheory.LvT.Built.KerExt.exists_kerPt | exact GlobalTheory.LvT.Built.KerExt.exists_kerPt | (intros; apply GlobalTheory.LvT.Built.KerExt.exists_kerPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DilateLawPointKernelOfCoefficientKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DilateLawPointKernelOfCoefficientKernel
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section
namespace GlobalTheory.LvT.Built.DilPass

variable {D : D7} {u : D.what₂.Word}

theorem isAct_unique {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {p p₁ p₂ : LocF.PP Lc n}
    (h₁ : p.IsAct g p₁) (h₂ : p.IsAct g p₂) : p₁ = p₂ := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  apply Subtype.ext
  apply LocF.Raw.ext
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1]
  · funext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2]

theorem isDil_act {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ} {g : GL (Fin n) Lc.K} {a : F}
    {p p' p₁ p₁' : LocF.PP Lc n} (h : LocF.PP.IsDil a p p') (h₁ : p.IsAct g p₁) (h₂ : p'.IsAct g p₁') :
    LocF.PP.IsDil a p₁ p₁' := by
  have hs : ∀ x : Fin n → Lc.K, ∃ y, Matrix.mulVec (g : Matrix (Fin n) (Fin n) Lc.K) y = x := fun x =>
    ⟨Matrix.mulVec ((g⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x, by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]⟩
  refine ⟨?_, fun x => ?_⟩
  · ext x
    obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).1, (h₂ y).1, h.1]
  · obtain ⟨y, rfl⟩ := hs x
    rw [(h₁ y).2, (h₂ y).2, h.2]

theorem dil_smul {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q : M.Pt} (h : M.Dil v a p q)
    (g : M.G) : M.Dil v a (g • p) (g • q) := by
  refine ⟨M.smul_fst g q p h.1, fun v' hv => ?_, isDil_act h.2.2 (M.smul_snd g p v) (M.smul_snd g q v)⟩
  have h1 := M.smul_snd g q v'
  rw [h.2.1 v' hv] at h1
  exact isAct_unique h1 (M.smul_snd g p v')

theorem dil_unique {X : Ch D u} {i : ℕ} (M : PtModel X i) {v : X.A.vT} {a : X.A.Fv v} {p q q' : M.Pt} (h : M.Dil v a p q)
    (h' : M.Dil v a p q') : q = q' := by
  refine Prod.ext (h.1.trans h'.1.symm) (funext fun v' => ?_)
  by_cases hv : v' = v
  · subst hv
    apply Subtype.ext
    apply LocF.Raw.ext
    · rw [h.2.2.1, h'.2.2.1]
    · funext x
      rw [h.2.2.2, h'.2.2.2]
  · rw [h.2.1 v' hv, h'.2.1 v' hv]

theorem dil_pt {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    (v : B.ch.A.vT) (a : (B.ch.A.Fv v)ˣ) (b : (B.I.S i).β) (d : (B.I.S i).D b) :
    M.Dil v a (R.pt b d) (R.pt b ((B.J.A i).dia b (B.pr v) a d)) := by
  have hs : ∀ (P : B.ch.A.vT) (x : Fin (D.R.N i) → (M.Lc P).K), ∃ y : Fin (D.R.N i) → B.E, (fun c => R.iK P (y c)) = x :=
    fun P x => ⟨fun c => (R.iK P).symm (x c), funext fun c => by simp⟩
  have hL : ∀ P, ((R.pt b ((B.J.A i).dia b (B.pr v) a d)).2 P).1.L = ((R.pt b d).2 P).1.L := by
    intro P
    ext x
    obtain ⟨y, rfl⟩ := hs P x
    rw [R.pt_L, R.pt_L, (B.hJ.lev i).dia_N b (B.pr v) a d]
  refine ⟨?_, fun v' hv => ?_, hL v, fun x => ?_⟩
  · have h := (R.fst 1 b ((B.J.A i).dia b (B.pr v) a d) d).2
      ⟨1, map_one _, map_one _, by rw [one_smul]; exact (sp.off b).symm (sp.off_dia b d (B.pr v) a)⟩
    rwa [map_one, one_smul] at h
  · apply Subtype.ext
    apply LocF.Raw.ext (hL v')
    funext x
    obtain ⟨y, rfl⟩ := hs v' x
    exact (R.pt_f _ _ v' y).trans ((congrFun (sp.dia_deco b d (B.pr v) (B.pr v') a hv) y).trans (R.pt_f _ _ v' y).symm)
  · obtain ⟨y, rfl⟩ := hs v x
    refine (R.pt_f _ _ v y).trans (((B.hJ.lev i).dia_f b (B.pr v) a d y).trans ?_)
    rw [← R.pt_f b d v y]
    rfl

theorem ext_ev {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i} (R : B.Real i sp M)
    {V : Type} [AddCommGroup V] [Module ℂ V] (φ ψ : M.Val →ₗ[ℂ] V)
    (h : ∀ F (y : M.Val), y.1 = B.ev i F → φ y = ψ y) : φ = ψ := by
  have hsp : M.Val = Submodule.span ℂ (Set.range (B.ev i)) := R.val_eq.trans (span_evV _ _ _ _).symm
  ext ⟨y, hy⟩
  have hy' : y ∈ Submodule.span ℂ (Set.range (B.ev i)) := hsp ▸ hy
  have key : ∀ y ∈ Submodule.span ℂ (Set.range (B.ev i)), ∀ hy : y ∈ M.Val, φ ⟨y, hy⟩ = ψ ⟨y, hy⟩ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨F, rfl⟩ := hz
      exact fun hy => h F _ rfl
    | zero => exact fun hy => (map_zero φ).trans (map_zero ψ).symm
    | add a b ha hb iha ihb =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      have hb' : b ∈ M.Val := hsp ▸ hb
      exact (map_add φ ⟨a, ha'⟩ ⟨b, hb'⟩).trans ((congrArg₂ (· + ·) (iha ha') (ihb hb')).trans (map_add ψ ⟨a, ha'⟩ ⟨b, hb'⟩).symm)
    | smul r a ha iha =>
      intro hy
      have ha' : a ∈ M.Val := hsp ▸ ha
      exact (map_smul φ r ⟨a, ha'⟩).trans ((congrArg (r • ·) (iha ha')).trans (map_smul ψ r ⟨a, ha'⟩).symm)
  exact key y hy' hy

theorem dilLaw_of_kerDil : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  intro D u B i sp sp' M M' R R' k K hT hI hD v a p q p' q' h h'
  obtain ⟨ζ, b, d, rfl⟩ := R.surj p
  obtain ⟨ζ', b', d', rfl⟩ := R'.surj p'
  have hq := dil_unique M h (dil_smul M (dil_pt R v a b d) (R.zeta ζ))
  have hq' := dil_unique M' h' (dil_smul M' (dil_pt R' v a b' d') (R'.zeta ζ'))
  have h0 : K.k (R.pt b ((B.J.A i).dia b (B.pr v) a d)) (R'.pt b' ((B.J.A (i + 1)).dia b' (B.pr v) a d')) =
      K.k (R.pt b d) (R'.pt b' d') := by
    refine ext_ev R _ _ fun F y hy => Subtype.ext ?_
    rw [hI _ _ _ _ F y hy, hI _ _ _ _ F y hy, hD b b' d d' (B.pr v) a]
  have hs : ∀ y : M.Val, M.act (R.zeta ζ) (M.act (R.zeta ζ)⁻¹ y) = y := fun y => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hq, hq']
  refine LinearMap.ext fun y => ?_
  rw [← hs y, K.src, K.src, hT, hT, h0]

end GlobalTheory.LvT.Built.DilPass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DilateLawPointKernelOfCoefficientKernelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dilateLaw_pointKernel_of_coefficientKernel : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (sp' : Split (B.J.A (i + 1)) B.J.T) (M : PtModel B.ch i) (M' : PtModel B.ch (i + 1)) (R : B.Real i sp M) (R' : B.Real (i + 1) sp' M') (k : B.Ker i) (K : KerPt M M'), K.TgtEq → Built.Dat.KerIs R R' K k → Built.Dat.KerDil k → K.DilLaw := by
  first | exact @GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil | exact GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil | (intros; apply GlobalTheory.LvT.Built.DilPass.dilLaw_of_kerDil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdCardStabilizerForm
noncomputable section

namespace GlobalTheory.LvT.StabOrder

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2

theorem rank_le (R : Ranks) {i j : ℕ} (h : i ≤ j) : R.N i ≤ R.N j := by
  unfold Ranks.N
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem prime_le_of_embed {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* ((Fin n → E) ≃ₗ[E] (Fin n → E))) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 := by
  haveI : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
  have h := prime_le_of_dvd_card φ.range hp (by rwa [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv])
  rwa [Module.finrank_fin_fun] at h

theorem prime_le_of_embed_GL {E G : Type} [Field E] [NumberField E] [Group G] [Finite G] {n : ℕ}
    (φ : G →* GL (Fin n) E) (hφ : Function.Injective φ) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card G) : p ≤ Module.finrank ℚ E * n + 1 :=
  prime_le_of_embed ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).toMonoidHom.comp φ))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv E (Fin n → E)).injective.comp
      ((Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := E)).injective.comp hφ)) hp hd

section Concrete

variable {F : Fields} {Pr : Primes F} {R : Ranks} {W : Wts F Pr.Word R} {a : ℝ}

variable {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 F.E))}

variable (sel : HeightOneSpectrum (𝓞 F.F) → HeightOneSpectrum (𝓞 F.E)) {S : Set ℕ} (mu : Tup F.F F.E F.K S)
  (cst : LocCst F (rowSG Pr sel mu)) (L : ChIdx F Pr R (QE sel (mu : Chr F.F F.E F.K)))

end Concrete

section Record

variable {D : D7} {u : D.what₂.Word}

theorem stabUnit_of_embed (X : Ch D u) (E : Type) [Field E] [NumberField E]
    (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T)
    (h : ∀ i, i ≤ D.R.m → ∀ c : X.C.cls i, ∃ j : X.C.stab i c →* GL (Fin (D.R.N i)) E, Function.Injective j) :
    StabUnit X := fun i hi c hd => by
  obtain ⟨j, hj⟩ := h i hi c
  have h1 := prime_le_of_embed_GL j hj X.A.T_prime hd
  have h2 := Nat.mul_le_mul_left (Module.finrank ℚ E) (rank_le D.R hi)
  omega

theorem stabUnit_of_chainIn (X : Ch D u) {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    (I : ChainIn E K D.what₂.Tau D.R) (emb : D.what₂.Tau → E →+* K) (σ : K →+* ℂ) (hI : I.Ok)
    (hC : X.C = I.chain emb σ hI (D.hcW u)) (hT : Module.finrank ℚ E * D.R.N D.R.m + 1 < X.A.T) : StabUnit X := by
  refine stabUnit_of_embed X E hT ?_
  rw [hC]
  intro i _ c
  refine ⟨((I.S i).gam c.1).comp (MulAction.stabilizer _ ((I.S i).rep c)).subtype, ?_⟩
  rw [injective_iff_map_eq_one]
  exact fun g hg => Subtype.ext ((hI.step i).stab_inj c.1 g.1 _ g.2 hg)

end Record

end GlobalTheory.LvT.StabOrder
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

namespace GlobalTheory.LvT.Built.Assemble

theorem sharpBound_stability_latticeColumnChain : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u),
    (∀ i, i ≤ D.R.m → Nonempty (Split (B.J.A i) B.J.T)) → B.Sees →
    (∀ i, i < D.R.m → ∃ k : B.Ker i, Built.Dat.KerEq k ∧ Built.Dat.KerDil k ∧ Built.Dat.KerUK k ∧ Built.Dat.KerBar k ∧
      Built.Dat.KerP k) →
    Module.finrank ℚ B.E * D.R.N D.R.m + 1 < B.J.T → TwColumn.WtSigns B.ch → Conclusion5Sharp B.ch ∧ FormsStable B.ch := by
  intro D u B hsp hsee hker hT hW

  have hM : ∀ i (h : i ≤ D.R.m), ∃ M : PtModel B.ch i, Nonempty (B.Real i (hsp i h).some M) :=
    fun i h => GlobalTheory.T.exists_levelPrimePointModel_realisation D u B i (hsp i h).some
  let Lv : LevTie B.ch := fun i h => (hM i h).choose
  have hR : ∀ i (h : i ≤ D.R.m), B.Real i (hsp i h).some (Lv i h) := fun i h => (hM i h).choose_spec.some

  have hC : ∀ i (h : i ≤ D.R.m), ∃ Co : (Lv i h).Coord, Co.Ok ∧ (hR i h).ValIs Co :=
    fun i h => GlobalTheory.T.exists_coordinates_valueLattices_eq_weylLattices D u B i (hsp i h).some (Lv i h) (hR i h) h hsee
  let Vt : ValTie Lv := fun i h => ⟨(hC i h).choose, (hC i h).choose_spec.1⟩

  have hk : ∀ i (h : i < D.R.m), ∃ k : B.Ker i, Built.Dat.KerEq k ∧ Built.Dat.KerDil k ∧ Built.Dat.KerUK k ∧
      Built.Dat.KerBar k ∧ Built.Dat.KerP k := hker

  have hK : ∀ i (h : i < D.R.m), ∃ K : KerPt (Lv i h.le) (Lv (i + 1) h),
      K.TgtEq ∧ Built.Dat.KerIs (hR i h.le) (hR (i + 1) h) K (hk i h).choose :=
    fun i h => GlobalTheory.T.exists_pointKernel_realised_models D u B i (hsp i h.le).some (hsp (i + 1) h).some (Lv i h.le) (Lv (i + 1) h)
      (hR i h.le) (hR (i + 1) h) _ (hk i h).choose_spec.1
  let Kt : KerTie Lv := fun i h => (hK i h).choose
  have laws : KerLaws Vt Kt :=
    { tgt := fun i h => (hK i h).choose_spec.1
      dil := fun i h => GlobalTheory.T.dilateLaw_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hk i h).choose_spec.2.1
      uk := fun i h => GlobalTheory.T.heckeLaw_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hk i h).choose_spec.2.2.1
      bar := fun i h => GlobalTheory.T.conjugatePrimeBound_pointKernel_of_coefficientKernel D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _ _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hC i h.le).choose_spec.1 (hC (i + 1) h).choose_spec.1
        (hC i h.le).choose_spec.2 (hC (i + 1) h).choose_spec.2 (hk i h).choose_spec.2.2.2.1
      intP := fun i h => IntPPass.intP_of_kerP D u B i _ _ _ _ (hR i h.le) (hR (i + 1) h) _ _ _ _
        (hK i h).choose_spec.1 (hK i h).choose_spec.2 (hC i h.le).choose_spec.1 (hC (i + 1) h).choose_spec.1
        (hC i h.le).choose_spec.2 (hC (i + 1) h).choose_spec.2 (hk i h).choose_spec.2.2.2.2 }
  have hF : FormsStable B.ch := formsStable_of_tgtEq D u B.ch Lv Kt laws.tgt
  have h4 : LevelChainUOperatorCommutation B.ch := levelChainUOperatorCommutation_of_pointPairLaw D u B.ch Lv Kt laws.tgt laws.uk
  have hst : StabUnit B.ch := StabOrder.stabUnit_of_chainIn B.ch B.I B.emb D.what₂.embLL B.hI rfl hT
  have hWb : WtBounds B.ch := wtBounds_of_nonneg D u B.ch hW.1 hW.2
  exact ⟨levelChainSharpColumnValuation_of_stability D u B.ch hF h4 (UKS.ukSharp D u B.ch Lv Vt Kt laws hst hWb) hWb, hF⟩

end GlobalTheory.LvT.Built.Assemble
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ColumnWeightTwisted
open Formalism.BasicNotions GlobalTheory.LvT

namespace GlobalTheory.Proof.ColumnWeightTwisted

theorem exists_int_m_mul_EatT (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ k : ℤ, (D.R.m : ℝ) * EatT D u w = (k : ℝ) := by
  unfold EatT
  split_ifs
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := D.R.t_odd
    refine ⟨(D.R.m : ℤ) * (2 * (∑ τ : D.what₂.Tau, (Wtau D u τ : ℤ)) + (D.R.f : ℤ) * (D.R.N D.R.m : ℤ)) +
      ((topsOf D.host D.eTau).card : ℤ) * ((b : ℤ) + 1) * ((D.R.m : ℤ) + 1) * a, ?_⟩
    have ha' : (D.R.m : ℝ) = a + a := by exact_mod_cast ha
    have hb' : (D.R.t : ℝ) = 2 * b + 1 := by exact_mod_cast hb
    unfold Formalism.MainNotions.G.Nm
    push_cast
    rw [hb', ha']
    ring
  · exact ⟨0, by simp⟩

theorem colGeTw_of_tupleChainSharpColumnValuation : ∀ (D : D7) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup), TupleChainSharpColumnValuation T u μ → ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∀ x ∈ LT.Nlam D u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w)) := by
  intro D T u μ h w hw x hx
  obtain ⟨k, hk⟩ := exists_int_m_mul_EatT D u w
  obtain ⟨c, hc⟩ := D.what₂.places.val_surj w ((D.what₂.places.ramIdx w : ℤ) * k)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [AddValuation.map_zero] at hc
    exact WithTop.top_ne_coe hc
  obtain ⟨y, hy, e⟩ := h w hw c _ hc (by rw [hk]; push_cast; exact le_rfl) x hx
  have hv : vAdd (D.plEq w) c = (D.what₂.places.ramIdx w : ℤ) * k := by
    rw [D.val_eq w _ hc0] at hc
    exact_mod_cast hc
  have hvi : vAdd (D.plEq w) c⁻¹ = - vAdd (D.plEq w) c := by
    unfold vAdd
    rw [map_inv₀, WithZero.log_inv]
  refine ⟨c⁻¹ • y, ?_, c⁻¹, y, hy, rfl, Or.inr ?_⟩
  · rw [LinearMap.map_smulₛₗ, e, smul_smul, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_smul]
  · rw [hvi, hv, hk]
    unfold DV.ur
    push_cast
    exact le_of_eq (by ring)

end GlobalTheory.Proof.ColumnWeightTwisted
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBounds
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws

noncomputable section
namespace GlobalTheory.LvT.Built.TrueCols

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X}

theorem trueColumns_chain_last_step_sharp_bound (h : I.Ok) (hJ : I.JetsIn) (hS : GlobalTheory.LvT.WtSign.BaseSigns B) (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : (I.rec7 l Z).what₂.Word) (a : I.ι) : Conclusion5Sharp (tw (I.tw l l0 Z) u a) := by
  obtain ⟨Bd, hch, hsp, hse, hk, hBd⟩ := GlobalTheory.T.fivePointLaws_trueChains B X I h hJ l l0 Z u a
  have hT : Module.finrank ℚ Bd.E * (I.rec7 l Z).R.N (I.rec7 l Z).R.m + 1 < Bd.J.T := by
    subst hBd
    show Module.finrank ℚ B.host.E * B.R.N B.R.m + 1 < B.T u
    have h1 := X.a_gt
    have h2 := X.T_gt u
    have hf : Module.finrank ℚ B.host.E = 2 * B.R.f := by
      rw [B.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
      ring
    rw [hf]
    have h3 : ((2 * B.R.f * B.R.N B.R.m + 1 : ℕ) : ℝ) < (B.T u : ℝ) := lt_trans h1 h2
    exact_mod_cast h3
  have hW : TwColumn.WtSigns Bd.ch :=
    (GlobalTheory.LvT.WtSign.wtSigns_assemble_iff B (I.cols l) Z.W Z.V Z.S Z.N Z.G u Bd.ch).2 hS
  have := (GlobalTheory.LvT.Built.Assemble.sharpBound_stability_latticeColumnChain (I.rec7 l Z) u Bd hsp hse hk hT hW).1
  rwa [hch] at this

theorem row_true : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B →
    ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word),
      Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ ∀ w : (I.rec7 l Z).what₂.places.Pl,
        (I.rec7 l Z).what₂.places.resChar w = ((I.rec7 l Z).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (I.rec7 l Z) μ →
        μ ≠ (I.rec7 l Z).what₂.mu0 → (I.rec7 l Z).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (I.rec7 l Z) u w,
        Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((I.rec7 l Z).R.m : ℝ) * EatT (I.rec7 l Z) u w)) := by
  intro B X I h hJ hS l l0 Z Dx u
  refine ⟨?_, fun w hw μ _ _ _ x hx => ?_⟩
  · have h0 := trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u I.mu0
    rw [← own_eq I l l0 Z u] at h0
    exact (levelChainSharpColumnValuation_ownChain_iff (I.rec7 l Z) u).1 h0
  · have hTw : TupleChainSharpColumnValuation (I.tw l l0 Z) u μ :=
      TwSharp.tupleChainSharpColumnValuation_of_twisted (I.rec7 l Z) u (I.tw l l0 Z) μ (GlobalTheory.T.twistedChain_initialLattice_compatible_trueColumns B X I h l l0 Z u μ)
        (trueColumns_chain_last_step_sharp_bound h hJ hS l l0 Z u μ)
    exact GlobalTheory.Proof.ColumnWeightTwisted.colGeTw_of_tupleChainSharpColumnValuation (I.rec7 l Z) (I.tw l l0 Z) u μ hTw w hw x hx

end GlobalTheory.LvT.Built.TrueCols
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueColumnsRowSharpBoundsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built GlobalTheory.LvT.Built.TrueLaws
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_row_sharp_bounds : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → GlobalTheory.LvT.WtSign.BaseSigns B → ∀ (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (Dx : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ ∀ w : (I.rec7 l Z).what₂.places.Pl, (I.rec7 l Z).what₂.places.resChar w = ((I.rec7 l Z).mem u).A.T → ∀ μ, Formalism.MainNotions.LocalQuadraticParts.UsedT (I.rec7 l Z) μ → μ ≠ (I.rec7 l Z).what₂.mu0 → (I.rec7 l Z).what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam (I.rec7 l Z) u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw (I.tw l l0 Z) u μ w x (-(((I.rec7 l Z).R.m : ℝ) * EatT (I.rec7 l Z) u w)) := by
  first | exact @GlobalTheory.LvT.Built.TrueCols.row_true | exact GlobalTheory.LvT.Built.TrueCols.row_true | (intros; apply GlobalTheory.LvT.Built.TrueCols.row_true <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LvT.Built.TrueCols

theorem closing_true_cols : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ColIn.JetsIn I → GlobalTheory.LvT.WtSign.BaseSigns B → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (u : (I.rec7 l Z).what₂.Word), Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp (I.rec7 l Z) u ∧ Formalism.L2.G.Adm2InU.TwistedColumnBoundAtT Y (I.tw l l0 Z) u := by
  intro B X I hOk hJ hS l Z l0 Y u
  exact GlobalTheory.T.trueColumns_row_sharp_bounds B X I hOk hJ hS l l0 Z Y u
end GlobalTheory.LvT.Built.TrueCols
