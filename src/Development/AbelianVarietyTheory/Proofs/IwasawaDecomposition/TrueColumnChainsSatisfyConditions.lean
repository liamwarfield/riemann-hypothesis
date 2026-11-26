module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditions
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

theorem GStep.Ok.reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Ok)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Ok :=
  ⟨h.fin_orb, h.fin_stab, h.unit, h.root, h.lsh_smul, h.lsh_full_lat, h.stab_inj⟩

theorem GStep.Free.reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n} (h : S.Free)
    (pref : ∀ b, S.D b → Prop) : (S.reRep pref).Free := fun b g d hd => h b g d hd

namespace TC

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.xi_unitary (h : I.Ok) (a : I.ι) : (I.xi a).IsUnitary := by
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  exact HChar.isUnitary_of_order hn ((h.xi_reads a).orderDvd hpow)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.unrepresented_step_conditions (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp0 u a i).Ok := by
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  have hPr : (B.primes X).Ok := (base_fields_primes_ok B X).2.1
  refine StepOk.stepY_ok _ _ _ _ hX _ _ ?_ ?_ ?_
  · rintro ⟨_ | b, hb⟩ P
    · exact topLev_finiteIndex I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).1
  · rintro ⟨_ | b, hb⟩ P g
    · obtain ⟨m, hm, hk⟩ := topLev_root I.Ch I.sel (I.tup a) (I.cst a) I.Ps i P
      exact ⟨m, hm, hk g⟩
    · exact (LevFin.levQ_finiteIndex_and_root I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) hX hPr
        (h.idx_ok a) i (hb.1 rfl) b P).2 g
  · exact fun N hN => (CosetFin.ysAt_finite_nonempty B.R I.sel (I.tup a) (I.cst a) i N hN).1

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_ok (h : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) : (I.stp u a i).Ok := (h.unrepresented_step_conditions u a i).reRep _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.stp_zero_free (h : I.Ok) (u : B.Word) (a : I.ι) : (I.stp u a 0).Free :=
  GStep.Free.reRep (stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u (base_fields_primes_ok B X).1
    (base_fields_primes_ok B X).2.1 (base_fields_primes_ok B X).2.2.2.2 (h.idx_ok a).zero_G) _

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.chIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.chIn u a).Ok := by
  refine
    { step := h.stp_ok u a
      rho_norm := ?_
      rho'_norm := ?_
      DG_pos := DGam_pos (posStar_of_ok (base_fields_primes_ok B X).1) B.R
      dvd_DG := ?_ }
  · intro i _ c
    show ‖((rhoAt I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt I.SQ I.C (h.xi_unitary a) i _
  · intro i _ c
    show ‖((rhoAt' I.SQ I.C (I.xi a) i _ : ℂˣ) : ℂ)‖ = 1
    exact norm_rhoAt' I.SQ I.C (h.xi_unitary a) i _
  · intro i hi c
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · have hf := h.stp_zero_free u a
      have : Subsingleton ((I.stp u a 0).Stab c) :=
        ⟨fun x y => Subtype.ext ((hf c.1 x.1 _ x.2).trans (hf c.1 y.1 _ y.2).symm)⟩
      rw [Nat.card_unique]
      exact one_dvd _
    · exact stepY_dvd _ _ _ _ ((I.Tp a).pref u i) (base_fields_primes_ok B X).1 B.R (N_mem_gamRanks B.R hpos hi) c.1 ((I.stp u a i).rep c)

theorem _root_.GlobalTheory.Mem.Col2.ColIn.Ok.idx0 (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b, by simp only [Option.isSome_some, true_iff]; exact lt_of_lt_of_le (by norm_num) B.R.two_le_m⟩⟩

theorem rep_L_lattice (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) :
    Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  ((I.stp u a i).rep c).1.1.deco.2.L_lattice

theorem ok_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.chIn u a).Ok ∧ Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) ∧ ∀ i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L :=
  fun _ h u a => ⟨h.chIn_ok u a, h.idx0 a, fun i c => rep_L_lattice u a i c⟩

end TC

end GlobalTheory.Mem.Col2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnChainsSatisfyConditionsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_chains_satisfy_conditions : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.chIn u a).Ok ∧ Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) ∧ ∀ i c, Submodule.IsLattice B.fields.E ((I.stp u a i).rep c).1.1.deco.1.L := by
  first | exact @GlobalTheory.Mem.Col2.TC.ok_chains | exact GlobalTheory.Mem.Col2.TC.ok_chains | (intros; apply GlobalTheory.Mem.Col2.TC.ok_chains <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CevInjective
noncomputable section

namespace GlobalTheory.Mem.Col2.PerConj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix
open scoped ComplexOrder

section Val

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n)

def cev : Pol ℂ ι n →ₛₗ[starRingEnd ℂ] (Fr emb σ n → ℂ) := evFr (Gr emb σ n) (shiftOf lam) (starRingEnd ℂ)

theorem cev_injective : Function.Injective (cev emb σ lam) := evFr_injective _ _ _ (fr0 emb σ n)

theorem cev_mem {P : Pol ℂ ι n} (hP : P ∈ VV ℂ lam) : cev emb σ lam P ∈ ValC (Gr emb σ n) lam :=
  ⟨_, map_mem_CSpan (starRingEnd ℂ) lam P hP, rfl⟩

theorem exists_cev {z : Fr emb σ n → ℂ} (hz : z ∈ ValC (Gr emb σ n) lam) : ∃ P ∈ VV ℂ lam, cev emb σ lam P = z := by
  obtain ⟨p, hp, rfl⟩ := hz
  have h := CSpan_le_span (starRingEnd ℂ) lam hp
  clear hp
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨P, hP, rfl⟩ := hx
    exact ⟨P, hP, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨P, hP, e⟩ := hx
    obtain ⟨Q, hQ, e'⟩ := hy
    exact ⟨P + Q, Submodule.add_mem _ hP hQ, by rw [map_add (f := _), map_add (f := _), e, e']⟩
  | smul r x _ hx =>
    obtain ⟨P, hP, e⟩ := hx
    exact ⟨starRingEnd ℂ r • P, Submodule.smul_mem _ _ hP, by rw [map_smulₛₗ, map_smul, e, Complex.conj_conj]⟩

theorem polOf_cev (P : Pol ℂ ι n) :
    polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (cev emb σ lam P) = MvPolynomial.map (starRingEnd ℂ) P := by
  have h := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (MvPolynomial.map (starRingEnd ℂ) P)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = (1 : ι → Matrix (Fin n) (Fin n) ℂ) := by
    funext τ
    exact inv_one
  rw [e] at h
  exact h

theorem nfAll_conj (p P : Pol ℂ ι n) : nfAll lam p (MvPolynomial.map (starRingEnd ℂ) P) = pairB lam p P := by
  have h1 := map_extNorm (RingHom.id ℂ) lam
  rw [RingHom.id_apply, pb_extNorm_eq] at h1
  rw [nfAll, ← h1, pairB_apply, div_eq_inv_mul]
  congr 1
  rw [fockF_eq_sum _ _ _ subset_rfl, fockB]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_map, starRingEnd_apply, star_star, mfact]

theorem ipVal_cev (P : Pol ℂ ι n) (w : Fr emb σ n → ℂ) :
    ipVal emb σ lam (cev emb σ lam P) w = pairB lam (polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) w) P := by
  rw [ipVal, ipFr_apply, polOf_cev, nfAll_conj]

theorem ipVal_pos {z : Fr emb σ n → ℂ} (hz : z ∈ ValC (Gr emb σ n) lam) (h0 : z ≠ 0) : 0 < ipVal emb σ lam z z := by
  obtain ⟨P, -, rfl⟩ := exists_cev emb σ lam hz
  rw [ipVal, ipFr_apply, polOf_cev, nfAll]
  have hP : MvPolynomial.map (starRingEnd ℂ) P ≠ 0 := by
    intro h
    apply h0
    have : P = 0 := MvPolynomial.map_injective _ (starRingEnd ℂ).injective (by rw [h, map_zero])
    rw [this, map_zero]
  exact div_pos (ps_fockF_pos _ hP)
    (Finset.prod_pos fun τ _ => ps_fockF_pos _ (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl _))

theorem cev_act [StarRing E] (hE : ∀ τ x, embAt σ emb τ (star x) = starRingEnd ℂ (embAt σ emb τ x)) (γ : GL (Fin n) E)
    (hγ : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1) (c : Kˣ) (hc : ∃ m : ℕ, 0 < m ∧ c ^ m = 1)
    (P : Pol ℂ ι n) :
    cev emb σ lam ((σ (c : K))⁻¹ • rhoP lam (embGL (embAt σ emb) γ) P) = trFr emb σ γ c (cev emb σ lam P) := by
  have h1 : starRingEnd ℂ (σ (c : K))⁻¹ = σ c := by
    obtain ⟨m, hm, hc⟩ := hc
    have h2 : σ (c : K) ^ m = 1 := by rw [← map_pow, ← Units.val_pow_eq_pow_val, hc, Units.val_one, map_one]
    have h3 : ‖σ (c : K)‖ = 1 := Complex.norm_eq_one_of_pow_eq_one h2 hm.ne'
    rw [Complex.inv_eq_conj h3, Complex.conj_conj]
  have h4 : ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) = (γ : Matrix (Fin n) (Fin n) E)ᴴ := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_left_inv hγ
  funext y
  rw [map_smulₛₗ, h1, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine (congrFun (evFr_actP (Gr emb σ n) (starRingEnd ℂ) lam (embGL (embAt σ emb) γ) P) y).trans ?_
  refine Eq.trans ?_ (fnOf_tr (G := Gr emb σ n) (G' := Gr emb σ n) (shiftOf lam) 1
    (fun τ => ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (embAt σ emb τ))
    (MvPolynomial.map (starRingEnd ℂ) P) (frMul emb σ γ⁻¹ y) y fun _ => rfl).symm
  refine congrArg (fun M => fnOf (Gr emb σ n) (shiftOf lam) M (MvPolynomial.map (starRingEnd ℂ) P) y) ?_
  funext τ
  rw [h4, Pi.one_apply, Matrix.one_mul]
  ext a b
  exact (hE τ _).symm

end Val

section Per

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

def law (b : Q.S'.β) : Q.S'.G b →* Module.End ℂ (Pol ℂ ι (R.N R.m - 1)) where
  toFun g := (σ (Q.S'.chr b g : K))⁻¹ • rhoP Q.sgT (embGL (embAt σ emb) (Q.S'.gam b g))
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, Units.val_mul]
    rw [smul_mul_smul_comm, mul_inv]

def jM : Q.Mt emb σ →ₛₗ[starRingEnd ℂ] (Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) where
  toFun F c := cev emb σ Q.sgT (F.1 c.1 (Q.S'.rep c))
  map_add' F G := by
    funext c
    exact map_add (cev emb σ Q.sgT) _ _
  map_smul' r F := by
    funext c
    exact map_smulₛₗ (cev emb σ Q.sgT) r _

variable {Q}

theorem mt_law (hH : ∀ b, Q.H b = ⊤) (F : Q.Mt emb σ) (b : Q.S'.β) (g : Q.S'.G b) (d : Q.S'.D b) :
    F.1 b (g • d) = law Q emb σ b g (F.1 b d) :=
  (F.2 b d).2 g (by rw [hH]; trivial)

theorem jM_injective (hH : ∀ b, Q.H b = ⊤) : Function.Injective (jM Q emb σ) := by
  intro F G h
  apply Subtype.ext
  funext b d
  have h1 := cev_injective emb σ Q.sgT (congrFun h (Q.S'.cl b d))
  have h2 := mt_law emb σ hH F b (Q.S'.mv b d) (Q.S'.rep (Q.S'.cl b d))
  have h3 := mt_law emb σ hH G b (Q.S'.mv b d) (Q.S'.rep (Q.S'.cl b d))
  rw [Q.S'.mv_smul] at h2 h3
  rw [h2, h3]
  exact congrArg _ h1

variable (hE : ∀ τ x, embAt σ emb τ (star x) = starRingEnd ℂ (embAt σ emb τ x))
include hE

theorem cev_law (h : Q.Ok) (b : Q.S'.β) (g : Q.S'.G b) (P : Pol ℂ ι (R.N R.m - 1)) :
    cev emb σ Q.sgT (law Q emb σ b g P) = Q.S'.tr emb σ b g (cev emb σ Q.sgT P) :=
  cev_act emb σ Q.sgT hE _ (h.step.unit b g) _ (h.step.root b g) P

theorem jM_mem (h : Q.Ok) (hH : ∀ b, Q.H b = ⊤) (F : Q.Mt emb σ) : jM Q emb σ F ∈ Q.S'.Fi emb σ Q.sgT := by
  intro c
  refine ⟨cev_mem emb σ Q.sgT (F.2 c.1 (Q.S'.rep c)).1, fun g => ?_⟩
  have h2 := mt_law emb σ hH F c.1 g.1 (Q.S'.rep c)
  rw [g.2] at h2
  exact (cev_law emb σ hE h c.1 g.1 _).symm.trans (congrArg _ h2.symm)

theorem jM_onto (h : Q.Ok) (z : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (hz : z ∈ Q.S'.Fi emb σ Q.sgT) :
    ∃ F, jM Q emb σ F = z := by
  choose P hP hPz using fun c => exists_cev emb σ Q.sgT (hz c).1
  have hfix : ∀ b q (g : Q.S'.G b), g • Q.S'.rp b q = Q.S'.rp b q → law Q emb σ b g (P ⟨b, q⟩) = P ⟨b, q⟩ := by
    intro b q g hg
    apply cev_injective emb σ Q.sgT
    rw [cev_law emb σ hE h, hPz]
    exact (hz ⟨b, q⟩).2 ⟨g, hg⟩
  have key : ∀ b q (g : Q.S'.G b) (d : Q.S'.D b), g • Q.S'.rp b q = d →
      law Q emb σ b (Q.S'.mv b d) (P (Q.S'.cl b d)) = law Q emb σ b g (P ⟨b, q⟩) := by
    intro b q g d hd
    have hq : q = Quotient.mk (MulAction.orbitRel (Q.S'.G b) (Q.S'.D b)) d := by
      rw [← Q.S'.rp_spec b q]
      exact (Quotient.sound (⟨g, hd⟩ : (MulAction.orbitRel (Q.S'.G b) (Q.S'.D b)).r d (Q.S'.rp b q))).symm
    subst hq
    have h1 : Q.S'.mv b d • Q.S'.rp b (Quotient.mk _ d) = d := Q.S'.mv_smul b d
    have h2 := hfix b (Quotient.mk _ d) (g⁻¹ * Q.S'.mv b d) (by rw [mul_smul, h1, inv_smul_eq_iff, hd])
    refine Eq.trans ?_ (congrArg (law Q emb σ b g) h2)
    rw [← Module.End.mul_apply ((law Q emb σ b) g), ← map_mul, mul_inv_cancel_left]
  refine ⟨⟨fun b d => law Q emb σ b (Q.S'.mv b d) (P (Q.S'.cl b d)), fun b d => ⟨?_, fun g _ => ?_⟩⟩, ?_⟩
  · exact Submodule.smul_mem _ _ (polyAction_mem_VV _ _ (hP _))
  · have h1 : Q.S'.mv b d • Q.S'.rp b (Quotient.mk _ d) = d := Q.S'.mv_smul b d
    refine (key b (Quotient.mk _ d) (g * Q.S'.mv b d) (g • d) (by rw [mul_smul, h1])).trans ?_
    rw [map_mul]
    rfl
  · funext c
    have h1 := key c.1 c.2 1 (Q.S'.rep c) (one_smul _ _)
    rw [map_one] at h1
    exact (congrArg (cev emb σ Q.sgT) h1).trans (hPz c)

omit hE in
theorem petersson_apply (h : Q.Ok) (z w : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) :
    Q.ipP emb σ h z w = letI := Q.clFin h; ∑ c, Q.wt c * ipVal emb σ Q.sgT (z c) (w c) := by
  simp only [PerIn.ipP, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

omit hE in
theorem period_eq (hI : I.Ok) (h : Q.Ok) (hc : ι → HCParam R) (w : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (F : Q.Mt emb σ) :
    (Q.per emb σ hI h hc).period w F = Q.ipP emb σ h (jM Q emb σ F) w := by
  rw [petersson_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (ipVal_cev emb σ Q.sgT _ _).symm

omit hE in
theorem re_petersson_self_pos (h : Q.Ok) (z : Q.S'.Cl → Fr emb σ (R.N R.m - 1) → ℂ) (hz : z ∈ Q.S'.Fi emb σ Q.sgT) (h0 : z ≠ 0) :
    0 < (Q.ipP emb σ h z z).re := by
  letI := Q.clFin h
  refine (Complex.lt_def.mp ?_ : (0 : ℂ).re < _ ∧ _).1
  rw [petersson_apply]
  have hw : ∀ c, 0 < Q.wt c := fun c => by
    haveI := h.step.fin_stab c.1 (Q.S'.rep c)
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  obtain ⟨c, hc⟩ := Function.ne_iff.1 h0
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, mul_pos (hw c) (ipVal_pos emb σ _ (hz c).1 hc)⟩
  by_cases h1 : z c = 0
  · simp [h1]
  · exact (mul_pos (hw c) (ipVal_pos emb σ _ (hz c).1 h1)).le

end Per

open Formalism.MainNotions Formalism.L2.Ker Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem period_conj : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ jM : (I.per l u a).Mt →ₛₗ[starRingEnd ℂ] (I.per l u a).Wrow, Function.Injective jM ∧ (∀ z ∈ (I.fm l u a).ptC, ∃ F, jM F = z) ∧ (∀ F, jM F ∈ (I.fm l u a).ptC) ∧ (∀ w F, (I.per l u a).period w F = (I.fm l u a).ipP (jM F) w) ∧ ∀ z ∈ (I.fm l u a).ptC, z ≠ 0 → 0 < ((I.fm l u a).ipP z z).re := by
  intro B X I _ _ l _ u a
  have hE : ∀ τ x, embAt B.embLL B.fields.emb τ (letI := B.fields.starE; star x) =
      starRingEnd ℂ (embAt B.embLL B.fields.emb τ x) := fun τ x => (GlobalTheory.Mem.FieldsLaws.fields_ok B).conjE _ x
  have hH : ∀ b, (I.perIn u a).H b = ⊤ := fun _ => rfl
  exact ⟨jM (I.perIn u a) B.fields.emb B.embLL, jM_injective _ _ hH, jM_onto _ _ hE (l.per u a),
    jM_mem _ _ hE (l.per u a) hH, period_eq _ _ (l.ch u a) (l.per u a) (B.hcW u), re_petersson_self_pos _ _ (l.per u a)⟩

end GlobalTheory.Mem.Col2.PerConj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ProperCover

theorem isFractionRing_evaluation (X : Scheme.{0}) [IsIntegral X] {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} (hx : x = genericPoint X) (hxU : x ∈ U) :
    letI := (X.evaluation U x hxU).hom.toAlgebra
    IsFractionRing Γ(X, U) (X.residueField x) := by
  subst hx
  letI := (X.evaluation U _ hxU).hom.toAlgebra
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  let e : X.functionField ≃ₐ[Γ(X, U)] X.residueField (genericPoint X) :=
    { RingEquiv.ofBijective φ ⟨φ.injective, X.residue_surjective _⟩ with
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv _ e

theorem evaluation_genericPoint_injective (X : Scheme.{0}) [IsIntegral X] (V : X.Opens)
    (hV : genericPoint X ∈ V) : Function.Injective (X.evaluation V (genericPoint X) hV) := by
  intro a b h
  apply germ_injective_of_isIntegral X _ hV
  let φ : X.functionField →+* X.residueField (genericPoint X) := (X.residue _).hom
  apply φ.injective
  exact h

theorem dim_le_of_residueDegree_pos {Z' Z : Scheme.{0}} [IsIntegral Z'] [IsIntegral Z]
    [IsLocallyNoetherian Z] (f : Z' ⟶ Z) [LocallyOfFiniteType f]
    (hg : f (genericPoint Z') = genericPoint Z) (hdeg : 0 < f.residueDegree (genericPoint Z')) :
    topologicalKrullDim Z' ≤ topologicalKrullDim Z := by
  have hd : ∀ {X : Scheme.{0}} (U : X.Opens), IsAffineOpen U →
      topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := fun {X} U hU => by
    rw [topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U))
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 Z.isBasis_affineOpens (Opens.mem_top (f x))
  obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 Z'.isBasis_affineOpens (show x ∈ f ⁻¹ᵁ U from hxU)
  refine ⟨V, V.isOpen, hxV, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le Z (U : Set Z))
  rw [hd U hU, hd V hV]
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Z, U) Γ(Z', V) := f.finiteType_appLE hU hV hVU
  have hηV : genericPoint Z' ∈ V :=
    ((genericPoint_spec Z').mem_open_set_iff V.isOpen).mpr ⟨x, trivial, hxV⟩
  have hyU : f (genericPoint Z') ∈ U := hVU hηV
  letI := (Z.evaluation U _ hyU).hom.toAlgebra
  letI := (f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  letI : Algebra Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    (Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z')).hom.toAlgebra
  haveI : IsScalarTower Γ(Z, U) (Z.residueField (f (genericPoint Z')))
      (Z'.residueField (genericPoint Z')) := IsScalarTower.of_algebraMap_eq' rfl
  haveI := isFractionRing_evaluation Z hU hg hyU
  have : Algebra.IsAlgebraic Γ(Z, U) (Z.residueField (f (genericPoint Z'))) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(Z, U))
  have : Module.Finite (Z.residueField (f (genericPoint Z'))) (Z'.residueField (genericPoint Z')) :=
    Module.finite_of_finrank_pos hdeg
  have : Algebra.IsAlgebraic Γ(Z, U) (Z'.residueField (genericPoint Z')) :=
    Algebra.IsAlgebraic.trans Γ(Z, U) (Z.residueField (f (genericPoint Z'))) _
  have hnat : f.appLE U V hVU ≫ Z'.evaluation V _ hηV =
      Z.evaluation U _ hyU ≫ f.residueFieldMap (genericPoint Z') := by
    rw [Scheme.evaluation_naturality, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp [Scheme.evaluation]
  let ψ : Γ(Z', V) →ₐ[Γ(Z, U)] Z'.residueField (genericPoint Z') :=
    { (Z'.evaluation V _ hηV).hom with
      commutes' := fun a => RingHom.congr_fun congr($(hnat).hom) a }
  have hψ : Function.Injective ψ := evaluation_genericPoint_injective Z' V hηV
  have hinj : Function.Injective (algebraMap Γ(Z, U) Γ(Z', V)) := by
    have h1 : Function.Injective (algebraMap Γ(Z, U) (Z'.residueField (genericPoint Z'))) := by
      rw [IsScalarTower.algebraMap_eq Γ(Z, U) (Z.residueField (f (genericPoint Z')))
        (Z'.residueField (genericPoint Z'))]
      exact (f.residueFieldMap (genericPoint Z')).hom.injective.comp (IsFractionRing.injective Γ(Z, U) _)
    intro a b h
    apply h1
    rw [← ψ.commutes, ← ψ.commutes, h]
  have : FaithfulSMul Γ(Z, U) Γ(Z', V) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.IsAlgebraic Γ(Z, U) Γ(Z', V) := Algebra.IsAlgebraic.of_injective ψ hψ
  exact GlobalTheory.ModelDom.ringKrullDim_le_of_isAlgebraic _ _

end GlobalTheory.ProperCover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtPointSpecializingOutsideBasicOpen
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.HorizPt

def strHom {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (U : X.Opens) : CommRingCat.of R ⟶ Γ(X, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appLE ⊤ U le_top

theorem fromSpec_str {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (strHom q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU le_top, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem charZero {X : Scheme.{0}} (q : X ⟶ Sp ℤ) [Flat q] {U : X.Opens} (hU : IsAffineOpen U)
    [Nontrivial Γ(X, U)] : CharZero Γ(X, U) := by
  have h₁ : (q.appLE ⊤ U le_top).hom.Flat :=
    HasRingHomProperty.appLE @Flat q inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : (strHom q U).hom.Flat :=
    RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv)) h₁
  have h₃ : (algebraMap ℤ Γ(X, U)).Flat := by
    rwa [Subsingleton.elim (algebraMap ℤ Γ(X, U)) (strHom q U).hom]
  have := RingHom.flat_algebraMap_iff.1 h₃
  exact charZero_of_injective_algebraMap (FaithfulSMul.algebraMap_injective ℤ Γ(X, U))

theorem main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : TrueGeo.Model Y) (W : N.X.Opens) (z : N.X) (g : Γ(N.X, W)), z ∈ W → g ≠ 0 → z ∉ N.X.basicOpen g → ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ N.X), spMap e.O.subtype ≫ yt = y.1 ≫ N.j ∧ ⊤ ≤ yt ⁻¹ᵁ W ∧ yt (IsLocalRing.closedPoint e.O) ∉ N.X.basicOpen g ∧ N.j (below y.1) ∈ N.X.basicOpen g := by
  intro F _ _ Y N W z g hz hg hzg
  have := N.ar.isIntegral
  have := N.ar.flat
  have : IsProper N.p := by
    obtain ⟨n, c, hc, h⟩ := N.ar.isProjOver
    have := isProper_str (𝓞 F) n
    rw [← h]
    infer_instance
  obtain ⟨U, hU, hzU, hUW⟩ := exists_isAffineOpen_mem_and_subset hz
  have hle : U ≤ W := hUW
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(N.X, U) := charZero (N.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(N.X, U) := (strHom N.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(N.X, U) :=
    RingHom.FiniteType.comp (N.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  set g' : Γ(N.X, U) := N.X.presheaf.map (homOfLE hle).op g with hg'
  have hg0 : g' ≠ 0 := fun h => hg (map_injective_of_isIntegral N.X (homOfLE hle) (by rw [← hg', h, map_zero]))
  have hb : ∀ x : PrimeSpectrum Γ(N.X, U), hU.fromSpec x ∈ N.X.basicOpen g ↔ g' ∉ x.asIdeal := by
    intro x
    have h₁ : hU.fromSpec x ∈ U := by
      have := hU.range_fromSpec
      exact (Set.ext_iff.1 this _).1 ⟨x, rfl⟩
    have h₂ : hU.fromSpec x ∈ N.X.basicOpen g' ↔ g' ∉ x.asIdeal := by
      change x ∈ hU.fromSpec ⁻¹ᵁ N.X.basicOpen g' ↔ _
      rw [hU.fromSpec_preimage_basicOpen]
      rfl
    rw [← h₂, hg', Scheme.basicOpen_res]
    exact ⟨fun h => ⟨h₁, h⟩, fun h => h.2⟩
  have hp : g' ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra h
    have := (hb _).2 h
    rw [hU.fromSpec_primeIdealOf] at this
    exact hzg this
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(N.X, U) 𝔪 h𝔪 g' hg0
  let yt : Sp e.O ⟶ N.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ N.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := N.pb.lift_fst _ _ hw
  refine ⟨v, e, ⟨N.pb.lift _ _ hw, N.pb.lift_snd _ _ hw⟩, yt, hy.symm, ?_, ?_, ?_⟩
  · intro x _
    exact hle ((Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩)
  · intro h
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O))).1 h ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (N.pb.lift _ _ hw ≫ N.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F))))).2 fun h => h₃ ?_
    have h' : ((φ g' : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := h
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'

end GlobalTheory.TrueGeo.HorizPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreimagePositiveResidueDegree
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory


set_option backward.isDefEq.respectTransparency.types false in
theorem exists_residueDegree_pos_of_mem_range (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g]
    [LocallyOfFiniteType g] (z : Z) (hz : z ∈ Set.range g) :
    ∃ w, g w = z ∧ 0 < g.residueDegree w := by
  obtain ⟨w₀, hw₀⟩ := hz
  let F := g.fiber z
  have hne : (Set.univ : Set F).Nonempty := ⟨(g.fiberHomeo z).symm ⟨w₀, hw₀⟩, trivial⟩
  obtain ⟨x, -, hx⟩ := IsClosed.exists_closed_singleton isClosed_univ hne
  have h₁ : LocallyOfFiniteType (F.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h₂ : LocallyOfFiniteType (g.fiberToSpecResidueField z) := by
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let h : F ⟶ Z := g.fiberι z ≫ g
  have e : h x = z := by
    have := (g.range_fiberι z).le ⟨x, rfl⟩
    simpa [h] using this
  let β : Z.residueField z ⟶ F.residueField x := (Z.residueFieldCongr e.symm).hom ≫ h.residueFieldMap x
  have hβ : Spec.map β = F.fromSpecResidueField x ≫ g.fiberToSpecResidueField z := by
    rw [← cancel_mono (Z.fromSpecResidueField z)]
    simp only [β, Spec.map_comp, Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    simp [h, Scheme.Hom.fiber_fac]
  have hβft : β.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map β) := hβ ▸ inferInstance
    exact HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) |>.mp this
  have hβf : β.hom.Finite := by
    letI := β.hom.toAlgebra
    haveI : Algebra.FiniteType (Z.residueField z) (F.residueField x) := hβft
    exact finite_of_finite_type_of_isJacobsonRing _ _
  have hhf : (h.residueFieldMap x).hom.Finite := by
    have : h.residueFieldMap x = (Z.residueFieldCongr e.symm).inv ≫ β := by simp [β]
    rw [this, CommRingCat.hom_comp]
    exact hβf.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Z.residueFieldCongr e.symm).inv).2)
  refine ⟨g.fiberι z x, e, ?_⟩
  rw [show h.residueFieldMap x = g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x
    from Scheme.residueFieldMap_comp _ _ _] at hhf
  letI := (g.residueFieldMap (g.fiberι z x)).hom.toAlgebra
  letI := ((g.fiberι z).residueFieldMap x).hom.toAlgebra
  letI := (g.residueFieldMap (g.fiberι z x) ≫ (g.fiberι z).residueFieldMap x).hom.toAlgebra
  haveI : IsScalarTower (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x))
      (F.residueField x) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (F.residueField x) := hhf
  let φ := IsScalarTower.toAlgHom (Z.residueField (g (g.fiberι z x)))
    (W.residueField (g.fiberι z x)) (F.residueField x)
  haveI : Module.Finite (Z.residueField (g (g.fiberι z x))) (W.residueField (g.fiberι z x)) :=
    Module.Finite.of_injective φ.toLinearMap φ.toRingHom.injective
  exact Module.finrank_pos

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrime
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PerLaw

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem piT_notMem_Q (h : I.Ok) (u : B.Word) (a : I.ι) (P : I.Q a) : (B.primes X).piT u ∉ P.1.asIdeal := fun hm => by
  have hPr := (base_fields_primes_ok B X).2.1
  refine T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u) P.1 P.2 ?_
  rw [← hPr.piT_norm u]
  exact P.1.asIdeal.mul_mem_right _ hm

theorem til_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b : (I.perIn u a).S'.β) (p : (I.stX a).D b) :
    ((I.perIn u a).til b p).1.1.deco = DecoSet.tilH (N_m_succ B.R) ((B.primes X).piT u) p.1.1.deco :=
  tilF_deco I.sel (I.tup a) (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) p.1.1

theorem pref_m (u : B.Word) (a : I.ι) (b : (I.stp0 u a B.R.m).β) (q : (I.stp0 u a B.R.m).D b) :
    I.pref u a B.R.m b q ↔ ∃ d, q.1.1 = tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d := by
  have hm := B.R.two_le_m
  rw [← topLev_pref_m I.Ch I.sel (I.tup a) (I.cst a) I.Ps u]
  exact ⟨fun h => h.2.2, fun h => ⟨fun e => by omega, fun e => by omega, h⟩⟩

theorem stX_ok (a : I.ι) : (I.stX a).Ok := by
  have hX := (base_fields_primes_ok B X).1
  let y := Ys.triv B.fields (B.R.N B.R.m - 1)
  let Λ := rowTyG I.Ch I.Ps
  let Θ := levQX B.R I.sel (I.tup a)
  have hRoot (g : Θ.grp) : IsOfFinOrder (Θ.chr g) := by
    rw [show Θ.chr g = ∏ P, (Θ P).lam (piProj (fun P => (Θ P).H) P g) from
      piChar_apply (fun P => (Θ P).H) (fun P => (Θ P).lam) g]
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) IsOfFinOrder.one ?_
    intro P _
    obtain ⟨m, hm, hpow⟩ := levQX_root (R := B.R) I.sel (I.tup a) P
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, hpow _⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepY_fin_orb (ST := ∅) y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) hX
      (fun _ => levQX_finiteIndex I.sel (I.tup a)) (fun _ _ => Set.finite_singleton _)
  · intro b p
    haveI : Finite (autO p.1.1.deco.1.N) := by
      first
      | exact autO_finite (posStar_of_ok hX) p.1.1.deco.full_lattice
      | exact autO_finite (posStar_of_ok hX) p.1.1.deco.full_lattice.toIsLattice
    exact Finite.of_injective _ (stabAut_inj y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) b p)
  · intro _ g
    let M : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) B.fields.E := ↑(toGLm _ _ g.1.1)
    have h : Mᴴ * 1 * M = 1 := toGLm_mem_UJ g.1
    rw [Matrix.mul_one] at h
    exact h
  · intro _ g
    exact isOfFinOrder_iff_pow_eq_one.1
      ((MonoidHom.isOfFinOrder Λ.chr (isOfFinOrder_of_finite g.2.1)).mul (hRoot g.2.2))
  · intro _ g p x
    show (↑(toGLm _ _ g.1.1) : Matrix _ _ _) *ᵥ x ∈ (p.1.1.deco.1.act g.1.1 g.2.1.1).Lsh ↔
      x ∈ p.1.1.deco.1.Lsh
    rw [toGLm_mulVec, Deco.Lsh_act _ g.1.2, mem_gmap, LinearEquiv.symm_apply_apply]
  · intro _ p
    first
    | exact p.1.1.deco.2.Lsh_full_lattice
    | exact p.1.1.deco.2.Lsh_full_lattice.toIsLattice
  · intro b g p h h₁
    exact stepY_eq_one y Unit (fun _ => Λ) (fun _ => Θ) (fun _ => True) b g p h
      (Subtype.ext ((toGLm B.fields.E (B.R.N B.R.m - 1)).injective (h₁.trans (map_one _).symm)))


set_option maxHeartbeats 1600000 in
theorem perIn_ok (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Ok := {
  step := stX_ok a
  til_smul _ g p := Subtype.ext (Prod.ext
    (tilF_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps (base_fields_primes_ok B X).2.1 u (piT_notMem_Q h u a) g p.1.1)
    (Set.image_empty _).symm)
  ext_inj _ := extTop_injective I.Ch I.sel (I.tup a) (I.cst a) I.Ps
  gam_ini _ g x := (congrArg (iniH (N_m_succ B.R)) (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x)).trans
    ((iniH_extUH _ g.1 x).trans (toGLm_mulVec g.1.1 _).symm)
  gam_last _ g x := (congrFun (toGLm_mulVec (extUH (N_m_succ B.R) g.1).1 x) _).trans (extUH_last _ g.1 x)
  chr_ext _ g := chr_extTop I.Ch I.sel (I.tup a) (I.cst a) I.Ps g
  tz_ne := by
    have hPr := (base_fields_primes_ok B X).2.1
    show star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) ≠ 0
    rw [star_ne_zero]
    intro h
    have h1 : (B.primes X).piT u = 0 := RingOfIntegers.ext h
    have h2 := hPr.piT_norm u
    rw [h1, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  Lsh_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.Lsh ↔ _
    rw [til_deco h u a b p]
    exact tilH_Lsh _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u)
      (fun P => decoFin_mem_of_mem_divs P.2) (piT_dvd_of_mem (base_fields_primes_ok B X).1 hPr u) x
  rep_til b p := by
    obtain ⟨d, hd⟩ := (pref_m u a _ _).1 (@pref_prefRep _ _ _ ((I.stp0 u a B.R.m).actD _)
      (I.pref u a B.R.m (idxTop I.sel (I.tup a) (I.idx a))) ((I.perIn u a).til b p) ((pref_m u a _ _).2 ⟨p.1.1, rfl⟩))
    exact ⟨(), trivPt _ _ _ _ _ d, (topPt_val I.sel (I.tup a) (I.cst a) u _).symm.trans
      (congrArg (topPt I.sel (I.tup a) (I.cst a) u) hd)⟩
  H_idx _ := (inferInstance : (⊤ : Subgroup _).FiniteIndex)
  H_rat _ g := ⟨g, Subgroup.mem_top _, rfl⟩ }


set_option maxHeartbeats 1600000 in
theorem perIn_over (h : I.Ok) (u : B.Word) (a : I.ι) : (I.perIn u a).Over (I.atIn u a) := {
  norm_tz := by
    show star (star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E)) *
      star (((B.primes X).piT u : 𝓞 B.fields.E) : B.fields.E) = ((B.primes X).T u : B.fields.E)
    rw [star_star]
    have h := congrArg (algebraMap (𝓞 B.fields.E) B.fields.E) ((base_fields_primes_ok B X).2.1.piT_norm u)
    rw [map_mul, map_natCast] at h
    exact h
  N_til b p x := by
    have hPr := (base_fields_primes_ok B X).2.1
    show x ∈ ((I.perIn u a).til b p).1.1.deco.1.N ↔ _
    rw [til_deco h u a b p]
    exact tilH_N _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) x
  f_til b p P x hx := by
    have hPr := (base_fields_primes_ok B X).2.1
    change x ∈ ((I.perIn u a).til b p).1.1.deco.1.N at hx
    show ((I.perIn u a).til b p).1.1.deco.1.f P x = _
    rw [til_deco h u a b p] at hx ⊢
    exact tilH_f _ p.1.1.deco (conj_piT_notMem hPr u) (piT_notMem_vGs hPr u) P x hx }

theorem perIn_laws : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok →
    ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) :=
  fun _ h u a => ⟨perIn_ok h u a, perIn_over h u a⟩

end GlobalTheory.Mem.Col2.PerLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnsPeriodMapDatumOkAndOverLevelPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_periodMapDatum_ok_and_over_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.perIn u a).Ok ∧ (I.perIn u a).Over (I.atIn u a) := by
  first | exact @GlobalTheory.Mem.Col2.PerLaw.perIn_laws | exact GlobalTheory.Mem.Col2.PerLaw.perIn_laws | (intros; apply GlobalTheory.Mem.Col2.PerLaw.perIn_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoices
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem toTerm_eTT_symm {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (s : TT (reY Z Y) (wd Z u) (wd Z u')) :
    ((eTT Z Y u u').symm s).toTerm = (eRT Z Y u u').symm s.toTerm := (by with_unfolding_all exact (Eq.refl ((eRT Z Y u u').symm s.toTerm) :))


set_option maxHeartbeats 4000000 in
def eFib {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : RT (reY Z Y) (wd Z u) (wd Z u')) :
    fib Y ((eRT Z Y u u').symm t) ≃ fib (reY Z Y) t :=
  ((eTT Z Y u u').symm.subtypeEquiv fun s => by
    rw [toTerm_eTT_symm]
    exact ((eRT Z Y u u').symm.injective.eq_iff).symm).symm


set_option maxHeartbeats 4000000 in
theorem fibFin_re {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (u u' : D.what₂.Word)
    (t : RT (reY Z Y) (wd Z u) (wd Z u')) : Finite (fib (reY Z Y) t) := by
  have := h.fibFin u u' ((eRT Z Y u u').symm t)
  exact Finite.of_equiv _ (eFib Z Y u u' t)


set_option maxHeartbeats 4000000 in
theorem pairIndep_re {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (u u' : D.what₂.Word)
    (s₁ s₂ s₁' s₂' : TT (reY Z Y) (wd Z u) (wd Z u')) (e₁ : s₁.toTerm = s₁'.toTerm) (e₂ : s₂.toTerm = s₂'.toTerm)
    (r₁ : rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₁ = rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₂)
    (r₂ : rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₁' = rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₂') :
    s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂') := by
  have e₁' : ((eTT Z Y u u').symm s₁).toTerm = ((eTT Z Y u u').symm s₁').toTerm := by
    rw [toTerm_eTT_symm, toTerm_eTT_symm, e₁]
  have e₂' : ((eTT Z Y u u').symm s₂).toTerm = ((eTT Z Y u u').symm s₂').toTerm := by
    rw [toTerm_eTT_symm, toTerm_eTT_symm, e₂]
  have := h.pairIndep u u' ((eTT Z Y u u').symm s₁) ((eTT Z Y u u').symm s₂)
    ((eTT Z Y u u').symm s₁') ((eTT Z Y u u').symm s₂') e₁' e₂' ((by with_unfolding_all exact (r₁ :))) ((by with_unfolding_all exact (r₂ :)))
  with_unfolding_all exact this


set_option maxHeartbeats 16000000 in
theorem finX_reY : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  intro D Z X Y h
  refine
  { shInj := (by with_unfolding_all exact (h.shInj :))
    shSurj := (by with_unfolding_all exact (h.shSurj :))
    inHH := by with_unfolding_all exact h.inHH
    puLin := by with_unfolding_all exact h.puLin
    finHH := (by with_unfolding_all exact (h.finHH :))
    fibFin := (by with_unfolding_all exact (fibFin_re Z h :))
    pairIndep := (by with_unfolding_all exact (pairIndep_re Z h :))
    Greal := ?_
    cdEx := (by with_unfolding_all exact (h.cdEx :))
    volPos := (by with_unfolding_all exact (h.volPos :)) }
  intro u u' t
  with_unfolding_all exact h.Greal u u' ((eRT Z Y u u').symm t)

end GlobalTheory.Mem.SRe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoicesStatement
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finX_spectralRedivisionFullChoices : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  first | exact @GlobalTheory.Mem.SRe.finX_reY | exact GlobalTheory.Mem.SRe.finX_reY | (intros; apply GlobalTheory.Mem.SRe.finX_reY <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.LevelLaw

theorem ok_reRep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Ok T) :
    TDat.Ok (S := S.reRep pref) { A with } T :=
  { h with }

theorem tied_reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ} (pref : ∀ b, S.D b → Prop) (h : A.Tied T) :
    TDat.Tied (S := S.reRep pref) { A with } T :=
  { h with }

theorem atIn_ok : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  intro B X I h u a
  obtain ⟨hX, hPr, -, -, hbig⟩ := base_fields_primes_ok B X
  have hQ : ∀ w ∈ I.Q a, ((B.primes X).T u : 𝓞 B.fields.E) ∉ w.asIdeal :=
    T_notMem_QE I.sel (I.tup a) u hPr h.sel_ok (h.T_mem u)
  exact
    { T_prime := hPr.T_prime u
      card_ST := (hPr.vT_card u).trans B.fields_f
      card_res := fun P => (card_res P.1).trans (hPr.vT_norm u P.1 P.2)
      lev := fun j => ok_reRep (I.pref u a j) (tdatAt_ok I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u j)
      tied := fun j => tied_reRep (I.pref u a j) (tdatAt_tied I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) hX hPr u hQ j)
      psi_ne := fun P => psiWeil_ne_one (xiUnitAt_vT B X u P).2
      free0 := stepAt_zero_free I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (I.Tp a) u hX hPr hbig (h.idx_ok a).zero_G
      duStar_pos := B.duStar_pos u
      Dstar_pos := B.Dstar_pos
      one_lt_gammaP := B.one_lt_gammaP }

end GlobalTheory.Mem.Col2.LevelLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDataOkOfTrueColumnChoicesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeData_ok_of_trueColumnChoices : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a, (I.atIn u a).Ok := by
  first | exact @GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | exact GlobalTheory.Mem.Col2.LevelLaw.atIn_ok | (intros; apply GlobalTheory.Mem.Col2.LevelLaw.atIn_ok <;> assumption)
end
end
