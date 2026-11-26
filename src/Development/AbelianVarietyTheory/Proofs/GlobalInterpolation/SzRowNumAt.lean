module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitConstantsParameterConditionsLarge
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNodeGapBlockLength
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowElevenLeSplitBound
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FieldIsoSelfDualAndPeriodLatticesAgree
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BandWidthLeInvSqOfRankBounds
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem bandWidth_le_inv_sq_of_rank_bounds (x e n k d La B c : ℝ) (hx : 1 < x) (hd0 : 0 ≤ d) (hd : d ≤ 1) (hn0 : 0 ≤ n)
    (hn : n ≤ 2 * x ^ (2 + 8 * e)) (hk : x ^ (9 / 2 + 10 * e) ≤ k) (hLa0 : 0 ≤ La)
    (hLa : La ≤ B * Real.log x ^ 2 * (2 * x ^ e))
    (h1 : 64 * B * x ^ (2 + 10 * e) * Real.log x ^ 2 ≤ x ^ (5 / 2 + 10 * e))
    (h2 : 4 * |c| * B * x ^ e * Real.log x ^ 3 ≤ x ^ (5 / 2 + 10 * e)) :
    4 * (2 * n * d) * x ^ e * La / k + c * Real.log x * La / k ≤ x ^ (-2 : ℝ) := by
  have hx0 : 0 < x := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hk
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx.le
  have hxe : 0 < x ^ e := Real.rpow_pos_of_pos hx0 _
  have e1 : x ^ (2 + 10 * e) = x ^ (2 + 8 * e) * x ^ e * x ^ e := by
    rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
  have e2 : x ^ (5 / 2 + 10 * e) = x ^ (-2 : ℝ) * x ^ (9 / 2 + 10 * e) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have hnd : n * d ≤ 2 * x ^ (2 + 8 * e) := le_trans (mul_le_of_le_one_right hn0 hd) hn
  have t1 : 4 * (2 * n * d) * x ^ e * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc 4 * (2 * n * d) * x ^ e * La = 8 * (n * d) * x ^ e * La := by ring
      _ ≤ 8 * (2 * x ^ (2 + 8 * e)) * x ^ e * (B * Real.log x ^ 2 * (2 * x ^ e)) := by gcongr
      _ = 64 * B * x ^ (2 + 10 * e) * Real.log x ^ 2 / 2 := by rw [e1]; ring
      _ ≤ _ := by linarith
  have t2 : c * Real.log x * La ≤ x ^ (5 / 2 + 10 * e) / 2 := by
    calc c * Real.log x * La ≤ |c| * Real.log x * (B * Real.log x ^ 2 * (2 * x ^ e)) := by
          gcongr
          exact le_abs_self c
      _ = 4 * |c| * B * x ^ e * Real.log x ^ 3 / 2 := by ring
      _ ≤ _ := by linarith
  rw [← add_div, div_le_iff₀ hk0]
  have t3 : x ^ (5 / 2 + 10 * e) ≤ x ^ (-2 : ℝ) * k := by
    rw [e2]; gcongr
  linarith

theorem szRow_band_lambda_primes :
    SzRow (fun C D L => G.rhoB D C.GK L.sc ≤ L.sc.x ^ (-2 : ℝ) ∧ L.sc.x ^ L.sc.eps ≤ L.LaG ∧
      (∀ j : Fin 2, ((D.host.g j : ℕ) : ℝ) ≤ Real.exp (9 * L.sc.L)) ∧ (D.host.pde : ℝ) < L.sc.X' ∧
      (D.host.pde' : ℝ) < L.sc.X' ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  intro eps he0 he1 C hC
  refine ⟨0, fun cD _ => ⟨0, fun ch _ => ?_⟩⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hpde, -, hmid, -⟩ := hC
  have hKLa : 1 ≤ C.GK.La := hmid _ (by simp [FC.cMid])
  obtain ⟨CN, x1, h1⟩ := GlobalTheory.topCount_and_lambda_bounds eps he0 he1
  obtain ⟨x2, h2⟩ := GlobalTheory.EX.hostBounds eps C.P.Cpde he0 he1 hpde
  obtain ⟨x3, h3⟩ := GlobalTheory.scale_poly_comparison eps 41 1 he0 one_pos
  obtain ⟨x4, h4⟩ := GlobalTheory.scale_poly_comparison eps (2 * C.P.Cpde) 1 he0 one_pos
  obtain ⟨x5, h5⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow (2 + 10 * eps) (5 / 2 + 10 * eps)
    (64 * (C.GK.La * CN ^ 2)) 2 (by linarith)
  obtain ⟨x6, h6⟩ := GlobalTheory.const_mul_rpow_mul_log_pow_le_rpow eps (5 / 2 + 10 * eps)
    (4 * |C.GK.rho * C.GK.CN| * (C.GK.La * CN ^ 2)) 3 (by linarith)
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max (max x5 x6) 512), fun D L he hx hV => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨hx1, hx2⟩, hx3, hx4⟩, ⟨hx5, hx6⟩, hx7⟩ := hx
  have hx1' := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  obtain ⟨-, -, hLa⟩ := h1 L.sc he hx1
  obtain ⟨hLa1, hLa2⟩ := hLa C.GK hKLa
  obtain ⟨-, -, -, -, -, -, -, -, hp1, hp2⟩ := h2 L.sc D.R D.host he hx2 hV.ranks hV.host
  obtain ⟨-, -, hb, -⟩ := h3 L.sc he hx3
  obtain ⟨-, -, -, -, -, -, hX⟩ := h4 L.sc he hx4
  have hy0 : 0 < L.sc.x ^ (L.sc.eps / 100) := Real.rpow_pos_of_pos hx0 _
  have hn : (D.R.n : ℝ) / L.sc.x ^ (L.sc.eps / 100) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) := by
    rw [div_le_iff₀ hy0, mul_assoc, ← Real.rpow_add hx0]
    exact hV.ranks.n_le
  have hd : L.sc.delta1 * L.sc.x ^ (L.sc.eps / 100) ≤ 1 := by
    unfold Scale.delta1
    rw [← Real.rpow_add hx0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1'.le (by have := L.sc.eps_pos; linarith)
  have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0.le _
  have hnd : 2 * (D.R.n : ℝ) * L.sc.delta1 =
      2 * ((D.R.n : ℝ) / L.sc.x ^ (L.sc.eps / 100)) * (L.sc.delta1 * L.sc.x ^ (L.sc.eps / 100)) := by
    field_simp
  obtain ⟨-, -, ⟨hk1, hk2⟩, -⟩ := hV.ranks
  obtain ⟨-, hTT, -, -, hg, -⟩ := hV.host
  rw [Real.rpow_one] at hb hX
  have hp : ∀ y : ℝ, Real.log y ≤ 2 * C.P.Cpde * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 → y < L.sc.X' := by
    intro y hy
    have a1 : y ≤ Real.exp (2 * C.P.Cpde * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2) :=
      (Real.le_exp_log y).trans (Real.exp_le_exp.2 hy)
    have a2 : 1 < L.sc.x ^ (2 * C.P.Cpde) := Real.one_lt_rpow hx1' (by linarith)
    exact lt_of_le_of_lt a1 (lt_of_lt_of_le (lt_mul_of_one_lt_right (Real.exp_pos _) a2) hX)
  refine ⟨?_, hV.La_eq ▸ hLa1, fun j => ?_, hp _ hp1, hp _ hp2, hTT, ?_⟩
  · unfold G.rhoB G.Nstar
    rw [hnd]
    refine bandWidth_le_inv_sq_of_rank_bounds L.sc.x L.sc.eps _ _ _ _ (C.GK.La * CN ^ 2) _ hx1'
      (mul_nonneg hd0 hy0.le) hd (div_nonneg (Nat.cast_nonneg _) hy0.le) hn hk1
      ((Real.rpow_nonneg hx0.le _).trans hLa1) hLa2 ?_ ?_
    · rw [he]; exact h5 _ hx5
    · rw [he]; exact h6 _ hx6
  · have hk5 : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℝ) := by
      refine hk2.trans ?_
      have : L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ L.sc.x ^ (5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1'.le (by rw [he]; linarith)
      linarith
    have hX1 : 1 ≤ L.sc.X' := Real.one_le_exp (Real.rpow_nonneg hx0.le _)
    have hb0 : 0 < L.sc.b := Real.exp_pos _
    have h41 : L.sc.x ^ (41 : ℕ) ≤ L.sc.b := by
      have : L.sc.x ^ (41 : ℝ) ≤ L.sc.b :=
        (le_mul_of_one_le_right (Real.rpow_nonneg hx0.le _) hX1).trans hb
      exact_mod_cast this
    have hk5' : (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (5 : ℕ) := by exact_mod_cast hk5
    have e9 : Real.exp (9 * L.sc.L) = L.sc.b ^ 9 := by
      unfold Scale.b; rw [← Real.exp_nat_mul]; norm_num
    calc ((D.host.g j : ℕ) : ℝ) ≤ 2 * ((D.R.k : ℝ) * L.sc.b) ^ 8 := (hg j).2
      _ ≤ 2 * ((2 * L.sc.x ^ (5 : ℕ)) * L.sc.b) ^ 8 := by gcongr
      _ = 512 * L.sc.x ^ 40 * L.sc.b ^ 8 := by ring
      _ ≤ L.sc.x * L.sc.x ^ 40 * L.sc.b ^ 8 := by gcongr
      _ = L.sc.x ^ 41 * L.sc.b ^ 8 := by ring
      _ ≤ L.sc.b * L.sc.b ^ 8 := by gcongr
      _ = _ := by rw [e9]; ring
  · unfold ChCode_at
    rw [hV.words]
    exact Nat.le_ceil _

end GlobalTheory.EX
end

open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem szRow_numAt :
    SzRow (fun C D L => HostArith D.host → Nonempty (NumAt C L) ∧ ChTT_at L ∧ ChCode_at L 3 C.P.CF) := by
  refine szRow_and_imp.2 _ _ (szRow_and_imp.1 _ _ (szRow_and_imp.1 _ _ explicitConstants_parameterConditions_large szRow_blockLengthParams)
    (szRow_and_imp.1 _ _ szRow_sizesAt szRow_band_lambda_primes)) ?_
  rintro C cD ch D L hC hV ⟨⟨h5, hT⟩, hS, hrho, hLa, hg, hp, hp', hTT, hCode⟩ hA
  obtain ⟨P, hPK, hPW⟩ := h5 hA
  obtain ⟨T, hTK, hTe⟩ := hT P hPW
  have hCt : C.Ct = 401 := hC.1.2.2.2.2.2.2.2.2.2
  obtain ⟨hn, hm, hk, -⟩ := hV.ranks
  obtain ⟨-, -, -, -, -, hLw, hcc, -⟩ := hV.host
  refine ⟨⟨{ params := P
             params_K := hPK
             CnW_eq := hPW
             parT := T
             parT_K := hTK
             eP_eq := hTe
             sizes := hS
             rho_le := hrho
             CGam_eq := hV.CGam_eq
             Cc_eq := hV.Cc_eq
             Ct_eq := hV.Ct_eq
             secondConstant_eq := hV.secondConstant_eq
             LaG_ge := hLa
             bT_le := hV.bT_le
             ccK_top := hcc
             g_le := hg
             pde_lt := ⟨hp, hp'⟩
             logFiveDepth_eq := hV.logFiveDepth_eq
             Lw_eq := ?_
             cloud1 := fun τ τ' => ?_
             win := ⟨hn, hm, hk⟩ }⟩, hTT, hCode⟩
  · rw [hLw, hCt]; unfold Lwv; norm_num
  · funext i
    rw [hV.hc.1 τ i, hV.hc.1 τ' i]

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsClassSumPairingOfIsFormsOf
noncomputable section

namespace GlobalTheory.PeriodOnStep

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.DivisionValues
open GlobalTheory.IndefiniteRowSideFullHecke
open GlobalTheory.PeriodClassSum GlobalTheory.Mem.Col2
open scoped Matrix ComplexOrder

section Step

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

theorem Lsh_eq_N {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) : d.1.Lsh = d.1.N := by
  have e : d.1.L = d.1.N := by
    rw [Deco.L]
    simp
  rw [Deco.Lsh, e]
  exact d.2.uni

theorem emb_mem_cmMax (hX : X.Ok) (τ : X.Tau) (x : X.E) : X.emb τ x ∈ cmMax X.K := fun φ => by
  rw [← hX.emb_star]
  exact hX.conjE (φ.comp (X.emb τ)) x

theorem root_mem_cmMax (hX : X.Ok) {c : X.K} (hc : ∃ m : ℕ, 0 < m ∧ c ^ m = 1) : c ∈ cmMax X.K := fun φ => by
  obtain ⟨m, hm, hc⟩ := hc
  have h1 := star_mul_root hX.conjK hm hc
  have h2 : star (φ c) * φ c = 1 := by
    have h3 : ‖φ c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hc, map_one]) hm.ne'
    rw [← starRingEnd_apply, Complex.conj_mul', h3]
    simp
  have h0 : φ c ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine mul_right_cancel₀ h0 ?_
  rw [← map_mul, h1, map_one, starRingEnd_apply, h2]

theorem row_act_rat (hX : X.Ok) (g : (mtildeGSD W Ch sel mu P).G) (i j) :
    (mtildeGSD W Ch sel mu P).bV.repr ((mtildeGSD W Ch sel mu P).ρ g ((mtildeGSD W Ch sel mu P).bV j)) i ∈ cmMax X.K := by
  rw [formGSD_rho, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem (root_mem_cmMax hX (LevFam.chr_root _ _))
    (coefAction_repr_mem_subfield X.emb _ W.sgTrue (emb_mem_cmMax hX) _ i j).1

theorem isFormsOf_MtildeH (hX : X.Ok) : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P)
    (MtildeH W Ch hX sel mu P) (LinearEquiv.refl _ _) :=
  isFormsOf_toH _ _ (row_act_rat W Ch sel mu P hX) (fun v => by rw [row_gramV]; exact gramB_posDef _ _) _

def rowPt (c : (stepX Ch sel mu P).Cl) : RowPt Pr R sel mu := toRow sel mu ((stepX Ch sel mu P).rep c).1.1

def rowCl (c : (stepX Ch sel mu P).Cl) : (mtildeGSD W Ch sel mu P).Cl := (mtildeGSD W Ch sel mu P).cls (rowPt Ch sel mu P c)

theorem rowCl_surjective : Function.Surjective (rowCl W Ch sel mu P) := by
  rintro ⟨d⟩
  obtain ⟨p, rfl⟩ := toRow_surjective sel mu d
  refine ⟨(stepX Ch sel mu P).cl () (trivPt X _ _ _ _ p), ?_⟩
  obtain ⟨g, hg⟩ := (stepX Ch sel mu P).exists_mv () (trivPt X _ _ _ _ p)
  have h1 := congrArg (fun q => toRow sel mu q.1.1) hg
  refine Eq.symm (((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).2 ⟨toRowG Ch sel mu P g, ?_⟩)
  exact (toRow_smul Ch sel mu P g _).symm.trans h1

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))

include hd in
theorem exists_step_smul (a : FormG (rowTy Ch sel mu P).inv) (p q : (stepX Ch sel mu P).D ())
    (h : a • toRow sel mu p.1.1 = toRow sel mu q.1.1) :
    ∃ g : (stepX Ch sel mu P).G (), toRowG Ch sel mu P g = a ∧ (letI := (stepX Ch sel mu P).actD (); g • p) = q := by
  obtain ⟨g, h1, h2⟩ := exists_toRowG_smul Ch sel mu P hd a _ _ h
  refine ⟨g, h1, (trivPt X _ _ _ _).symm.injective h2⟩

include hd in
theorem rowCl_injective : Function.Injective (rowCl W Ch sel mu P) := by
  rintro ⟨⟨⟩, c⟩ ⟨⟨⟩, c'⟩ h
  obtain ⟨a, ha⟩ := ((mtildeGSD W Ch sel mu P).cls_eq_iff _ _).1 h
  obtain ⟨g, -, hg⟩ := exists_step_smul Ch sel mu P hd a _ _ ha
  refine congrArg (Sigma.mk ()) ?_
  rw [← (stepX Ch sel mu P).rp_spec () c, ← (stepX Ch sel mu P).rp_spec () c']
  exact Quotient.sound ⟨g, hg⟩

def clEquiv : (stepX Ch sel mu P).Cl ≃ (mtildeGSD W Ch sel mu P).Cl :=
  Equiv.ofBijective _ ⟨rowCl_injective W Ch sel mu P hd, rowCl_surjective W Ch sel mu P⟩

include hd in
theorem card_stab (c : (stepX Ch sel mu P).Cl) : Nat.card ((stepX Ch sel mu P).Stab c) =
    Nat.card (MulAction.stabilizer (mtildeGSD W Ch sel mu P).G (rowPt Ch sel mu P c)) := by
  refine Eq.trans ?_ (card_stabilizer_toRow Ch sel mu P hd _)
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun g => ?_)
  exact (trivPt X _ _ _ _).symm.injective.eq_iff.symm

variable (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok)

end Step

section Lattice

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K)))
  (hF : ((stepX Ch sel mu P).fam X.emb W.sgTrue).Ok) (h' : (dualGSD W Ch sel mu P).Ok)

end Lattice

section Pol

variable {K : Type} [Field K] (σ : K →+* ℂ)

theorem map_fockB {τ : Type} (f g : MvPolynomial τ K) : σ (fockB f g) = fockB (MvPolynomial.map σ f) (MvPolynomial.map σ g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [fockB_eq_sum _ _ f.support (MvPolynomial.support_map_subset _ _), fockB, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_mul, map_mul, map_natCast, MvPolynomial.coeff_map, MvPolynomial.coeff_map]

theorem map_pairB {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (F F' : Pol K ι n) :
    σ (pairB lam F F') = pairB lam (MvPolynomial.map σ F) (MvPolynomial.map σ F') := by
  rw [pairB_apply, pairB_apply, map_mul, map_inv₀, map_fockB, extNormB, extNormB, map_prod]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => by rw [map_fockB, Formalism.L2.DIV.map_extremal]

theorem polOf_evV {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* K) (lam : ι → DomWeight n) (x : VV K lam) :
    polOf (Gr emb σ n) (Formalism.L2.Forms.shiftOf lam) (fr0 emb σ n) (evV emb 1 lam σ x) = MvPolynomial.map σ x.1 := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun _ => inv_one
  rw [evV_apply, ← e, polOf_fnOf]

end Pol

section Layer

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) {I : ChainIn X.E X.K X.Tau R} (b0 : (I.S R.m).β)
  (til : ∀ b, (stepX Ch sel mu P).D b → (I.S R.m).D b0) (ext : ∀ b, (stepX Ch sel mu P).G b →* (I.S R.m).G b0)
  (tz : X.E) (H : ∀ b, Subgroup ((stepX Ch sel mu P).G b))

@[reducible] def perOn : PerIn I where
  S' := stepX Ch sel mu P
  b0 := b0
  til := til
  ext := ext
  sg := W.sgW
  tz := tz
  H := H

variable (hd : Disjoint Pr.vGs (QE sel (mu : Chr X.F X.E X.K))) (σ : X.K →+* ℂ)

include hd in
theorem row_law (z : (mtildeGSD W Ch sel mu P).EqFun) (g : (stepX Ch sel mu P).G ()) (d : (stepX Ch sel mu P).D ()) :
    MvPolynomial.map σ (z.1 (toRow sel mu (letI := (stepX Ch sel mu P).actD (); g • d : (stepX Ch sel mu P).D ()).1.1)).1 =
      (σ ((stepX Ch sel mu P).chr () g : X.K))⁻¹ • rhoP W.sgTrue (embGL (embAt σ X.emb) ((stepX Ch sel mu P).gam () g))
        (MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1) := by
  have h1 := z.2 (toRowG Ch sel mu P g) (toRow sel mu d.1.1)
  rw [mtilde_rho_toRowG W Ch sel mu P hd] at h1
  have h2 := (congrArg z.1 (toRow_smul Ch sel mu P g d.1.1)).trans h1
  refine (congrArg (fun y : VV X.K W.sgTrue => mapS σ y.1) h2).trans ?_
  refine (LinearMap.map_smulₛₗ (mapS σ) _ (actP W.sgTrue (embGL X.emb (ufGL _ _ g.1)) (z.1 (toRow sel mu d.1.1)).1)).trans ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, mapS_apply, GlobalTheory.ValCmp.use₂]
  congr 1

def rowEmb : (mtildeGSD W Ch sel mu P).EqFun →ₛₗ[σ] (perOn W Ch sel mu P b0 til ext tz H).Mt X.emb σ where
  toFun z := ⟨fun _ d => MvPolynomial.map σ (z.1 (toRow sel mu d.1.1)).1, fun _ d =>
    ⟨GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ W.sgTrue _ (z.1 (toRow sel mu d.1.1)).2, fun g _ => row_law W Ch sel mu P hd σ z g d⟩⟩
  map_add' _ _ := Subtype.ext (funext fun _ => funext fun _ => map_add (mapS σ) _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => funext fun _ => LinearMap.map_smulₛₗ (mapS σ) _ _)

variable (hX : X.Ok) (hc : X.Tau → HCParam R)
  {Pl : Rows.Places X.K} (J : AtIn I) (Z : FmIn J Pl) (hI : I.Ok) (hJ : J.Ok)
  (hQ : (perOn W Ch sel mu P b0 til ext tz H).Ok) (l : J.Laws X.emb σ hc)
  (lf : FmLaws J (perOn W Ch sel mu P b0 til ext tz H) X.emb σ hc Pl hI hQ)
  (hT : (perOn W Ch sel mu P b0 til ext tz H).Over J)

section AnyLattice

variable {Λ' : HLat X.K} {ι : Λ'.V ≃ₗ[X.K] (mtildeGSD W Ch sel mu P).EqFun}
  (hι : IsFormsOf _ (mtildeOk W Ch sel mu hX P) (MtildeL W Ch sel mu P) Λ' ι)

include hι

end AnyLattice

end Layer

end GlobalTheory.PeriodOnStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFacts
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.LatFin

theorem _root_.GlobalTheory.MomT.LatFin.per_lattice_facts : ∀ (X : _root_.Formalism.L2.Col.Fields) (A : _root_.Formalism.L2.Ker.Amb X) (a b : ℕ)
    (N : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E a)) (N' : Submodule (𝓞 X.E) (_root_.Formalism.L2.Col.Sp X.E b)),
    A.AA.FG → A.AA ≠ ⊥ → _root_.Formalism.L2.Col.IsSdLat N → _root_.Formalism.L2.Col.IsSdLat N' → (_root_.GlobalTheory.MomT.per A N N').FG ∧
    (∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N') ∧
    (∀ r : 𝓞 X.E, r ≠ 0 → (_root_.GlobalTheory.MomT.smulLat (r : X.E)
      (_root_.GlobalTheory.MomT.per A N N')).toAddSubgroup.relIndex
        (_root_.GlobalTheory.MomT.per A N N').toAddSubgroup ≠ 0) ∧
    ∀ P : HeightOneSpectrum (𝓞 X.E), _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A.AA =
      _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : _root_.Formalism.L2.Col.HomE X.E a b,
      y ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (_root_.GlobalTheory.MomT.per A N N') ↔
        ∀ v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N, y v ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N' := by
  intro X A a b N N' hAfg hA hN hN'
  have full_of_sd {n : ℕ} {L : Submodule (𝓞 X.E) (Sp X.E n)}
      (hL : IsSdLat L) : Submodule.IsFullLattice X.E L := by
    let := hL.1
    refine { span_eq_top := ?_ }
    let W := Submodule.span X.E (L : Set (Sp X.E n))
    change W = ⊤
    by_contra hW
    let e : Sp X.E n ≃ₗ⋆[X.E] Sp X.E n := starLinearEquiv X.E
    let g : Sp X.E n →ₗ[X.E] Module.Dual X.E W :=
      (LinearMap.domRestrict' W).comp ((hStd X.E n).comp e.toLinearMap)
    have hdim : Module.finrank X.E (Module.Dual X.E W) < Module.finrank X.E (Sp X.E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt hW
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (c : X.E) : c • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd X.E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual X.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : X.E →ₗ[𝓞 X.E] L :=
      ((LinearMap.toSpanSingleton X.E _ (e x)).restrictScalars (𝓞 X.E)).codRestrict L hsmul
    let : Module.Finite (𝓞 X.E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 X.E) X.E := Module.Finite.of_injective i fun c d hcd =>
      smul_left_injective X.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hcd)
    exact RingOfIntegers.not_isField X.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 X.E) X.E) (Field.toIsField X.E))
  have hNfull := full_of_sd hN
  have hN'full := full_of_sd hN'
  obtain ⟨hNl, -⟩ := hN
  obtain ⟨hN'l, -⟩ := hN'
  have hfull : _root_.GlobalTheory.ThetaMove.Full (_root_.Formalism.L2.Ker.perO A.AA N N') :=
    _root_.GlobalTheory.ThetaMove.PeriodComp.full A.AA N N' hNl.fg hN'full hA
  have hfg : (_root_.GlobalTheory.MomT.per A N N').FG :=
    _root_.GlobalTheory.ThetaMove.VolumePos.perO_fg hAfg
      (_root_.GlobalTheory.ThetaMove.VolumePos.homO_fg hNl.fg hN'l.fg (by
        let := hNfull
        exact Submodule.IsFullLattice.span_eq_top))
  have hmult : ∀ x : _root_.Formalism.L2.Col.HomE X.E a b, ∃ n : ℕ, 0 < n ∧
      (n : X.E) • x ∈ _root_.GlobalTheory.MomT.per A N N' := by
    intro x
    obtain ⟨n, hn, hx⟩ := hfull x
    refine ⟨n, hn, ?_⟩
    unfold _root_.GlobalTheory.MomT.per
    rw [Nat.cast_smul_eq_nsmul]
    rwa [Nat.cast_smul_eq_nsmul] at hx
  refine ⟨hfg, hmult, ?_, ?_⟩
  · intro r hr
    refine _root_.GlobalTheory.ThetaMove.VolumePos.relIndex_ne_zero ?_ hfg
    intro x
    obtain ⟨n, hn, hx⟩ := hmult ((r : X.E)⁻¹ • x)
    refine ⟨n, hn, ?_⟩
    rw [_root_.GlobalTheory.MomT.mem_smulLat]
    refine ⟨_, hx, ?_⟩
    have hr' : (r : X.E) ≠ 0 := by exact_mod_cast hr
    rw [smul_smul, smul_smul, mul_comm (r : X.E), mul_assoc, mul_inv_cancel₀ hr', mul_one,
      Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · intro P hP y
    unfold _root_.GlobalTheory.MomT.per
    constructor
    · intro hy v hv
      obtain ⟨s, hs, hsy⟩ := (_root_.Formalism.L2.Col.mem_locP P _ y).mp hy
      refine _root_.GlobalTheory.MomT.IdxBound.mem_localization_of_smul_mem P N' hs ?_
      simpa using _root_.GlobalTheory.MomT.IdxBound.per_apply_mem hP hsy hv
    · intro hy
      exact _root_.GlobalTheory.MomT.IdxBound.mem_localization_perO hP hNl.fg fun v hv =>
        hy v (_root_.GlobalTheory.ThetaMove.mem_localization_of_mem P hv)

end GlobalTheory.MomT.LatFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PerLatticeFactsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.per_relIndex_ne_zero_and_mem_locP_iff : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), A.AA.FG → A.AA ≠ ⊥ → IsSdLat N → IsSdLat N' → (per A N N').FG ∧ (∀ x : HomE X.E a b, ∃ n : ℕ, 0 < n ∧ (n : X.E) • x ∈ per A N N') ∧ (∀ r : 𝓞 X.E, r ≠ 0 → (smulLat (r : X.E) (per A N N')).toAddSubgroup.relIndex (per A N N').toAddSubgroup ≠ 0) ∧ ∀ P : HeightOneSpectrum (𝓞 X.E), localization₂ P.asIdeal A.AA = localization₂ P.asIdeal (1 : Submodule (𝓞 X.E) X.E) → ∀ y : HomE X.E a b, y ∈ localization₂ P.asIdeal (per A N N') ↔ ∀ v ∈ localization₂ P.asIdeal N, y v ∈ localization₂ P.asIdeal N' := by
  first | exact @GlobalTheory.MomT.LatFin.per_lattice_facts | exact GlobalTheory.MomT.LatFin.per_lattice_facts | (intros; apply GlobalTheory.MomT.LatFin.per_lattice_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TilLatticesOfLevel
noncomputable section

namespace GlobalTheory.TilClass

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open GlobalTheory.TopStep (sumE prH extI redGL)

section Points

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} (hN : N = n + 1)
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

variable (hconj : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
  (hbig : 2 ^ Module.finrank ℚ E < ∏ P ∈ ST, Ideal.absNorm P.asIdeal) {pi : 𝓞 E}
  (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
include hconj hbig hT hG

end Points

section Size

variable {X : Fields} {Pr : Primes X}

end Size

section Branch

theorem isBlock_of_mulVec {E : Type} [Field E] {N n : ℕ} (hN : N = n + 1) {A' : Matrix (Fin N) (Fin N) E}
    {A : Matrix (Fin n) (Fin n) E} (h1 : ∀ x, iniH hN (A'.mulVec x) = A.mulVec (iniH hN x))
    (h2 : ∀ x, A'.mulVec x (Br.iL hN) = x (Br.iL hN)) : BranchFormula.IsBlock hN A' A 1 := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  have hinj : Function.Injective (Br.iC hN) := fun a b h => Fin.ext (congrArg Fin.val h :)
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have h := congrFun (h1 (Pi.single (Br.iC hN b) 1)) a
    have e : iniH hN (Pi.single (Br.iC hN b) (1 : E)) = Pi.single b 1 := funext fun i => by
      simp only [iniH, Pi.single_apply, hinj.eq_iff]
    rw [e, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at h
    exact h
  · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
    have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
    rw [e, Matrix.mulVec_single_one, Matrix.mulVec_zero] at h
    exact h
  · have h := h2 (Pi.single (Br.iC hN a) 1)
    rw [Matrix.mulVec_single_one, Pi.single_eq_of_ne (hne a).symm] at h
    exact h
  · have h := h2 (Pi.single (Br.iL hN) 1)
    rw [Matrix.mulVec_single_one, Pi.single_eq_same] at h
    exact h

theorem brStd_rhoVr {E K ι : Type} [Field E] [Field K] [CharZero K] [Fintype ι] {N n : ℕ} (hN : N = n + 1) (e : ι → E →+* K)
    {lam : ι → DomWeight N} {sg : ι → DomWeight n} (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ))
    (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) {γ' : GL (Fin N) E} {γ : GL (Fin n) E}
    (h : BranchFormula.IsBlock hN ((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
      ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) 1) (G : VV K lam) :
    Br.brStd hN lam sg (rhoVr e lam γ' G) = rhoVr e sg γ (Br.brStd hN lam sg G) := by
  refine BranchFormula.equivariance K ι N n hN lam sg hI hS (invTrK (embGL e γ)) (invTrK (embGL e γ')) (fun τ => ?_) G
  have e1 : ∀ {m : ℕ} (g : GL (Fin m) E) (a b : Fin m), ((invTrK (embGL e g) τ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) a b =
      e τ (((g⁻¹ : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) b a) := fun g a b => rfl
  simp only [e1]
  refine ⟨fun a b => by rw [h.1], fun a => ⟨by rw [(h.2.1 a).2, map_zero], by rw [(h.2.1 a).1, map_zero]⟩, by rw [h.2.2, map_one]⟩

variable {E K ι : Type} [Field E] [Field K] [Fintype ι] (emb : ι → E →+* K) (σ : K →+* ℂ) {n : ℕ} (lam : ι → DomWeight n)

theorem mem_ValC_iff (f : Fr emb σ n → ℂ) :
    f ∈ ValC (Gr emb σ n) lam ↔ ∃ F : VV ℂ lam, fnOf (Gr emb σ n) (shiftOf lam) 1 F.1 = f := by
  have e : ∀ F : VV ℂ lam, evV (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ) F =
      fnOf (Gr emb σ n) (shiftOf lam) 1 F.1 := fun F => by
    rw [evV_apply, MvPolynomial.map_id]
    rfl
  constructor
  · intro hf
    have h : f ∈ Submodule.span ℂ (Set.range (evV (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ))) := by
      rw [span_evV]
      exact hf
    rw [← LinearMap.coe_range, Submodule.span_eq] at h
    obtain ⟨F, rfl⟩ := h
    exact ⟨F, (e F).symm⟩
  · rintro ⟨F, rfl⟩
    rw [← e]
    exact evV_mem_ValC _ _ _ _ F

theorem trFr_fnOf (γ : GL (Fin n) E) (c : Kˣ) (F : VV ℂ lam) :
    trFr emb σ γ c (fnOf (Gr emb σ n) (shiftOf lam) 1 F.1) =
      σ c • fnOf (Gr emb σ n) (shiftOf lam) 1 (rhoVr (embAt σ emb) lam γ F).1 := by
  funext y
  rw [trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  have h := evV_rhoVr_tr (embAt σ emb) (1 : Matrix (Fin n) (Fin n) E) lam (RingHom.id ℂ) γ F y (frMul emb σ γ⁻¹ y) fun τ =>
    (congrFun (congrArg Subtype.val ((frEquiv emb σ γ).apply_symm_apply y)) τ).symm
  rw [evV_apply, evV_apply, MvPolynomial.map_id, MvPolynomial.map_id] at h
  exact h.symm

theorem polOf_fnOf_one (sh : ι → ℤ) (F : Pol ℂ ι n) :
    polOf (Gr emb σ n) sh (fr0 emb σ n) (fnOf (Gr emb σ n) sh 1 F) = F := by
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  have h := polOf_fnOf (Gr emb σ n) sh (fr0 emb σ n) F
  rwa [e] at h

end Branch

section Period

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (Q : PerIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R)

variable {Q}

end Period

section Levels

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) {N n : ℕ} (hN : N = n + 1)
  {Q : Finset (HeightOneSpectrum (𝓞 X.E))} (hQ : ∀ P : Q, Pr.piT u ∉ P.1.asIdeal)
  {Λ : LevFam X.E X.K N Pr.vGs} {Θ : LevQFam X.E X.K N Q} {Λ' : LevFam X.E X.K n Pr.vGs} {Θ' : LevQFam X.E X.K n Q}
include hX hPr hQ

variable (hΛ : ∀ h, extGH hN h ∈ Λ.grp ↔ h ∈ Λ'.grp) (hΘ : ∀ c, extQ X.E hN Q c ∈ Θ.grp ↔ c ∈ Θ'.grp)
include hΛ hΘ

end Levels

section Lattices

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

variable (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word)
  (rho : ∀ i (b : Idx sel mu L i), (stepAt sel mu cst L Tp u i).D b → ℂ)
  (rho' : ∀ i (b : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u (i + 1)).D b → ℂ) (cD : X.Tau → ℂ)
  (Th : ∀ i (b : Idx sel mu L i) (b' : Idx sel mu L (i + 1)), (stepAt sel mu cst L Tp u i).D b →
    (stepAt sel mu cst L Tp u (i + 1)).D b' → Formalism.L2.Ker.VCx X.Tau (R.N i) (R.N (i + 1)) → ℂ)

variable {W Ch sel mu cst L P Tp u rho rho' cD Th} {Q : PerIn (chainAt sel mu cst L Tp u rho rho' cD Th)}

end Lattices

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (P : LevFam X.E X.K R.r Pr.vGs)

end Main

section Top

open GlobalTheory.TopStep (TilOk tilTop tilEl topLevG topLevQ topGSD evTop TopDepth inQ)

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {P : LevFam X.E X.K R.r Pr.vGs} {u : Pr.Word}

theorem brC_rho (hW : W.Ok) (γ : UF X.E (R.N R.m - 1)) (x : VV X.K (W.lamTrue u R.m)) :
    brC W u (rhoVr X.emb (W.lamTrue u R.m) (ufGL X.E _ (extUH (N_m_succ R) γ)) x) =
      rhoVr X.emb W.sgTrue (ufGL X.E _ γ) (brC W u x) := by
  have h := brStd_rhoVr (N_m_succ R) X.emb (fun τ => (BranchMembers.members X _ R W hW u τ).1)
    (fun τ => (BranchMembers.members X _ R W hW u τ).2) (γ' := ufGL X.E _ (extUH (N_m_succ R) γ)) (γ := ufGL X.E _ γ) (by
      have e : ∀ y, ((ufGL X.E _ (extUH (N_m_succ R) γ⁻¹) : GL _ _) : Matrix _ _ X.E).mulVec y =
          sumE (N_m_succ R) (γ⁻¹).1 1 y := fun y => by
        rw [← TopStep.extUH_val]
        exact toGLm_mulVec _ y
      rw [← map_inv, ← map_inv, ← map_inv]
      refine isBlock_of_mulVec _ (fun y => ?_) fun y => ?_
      · rw [e]
        exact (TopStep.prH_sumE _ _ _ y).trans (toGLm_mulVec _ _).symm
      · rw [e, TopStep.sumE_last, Units.val_one, one_mul]) x
  rw [brC, Br.brAt, LinearMap.smul_apply, LinearMap.smul_apply, h, map_smul]

end Top

end GlobalTheory.TilClass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InterTransport
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.Transport

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem opU_comp (e : V ≃ₗ[ℂ] V') {H : Sesq V} {H' : Sesq V'} (hH : ∀ x y, H' (e x) (e y) = H x y)
    (F : V' → ℂ) (x z : V) : opU H x (fun w => F (e w)) z = opU H' (e x) F (e z) := by
  simp only [opU, hH, map_add (f := _)]

def subEquiv (e : V ≃ₗ[ℂ] V') {Λ : AddSubgroup V} {Λ' : AddSubgroup V'} (h : ∀ x, x ∈ Λ ↔ e x ∈ Λ') : Λ ≃+ Λ' where
  toFun x := ⟨e x, (h _).1 x.2⟩
  invFun y := ⟨e.symm y, (h _).2 (by simp)⟩
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

def quotEquiv (e : V ≃ₗ[ℂ] V') {Λ₁ Λ₂ : AddSubgroup V} {Λ₁' Λ₂' : AddSubgroup V'} (h₁ : ∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁')
    (h₂ : ∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') : (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≃+ (Λ₂' ⧸ Λ₁'.addSubgroupOf Λ₂') :=
  QuotientAddGroup.congr _ _ (subEquiv e h₂) (by
    ext y
    obtain ⟨x, rfl⟩ := (subEquiv e h₂).surjective y
    exact (AddSubgroup.mem_map_iff_mem (f := (subEquiv e h₂ : Λ₂ →+ Λ₂')) (subEquiv e h₂).injective).trans (h₁ _))

theorem term_add {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hd : IsSelfDual H A₂)
    (hs : IsSemiChar H A₂ α) {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) {a s : V} (ha : a ∈ A₂) (hs₂ : s ∈ A₂)
    (hs₁ : s ∈ A₁) (z : V) : α (a + s) * opU H (a + s) F z = α a * opU H a F z := by
  rw [GlobalTheory.ThetaInter.alpha_opU_add hH hd hs ha hs₂, ← GlobalTheory.ThetaInter.opU_mul]
  congr 2
  funext w
  exact hF s hs₁ w

theorem inter_transport : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (e : V ≃ₗ[ℂ] V') (H : Sesq V) (H' : Sesq V') (α : V → ℂ) (α' : V' → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (Λ₁' Λ₂' : AddSubgroup V') (θ' : V' → ℂ), (∀ x y, H' (e x) (e y) = H x y) → (∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁') → (∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') → (∀ x ∈ Λ₂, α x = α' (e x)) → IsHerm H' → IsSelfDual H' Λ₂' → IsSemiChar H' Λ₂' α' → (IsSelfDual H Λ₂ ∧ IsSemiChar H Λ₂ α ∧ ∀ F' ∈ fixedBy H' α' Λ₂', (fun z => F' (e z)) ∈ fixedBy H α Λ₂) ∧ (θ' ∈ fixedBy H' α' Λ₁' → relIdx Λ₁' Λ₂' ≠ 0 → inter H α Λ₁ Λ₂ (fun z => θ' (e z)) = fun z => inter H' α' Λ₁' Λ₂' θ' (e z)) := by
  intro V V' _ _ _ _ e H H' α α' Λ₁ Λ₂ Λ₁' Λ₂' θ' hH h₁ h₂ hα hh hd hs
  have hE : ∀ x y, altE H x y = altE H' (e x) (e y) := fun x y => by simp only [altE, hH]
  refine ⟨⟨?_, ⟨fun x hx => ?_, fun x hx y hy => ?_⟩, fun F hF x hx z => ?_⟩, fun hθ _ => ?_⟩
  · ext x
    rw [h₂ x]
    conv_rhs => rw [← hd]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← hE]
      exact h y ((h₂ y).2 hy)
    · intro h y hy
      rw [hE]
      exact h _ ((h₂ y).1 hy)
  · rw [hα x hx]; exact hs.1 _ ((h₂ x).1 hx)
  · rw [hα _ (Λ₂.add_mem hx hy), hα x hx, hα y hy, map_add (f := _), hE]
    exact hs.2 _ ((h₂ x).1 hx) _ ((h₂ y).1 hy)
  · rw [opU_comp e hH, hα x hx]
    exact hF _ ((h₂ x).1 hx) _
  · funext z
    have hc : relIdx Λ₁ Λ₂ = relIdx Λ₁' Λ₂' := Nat.card_congr (quotEquiv e h₁ h₂).toEquiv
    rw [inter, inter, hc, ← finsum_comp_equiv (quotEquiv e h₁ h₂).toEquiv]
    congr 1
    refine finsum_congr fun c => ?_
    rw [opU_comp e hH, hα _ (Quotient.out c).2]
    have hm : -(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c) ∈
        Λ₁'.addSubgroupOf Λ₂' := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
      conv_rhs => rw [← QuotientAddGroup.out_eq' c]
      rfl
    have := term_add hh hd hs hθ (subEquiv e h₂ (Quotient.out c)).2
      (-(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c)).2
      (AddSubgroup.mem_addSubgroupOf.1 hm) (e z)
    rw [← AddSubgroup.coe_add, add_neg_cancel_left] at this
    exact this.symm

end GlobalTheory.ThetaMove.Transport
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.SeamMoves

variable {X : Fields} {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
  (cD : D.what₂.Tau → ℂ)

def reidx (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] TaylorLogMetric.VC D a b := LinearEquiv.funCongrLeft ℂ (Fin b → Fin a → ℂ) s.iT.symm

theorem form_reidx (A : ℝ) (a b : ℕ) (x y : VCx X.Tau a b) :
    formV A D.what₂.Tau a b (reidx s a b x) (reidx s a b y) = Formalism.L2.Ker.HV A⁻¹ x y := by
  change (∑ τ, ∑ i, ∑ j, x (s.iT.symm τ) i j * (starRingEnd ℂ) (y (s.iT.symm τ) i j)) / (A : ℂ) =
    ((A⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT.symm (fun τ => ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)), Complex.ofReal_inv, div_eq_inv_mul]

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (a b : ℕ) : IsHerm (formV A n a b) := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [formV, map_sum, mul_comm]

theorem iop_eq {a b : ℕ} (Λ₁ Λ₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D B.tor Λ₁ Λ₂ G = inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) Λ₁ Λ₂ G := rfl

theorem alV_eq {a b : ℕ} (x : VCx X.Tau a b) {m : ℤ}
    (hm : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x)).re = (m : ℝ)) :
    alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x = TaylorLogMetric.al D B.tor (reidx s a b x) := by
  have h1 : TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x) = Formalism.L2.Ker.HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x x :=
    form_reidx s _ a b x x
  unfold TaylorLogMetric.al
  rw [hm, round_intCast]
  rw [h1] at hm
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [hm, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

include B in
theorem delta_ne_zero : δ ≠ 0 := by
  rintro rfl
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  have h2 : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨c, -, rfl⟩
    simp
  rw [B.lat] at h1
  have h3 : B.L.ω₁ = 0 := AddSubgroup.mem_bot.1 (h2 h1)
  exact B.L.indep.ne_zero 0 h3

theorem aa_ne_bot (hcc : cc ≠ ⊥) : (ambOf s B χ cD).AA ≠ ⊥ := by
  intro h
  have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
    refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
    simp
  rw [h, Submodule.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
  exact hcc h1

theorem aa_fg : (ambOf s B χ cD).AA.FG := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  obtain ⟨z, hz, hden⟩ := D.host.AA0.isFractional
  have hz0 : j z ≠ 0 := fun h => nonZeroDivisors.ne_zero hz (by
    have h1 := hj z
    rw [h] at h1
    have h2 : (z : D.host.E) = 0 := s.iE.symm.injective (by rw [← h1]; simp)
    exact RingOfIntegers.coe_injective (by simpa using h2))
  have hfr : IsFractional (nonZeroDivisors (𝓞 X.E)) (ambOf s B χ cD).AA := by
    refine (FractionalIdeal.isFractional_span_iff).2 ⟨j z, mem_nonZeroDivisors_of_ne_zero hz0, ?_⟩
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    have hw' : (w : D.host.E) = (z : D.host.E) * t := by rw [Algebra.smul_def] at hw; exact hw
    rw [e, hw']
    ring
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨_, hfr⟩

theorem vac_eq {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (h : Base.chiFac χ a b (s.lat N) (s.lat N') ≠ 0) :
    vac (ambOf s B χ cD) N N' = fun z => B.thMoved a b (s.lat N) (s.lat N') (reidx s a b z) := by
  funext z
  exact inv_mul_cancel_left₀ h _

theorem moves_ambOf : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → Moves (ambOf s B χ cD) a b := by
  intro X D s cc δ B χ cD a b hX hs hcc hχ hE hL hZ ha hb
  obtain ⟨hsd, hlam⟩ := GlobalTheory.T.fieldIso_selfDual_and_periodLattices_agree X D s cc δ B χ cD hs
  obtain ⟨hth, hm1, hm2⟩ := GlobalTheory.T.movedVacuum_mem_thetaFunctions_and_moves D cc δ B χ a b hχ hE hL hZ ha hb
  have hq := GlobalTheory.T.quadraticForm_integral_of_selfDual_periodLattices D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  have key := fun (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) (h : IsSdLat N₂)
      (h' : IsSdLat N₂') (θ : TaylorLogMetric.VC D a b → ℂ) =>
    Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N₁ N₁') (lam (ambOf s B χ cD) N₂ N₂') (TaylorLogMetric.La D B.tor (s.lat N₁) (s.lat N₁'))
      (TaylorLogMetric.La D B.tor (s.lat N₂) (s.lat N₂')) θ (form_reidx s _ a b) (hlam a b N₁ N₁') (hlam a b N₂ N₂')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N₂ N₂' h h') (reidx s a b x) ((hlam a b N₂ N₂' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N₂ N₂' h h')).1 (hL.1 a b _ _ (hadm N₂ N₂' h h')).2
  refine ⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, aa_fg s B χ cD, aa_ne_bot s B χ cD hcc.1, ?_, ?_, ?_⟩
  · intro N N' h h'
    obtain ⟨hc, han, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    obtain ⟨h1, h2, h3⟩ := (key N N N' N' h h' 0).1
    refine ⟨hc, ?_, h1, h2⟩
    rw [vac_eq s B χ cD N N' hc]
    refine ⟨fun z _ => ?_, h3 _ hfix⟩
    exact (han _ (Set.mem_univ _)).comp ((reidx s a b).toLinearMap.toContinuousLinearMap.analyticAt z)
  · intro N N' N'' h h' h''
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N N'' (hth _ _ (hsd _ _ h) (hsd _ _ h'')).1,
      (key N N N' N'' h h'' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N N'' h h'')).1,
      hm1 _ _ _ (hsd _ _ h) (hsd _ _ h') (hsd _ _ h''), iop_eq]
  · intro N N₁ N' h h₁ h'
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N₁ N' (hth _ _ (hsd _ _ h₁) (hsd _ _ h')).1,
      (key N N₁ N' N' h₁ h' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N₁ N' h₁ h')).1,
      hm2 _ _ _ (hsd _ _ h) (hsd _ _ h₁) (hsd _ _ h'), iop_eq]

end GlobalTheory.ThetaMove.SeamMoves
end
end
