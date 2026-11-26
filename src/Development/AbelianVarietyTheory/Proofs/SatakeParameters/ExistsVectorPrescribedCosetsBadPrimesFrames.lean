module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFrames
noncomputable section

namespace GlobalTheory.CosetApprox

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Gen

variable {E : Type} [Field E] [NumberField E]

theorem intAt_of_valuation_le (P : HeightOneSpectrum (𝓞 E)) (x : E) (h : P.valuation E x ≤ 1) :
    Formalism.L2.Col.IntAt P x := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x h
  exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

theorem apply_eq_sum {n : ℕ} (g : (Fin n → E) →ₗ[E] (Fin n → E)) (w : Fin n → E) (l : Fin n) :
    g w l = ∑ k, w k * g (Pi.single k 1) l := by
  conv_lhs => rw [LinearMap.pi_apply_eq_sum_univ g w]
  rw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  rw [show (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 by funext j; simp [Pi.single_apply, eq_comm]]

theorem exists_approx (T : Finset (HeightOneSpectrum (𝓞 E))) {n : ℕ} (g : T → (Fin n → E) →ₗ[E] (Fin n → E))
    (c : T → E) (t : T → Fin n → E) :
    ∃ d : Fin n → E, ∀ P : T, ∀ l, (P.1).valuation E (c P * g P (d - t P) l) ≤ 1 := by
  classical
  have hb : ∀ P : T, ∃ b : WithZero (Multiplicative ℤ), 1 ≤ b ∧
      ∀ l k, (P.1).valuation E (c P * g P (Pi.single k 1) l) ≤ b := by
    intro P
    obtain ⟨b, hb⟩ := (Set.finite_range fun lk : Fin n × Fin n =>
      (P.1).valuation E (c P * g P (Pi.single lk.2 1) lk.1)).bddAbove
    exact ⟨max b 1, le_max_right _ _, fun l k => (hb ⟨(l, k), rfl⟩).trans (le_max_left _ _)⟩
  choose B hB1 hBle using hb
  have hB0 : ∀ P, B P ≠ 0 := fun P => (lt_of_lt_of_le zero_lt_one (hB1 P)).ne'
  have hk : ∀ k : Fin n, ∃ a : E, ∀ P : T, (P.1).valuation E (a - t P k) < (B P)⁻¹ := by
    intro k
    obtain ⟨a, -, ha, -⟩ := PI.FinOrdValD.WA.weakApprox T
      (fun v => if h : v ∈ T then algebraMap E (v.adicCompletion E) (t ⟨v, h⟩ k) else 0)
      (fun v => if h : v ∈ T then (B ⟨v, h⟩)⁻¹ else 1)
      (fun v hv => by simp only [dif_pos hv]; exact inv_ne_zero (hB0 _))
    refine ⟨a, fun P => ?_⟩
    have h := ha P.1 P.2
    simp only [dif_pos P.2, Subtype.coe_eta] at h
    rw [← map_sub, PI.FinOrdValD.WA.val_alg] at h
    exact h
  choose a ha using hk
  refine ⟨a, fun P l => ?_⟩
  rw [apply_eq_sum, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [show c P * ((a - t P) k * g P (Pi.single k 1) l) = (a - t P) k * (c P * g P (Pi.single k 1) l) by ring,
    map_mul, Pi.sub_apply]
  calc (P.1).valuation E (a k - t P k) * (P.1).valuation E (c P * g P (Pi.single k 1) l)
      ≤ (B P)⁻¹ * B P := mul_le_mul' (ha k P).le (hBle P l k)
    _ = 1 := inv_mul_cancel₀ (hB0 P)

end Gen

open NumberField IsDedekindDomain Matrix _root_.Formalism.BasicNotions _root_.Formalism.UG _root_.Formalism.L2.Col _root_.Formalism.L2.PairingIndexBounds.F _root_.Formalism.MainNotions.G.KAat _root_.Formalism.L2.Forms _root_.Formalism.L2.Ker _root_.Formalism.MainNotions _root_.Formalism.L2.DIV _root_.Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV

theorem exists_sameCoset {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n))
    (y0 : rowSG Pr sel mu → Sp X.E n) :
    ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  classical
  obtain ⟨d, hd⟩ := exists_approx (rowSG Pr sel mu) (fun P => ((f P).symm : Sp X.E n →ₗ[X.E] Sp X.E n))
    (fun P => (((qOf P.1 : ℕ) : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹) (fun P => f P (y0 P))
  refine ⟨d, fun P l => intAt_of_valuation_le _ _ ?_⟩
  have h := hd P l
  have e : (f P).symm d - y0 P = (f P).symm (d - f P (y0 P)) := by
    rw [map_sub, LinearEquiv.symm_apply_apply]
  rw [e]
  exact h

end GlobalTheory.CosetApprox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFramesStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu)) {n : ℕ} (f : rowSG Pr sel mu → (Sp X.E n ≃ₗ[X.E] Sp X.E n)) (y0 : rowSG Pr sel mu → Sp X.E n),
  ∃ y : Sp X.E n, ∀ P, SameCoset sel mu cst P ((f P).symm y) (y0 P) := by
  first | exact @GlobalTheory.CosetApprox.exists_sameCoset | exact GlobalTheory.CosetApprox.exists_sameCoset | (intros; apply GlobalTheory.CosetApprox.exists_sameCoset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrincipalCongruenceInDefiniteLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrincipalCongruenceInDefiniteLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VFormCong

theorem redFn_eq_one_of_finCong {D : D7} {V : TH.HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {N : ℕ} {k : GA D V}
    (hΛ : IsSDFrame V β Λ 1) (hN : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal)
    (hk : GlobalTheory.Member.FinCong V N k) :
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP (Lev.finE V k) = 1 := by
  have hfr : Formalism.L2.DIV.IsFrame β Λ := by obtain ⟨c, h, -⟩ := hΛ; exact h
  have hl : Formalism.L2.Pj.latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hΛ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  have hc : ∀ a : GA D V, GlobalTheory.Member.FinCong V N a → ∀ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ,
      ∃ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, (Lev.finE V a).1 *ᵥ z - z = N • y := by
    intro a ha
    unfold GlobalTheory.Member.FinCong at ha
    rw [hl] at ha
    exact GlobalTheory.PrincInLevel.cong_swap Λ N _ ha
  have hc' := hc _ (GlobalTheory.Member.PrincLevel.finCong_inv hk)
  rw [map_inv] at hc'
  obtain ⟨y, hy, hred⟩ := GlobalTheory.PrincInLevel.exists_int (Formalism.L2.Herm.intAf D.host.F D.host.E) β (Lev.finE V k)
    (Formalism.L2.Herm.hatL (F := D.host.F) Λ) N hfr (hc k hk) hc'
  have hy' : Formalism.L2.DIV.frGL β y = Lev.finE V k := hy
  intro PP hP
  rw [← hy', Formalism.L2.DIV.redFn_frGL]
  refine hred _ _ ?_
  rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hN PP hP)

theorem levFn_eq_one {D : D7} {n : ℕ} (β : GL (Fin n) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ n)
    (x : GL (Fin n) (Lev.EAf D)) (h3 : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → Formalism.L2.DIV.redFn β PP x = 1) :
    Formalism.L2.DIV.levFn β L x = 1 := by
  have e : Formalism.L2.DIV.levFn β L x = Formalism.L2.DIV.levFn β L 1 := by
    have hr : Formalism.L2.DIV.rTup β L x = Formalism.L2.DIV.rTup β L 1 := by
      funext PP
      show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP.1 x) = Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP.1 1)
      rw [h3 PP.1 (Or.inl PP.2), Formalism.L2.DIV.redFn_one]
    unfold Formalism.L2.DIV.levFn
    rw [hr]
    congr 1
    · congr 1
      exact Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => by
        rw [h3 PP (Or.inl hPP), Formalism.L2.DIV.redFn_one]
    · exact Finset.prod_congr rfl fun PP hPP => by
        rw [h3 PP (Or.inr hPP), Formalism.L2.DIV.redFn_one]
  rw [e]
  exact (Formalism.L2.DIV.levChar D.sp.cm (1 : Matrix (Fin n) (Fin n) D.host.E) β L).map_one

end GlobalTheory.VFormCong


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.VFormCong.exists_cong_levEnv : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J, (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, h⟩ = 1 := by
  intro D cf nch tp X M rep hA j t
  classical
  obtain ⟨N, hN0, hNmem⟩ : ∃ N : ℕ, 0 < N ∧ ∀ PP, PP ∈ (X.R.datVt j t).Pg ∨ PP ∈ (X.R.datVt j t).Q →
      ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    refine ⟨∏ PP ∈ (X.R.datVt j t).Pg ∪ (X.R.datVt j t).Q, Ideal.absNorm PP.asIdeal, Finset.prod_pos fun PP _ =>
      Nat.pos_of_ne_zero fun h => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun PP hPP => ?_⟩
    obtain ⟨u, hu⟩ := Finset.dvd_prod_of_mem (fun PP => Ideal.absNorm (IsDedekindDomain.HeightOneSpectrum.asIdeal PP))
      (Finset.mem_union.2 hPP)
    rw [hu, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
  obtain ⟨N', hN', hcong⟩ :=
    GlobalTheory.StdFrameCong.exists_cong_finCong D (Vc D j) D.R.nV (hA.PV j) hA.hF (hA.stdV j) N hN0
  refine ⟨N', hN', fun κ hκ => ?_⟩
  have hk := hcong κ hκ
  have hβ := X.given.core.lev.βV j
  refine ⟨GlobalTheory.PrincInLevel.finCong_mem_levEnv D (Vc D j) (X.R.βV j) (X.R.ΛV j) (X.R.datVt j t) N _ hβ hNmem hk, ?_⟩
  apply Units.ext
  change ((Formalism.L2.DIV.levFn (X.R.βV j) (Lev.flag1L (X.R.datVt j t)) (Lev.finE (Vc D j) ((hA.PV j).ψ κ)) : ℂˣ) : ℂ) = 1
  rw [GlobalTheory.VFormCong.levFn_eq_one (X.R.βV j) (Lev.flag1L (X.R.datVt j t)) _
    (fun PP hP => GlobalTheory.VFormCong.redFn_eq_one_of_finCong (X.R.datVt j t) hβ hNmem hk PP hP)]
  rfl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPrincipalCongruenceInDefiniteLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Theta
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalCongruence_in_definiteLevel : ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hA : GlobalTheory.NJoin.Agree X M rep) (j : Fin D.R.m) (t : X.T), ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : (finHom (Vc D j)).rangeRestrict ((hA.PV j).ψ κ) ∈ (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).J, (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j t)).χ ⟨_, h⟩ = 1 := by
  first | exact @GlobalTheory.VFormCong.exists_cong_levEnv | exact GlobalTheory.VFormCong.exists_cong_levEnv | (intros; apply GlobalTheory.VFormCong.exists_cong_levEnv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwist
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) {w : Pr.Word}


open Classical in
theorem cplCoset_frsF_mem {j : ℕ} (p : ChPt (R := R) sel mu w j) (P : rowSG Pr sel mu) (x : Sp X.E (R.N j)) :
    frsF sel mu p P x ∈ p.deco.1.at P.1 ↔ x ∈ stdAt X.E (R.N j) P.1 := by
  unfold frsF
  split_ifs with h
  · have h1 : p.deco.1.HasLift ⟨P.1, h⟩ := Deco.Ok.hasLift p.deco.2 ⟨P.1, h⟩
    exact (Deco.liftFr_spec h1).1 x
  · exact Subtype.property p ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x

theorem cplCoset_sameCoset_of_common {cst : LocCst X (rowSG Pr sel mu)} {n : ℕ} {P : rowSG Pr sel mu} {x y z : Sp X.E n}
    (h : SameCoset sel mu cst P x z) (h' : SameCoset sel mu cst P y z) : SameCoset sel mu cst P x y := fun l => by
  have h1 := (h l).add (ciIntAt_neg (h' l))
  rwa [← mul_neg, ← Pi.neg_apply, ← mul_add, ← Pi.add_apply, neg_sub, sub_add_sub_cancel] at h1

end Gen

end GlobalTheory.TwV

namespace GlobalTheory.TwV

theorem cplCoset_bound : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ)
  (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
  (P.1 ∈ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y l)) ∧
  (P.1 ∉ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y l))) := by
  classical
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hP H hi β P y hy
  obtain ⟨⟨c, rfl⟩, -⟩ := ((St (t.m2 + 1) hi).K β).y_bij.2 (Quotient.mk'' 1)
  obtain ⟨y1, hy1, hY⟩ := H.chain.2.1 c
  have hmem : y1 ∈ A.yb c := by rw [hY]; simp
  have h0 := H.coset c y1 hmem P
  have hy' : SameCoset t.sel (t.tup μ) (t.cst μ) P y (A.y0 ((St _ (cpl_lt t μ).le).chOf c) P) := by
    unfold y0At at hy
    rwa [dite_eq_left rfl] at hy
  have hyw := cplCoset_sameCoset_of_common t.sel (t.tup μ) hy' h0
  set p := A.pt (t.m2 + 1) (cpl_lt t μ).le c with hp
  set w := (frsF t.sel (t.tup μ) p P).symm y1 with hw
  have hq0 : (qOf P.1 : t.X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, qOf, Ne, Ideal.absNorm_eq_zero_iff]
    exact P.1.ne_bot
  have hloc := (mem_locLat _ _ _ _).1 hy1 P
  have hw1 : ∀ l, IntAt P.1 ((((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then (-1 : ℤ) else -((t.cst μ).M : ℤ)))⁻¹) * w l) := by
    have h2 : frsF t.sel (t.tup μ) p P ((((qOf P.1 : t.X.E) ^ (if P.1 ∈ t.Pr.vGs then (-1 : ℤ) else -((t.cst μ).M : ℤ)))⁻¹) • w) ∈ p.deco.1.at P.1 := by
      rw [map_smul, hw, LinearEquiv.apply_symm_apply]
      exact hloc
    have h3 := (ciMem_stdAt _ _).1 ((cplCoset_frsF_mem t.sel (t.tup μ) p P _).1 h2)
    intro l
    simpa using h3 l
  refine ⟨fun hG l => ?_, fun hG l => ?_⟩
  · have h1 := hw1 l
    have h2 := hyw l
    simp only [hG, if_true, pow_zero, inv_one, one_mul, _root_.zpow_neg, zpow_one, inv_inv, Pi.sub_apply] at h1 h2
    have e : (qOf P.1 : t.X.E) * y l = (qOf P.1 : t.X.E) * (y l - w l) + (qOf P.1 : t.X.E) * w l := by ring
    rw [e]
    exact (ciIntAt_q.mul h2).add h1
  · have h1 := hw1 l
    have h2 := hyw l
    simp only [hG, if_false, _root_.zpow_neg, zpow_natCast, inv_inv, Pi.sub_apply] at h1 h2
    have hqM : IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M) := by
      have := IntAt.coe P.1 (((qOf P.1 ^ (t.cst μ).M : ℕ)) : 𝓞 t.X.E)
      rwa [map_natCast, Nat.cast_pow] at this
    have e : (qOf P.1 : t.X.E) ^ (t.cst μ).M * y l = (qOf P.1 : t.X.E) ^ (t.cst μ).M * (qOf P.1 : t.X.E) ^ (t.cst μ).M *
        (((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ * (y l - w l)) + (qOf P.1 : t.X.E) ^ (t.cst μ).M * w l := by
      field_simp
      ring
    rw [e]
    exact ((hqM.mul hqM).mul h2).add h1

end GlobalTheory.TwV
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwistStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ)
  (y : Sp t.X.E (D.R.N (t.m2 + 1))), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
  (P.1 ∈ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) * y l)) ∧
  (P.1 ∉ t.Pr.vGs → ∀ l, IntAt P.1 ((qOf P.1 : t.X.E) ^ (t.cst μ).M * y l))) := by
  first | exact @GlobalTheory.TwV.cplCoset_bound | exact GlobalTheory.TwV.cplCoset_bound | (intros; apply GlobalTheory.TwV.cplCoset_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarOnIsotypicPart
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarOnIsotypicPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RtSumScalar

section Main

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem rtSum_iso {ρ : Representation ℂ (GQ L n) W} {S S' : Submodule ℂ (GAf L n → W)} (hS : NG.IsSubrep ρ S)
    (hiso : NG.IsoRep S S') (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f)
    (f' : GAf L n → W) (hf' : f' ∈ S') (hfix : ∀ κ ∈ K, NG.rt L n κ f' = f') :
    ∑ γ ∈ R, NG.rt L n γ f' = c • f' := by
  classical
  obtain ⟨T, hT⟩ := hiso
  set f : S := T.symm ⟨f', hf'⟩ with hfdef
  have hTf : T f = ⟨f', hf'⟩ := T.apply_symm_apply _
  have hrt : ∀ h : GAf L n, ((T ⟨NG.rt L n h f, hS.stable h _ f.2⟩ : S') : GAf L n → W) = NG.rt L n h f' := by
    intro h
    have := hT h f ⟨_, hS.stable h _ f.2⟩ rfl
    rw [this, hTf]
  have hffix : ∀ κ ∈ K, NG.rt L n κ (f : GAf L n → W) = f := by
    intro κ hκ
    have h1 := hrt κ
    rw [hfix κ hκ] at h1
    have h2 : T ⟨_, hS.stable κ _ f.2⟩ = T f := Subtype.ext (by rw [h1, hTf])
    exact congrArg Subtype.val (T.injective h2)
  have hcf := hc f f.2 hffix
  let σ : S := ∑ γ ∈ R, (⟨NG.rt L n γ f, hS.stable _ _ f.2⟩ : S)
  have hσ : (σ : GAf L n → W) = ∑ γ ∈ R, NG.rt L n γ f := by
    rw [Submodule.coe_sum]
  have hTσ : ((T σ : S') : GAf L n → W) = ∑ γ ∈ R, NG.rt L n γ f' := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun γ _ => hrt γ
  have key : σ = c • f := Subtype.ext (by rw [hσ, Submodule.coe_smul]; exact hcf)
  have h3 := congrArg (fun y => ((T y : S') : GAf L n → W)) key
  simp only [map_smul, Submodule.coe_smul, hTσ, hTf] at h3
  exact h3

theorem rtSum_finset_sum {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S)
    (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ)
    (hc : ∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f)
    (t : Finset (Submodule ℂ (GAf L n → W))) :
    (↑t ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'}) → ∀ f ∈ (⨆ i ∈ t, i),
      (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    intro _ f hf _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hf
    subst hf
    simp
  | insert a t ha ih =>
    intro hsub f hf hfix
    have haF : NG.IsIrrRep ρ a ∧ NG.IsoRep S a := hsub (Finset.mem_insert_self a t)
    have htF : (↑t : Set _) ⊆ {S' | NG.IsIrrRep ρ S' ∧ NG.IsoRep S S'} :=
      fun x hx => hsub (Finset.mem_insert_of_mem hx)
    rw [Finset.iSup_insert] at hf
    have hMst : ∀ h, ∀ g ∈ (⨆ i ∈ t, i), NG.rt L n h g ∈ (⨆ i ∈ t, i) :=
      GlobalTheory.HeckeScalarAll.iSup_finset_stable' t (fun i hi => (htF hi).1.1.stable)
    have hsubrep : NG.IsSubrep ρ (a ⊓ ⨆ i ∈ t, i) :=
      ⟨inf_le_left.trans haF.1.1.le, fun h g hg => ⟨haF.1.1.stable h g hg.1, hMst h g hg.2⟩⟩
    rcases haF.1.2.2 _ hsubrep inf_le_left with h0 | htop
    · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hf
      have hyfix : ∀ κ ∈ K, NG.rt L n κ y = y := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _)] at e
        have hd : NG.rt L n κ y - y ∈ a ⊓ ⨆ i ∈ t, i := by
          refine ⟨Submodule.sub_mem _ (haF.1.1.stable κ y hy) hy, ?_⟩
          have h4 : NG.rt L n κ y - y = z - NG.rt L n κ z := by
            rw [sub_eq_sub_iff_add_eq_add, e]
            exact add_comm _ _
          rw [h4]
          exact Submodule.sub_mem _ hz (hMst κ z hz)
        rw [h0, Submodule.mem_bot, sub_eq_zero] at hd
        exact hd
      have hzfix : ∀ κ ∈ K, NG.rt L n κ z = z := by
        intro κ hκ
        have e := hfix κ hκ
        rw [map_add (f := _), hyfix κ hκ] at e
        exact add_left_cancel e
      have e1 := rtSum_iso hS.1 haF.2 K R c hc y hy hyfix
      have e2 := ih htF z hz hzfix
      simp only [map_add (f := _), Finset.sum_add_distrib, e1, e2, smul_add]
    · have hle : a ≤ ⨆ i ∈ t, i := inf_eq_left.1 htop
      exact ih htF f ((sup_le hle le_rfl) hf) hfix

end Main

theorem rtSum_isoTyp : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f) → ∀ f ∈ NG.isoTyp ρ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS K R c hc f hf hfix
  obtain ⟨t, ht, hft⟩ := Submodule.mem_sSup_iff_exists_finset.1 hf
  exact rtSum_finset_sum hS K R c hc t ht f hft hfix

end GlobalTheory.RtSumScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarOnIsotypicPartStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (K : Subgroup (GAf L n)) (R : Finset (GAf L n)) (c : ℂ), (∀ f ∈ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f) → ∀ f ∈ NG.isoTyp ρ S, (∀ κ ∈ K, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  first | exact @GlobalTheory.RtSumScalar.rtSum_isoTyp | exact GlobalTheory.RtSumScalar.rtSum_isoTyp | (intros; apply GlobalTheory.RtSumScalar.rtSum_isoTyp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BiInvariantHeckeOpScalarOnSphericalIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BiInvariantHeckeOpScalarOnSphericalIrreducible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BiInvScalar

open GlobalTheory.SphLabelOps GlobalTheory.HeckeScalarSph

theorem biInv_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (Ds : Set (GAf L n)), (∀ x ∈ Ds, TrivOutside {s.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → ∀ R : Finset (GAf L n), (∀ γ ∈ R, γ ∈ Ds) → (∀ x ∈ Ds, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS s Ds hDt hDs R hRD hRu
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  choose Rb hRb using exists_repsU (L := L) (n := n) s.v
  let K := locK (L := L) n s.v
  let dc : GAf L n → Set (GAf L n) := fun a => {x | ∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a * k₂}

  have hdcD : ∀ a ∈ Ds, ∀ x ∈ dc a, x ∈ Ds := by
    rintro a ha _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact (hDs _ (hDs a ha k₁ h₁.1 h₁.2).2 k₂ h₂.1 h₂.2).1
  have hdc_eq : ∀ a b, b ∈ dc a → dc b = dc a := by
    rintro a _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    ext x
    constructor
    · rintro ⟨l₁, i₁, l₂, i₂, rfl⟩
      exact ⟨l₁ * k₁, K.mul_mem i₁ h₁, k₂ * l₂, K.mul_mem h₂ i₂, by group⟩
    · rintro ⟨l₁, i₁, l₂, i₂, rfl⟩
      exact ⟨l₁ * k₁⁻¹, K.mul_mem i₁ (K.inv_mem h₁), k₂⁻¹ * l₂, K.mul_mem (K.inv_mem h₂) i₂, by group⟩
  have hself : ∀ a, a ∈ dc a := fun a => ⟨1, K.one_mem, 1, K.one_mem, by group⟩

  let fib : GAf L n → Finset (GAf L n) := fun a => R.filter (fun γ => dc γ = dc a)
  have hfib : ∀ α ∈ R, (∀ γ ∈ fib α, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) ∧
      ∀ x, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ fib α ∧ γ⁻¹ * x ∈ Umax L n := by
    intro α hα
    refine ⟨fun γ hγ => ?_, fun x hx => ?_⟩
    · have e := (Finset.mem_filter.1 hγ).2
      have : γ ∈ dc α := e ▸ hself γ
      exact this
    · have hxD : x ∈ Ds := hdcD α (hRD α hα) x hx
      obtain ⟨γ, ⟨hγ, hu⟩, huniq⟩ := hRu x hxD
      have ht : TrivOutside {s.v} (γ⁻¹ * x) := triv_mul (triv_inv (hDt γ (hRD γ hγ))) (hDt x hxD)
      have hγdc : γ ∈ dc x := ⟨1, K.one_mem, (γ⁻¹ * x)⁻¹, K.inv_mem ⟨hu, ht⟩, by group⟩
      have e : dc γ = dc α := (hdc_eq x γ hγdc).trans (hdc_eq α x hx)
      exact ⟨γ, ⟨Finset.mem_filter.2 ⟨hγ, e⟩, hu⟩, fun δ hδ => huniq δ ⟨(Finset.mem_filter.1 hδ.1).1, hδ.2⟩⟩
  have hfibTriv : ∀ α ∈ R, TrivOutside {s.v} α := fun α hα => hDt α (hRD α hα)
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩

  have hsplit : ∀ (F : GAf L n → (GAf L n → W)), ∑ γ ∈ R, F γ = ∑ D ∈ R.image dc, ∑ γ ∈ R.filter (fun γ => dc γ = D), F γ :=
    fun F => (Finset.sum_fiberwise_of_maps_to (fun γ hγ => Finset.mem_image_of_mem dc hγ) F).symm
  have hD : ∀ D ∈ R.image dc, ∃ α ∈ R, R.filter (fun γ => dc γ = D) = fib α := by
    intro D hD
    obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hD
    exact ⟨α, hα, rfl⟩
  let T : (GAf L n → W) →ₗ[ℂ] (GAf L n → W) := ∑ γ ∈ R, rtHom L n W γ
  have hT : ∀ x, T x = ∑ γ ∈ R, rtHom L n W γ x := fun x => LinearMap.sum_apply _ _ _
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) Rb (fun b hb => reps_of_repsU hb (hRb b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hsplit, map_sum]
      refine Finset.sum_congr rfl fun D hDm => ?_
      obtain ⟨α, hα, e⟩ := hD D hDm
      rw [e]
      have hRα := reps_of_repsU (hfibTriv α hα) (hfib α hα)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hfibTriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      rw [hsplit (fun γ => rtHom L n W γ (∑ δ ∈ Rb b, rtHom L n W δ x)), hsplit (fun γ => rtHom L n W γ x)]
      refine Eq.trans ?_ ((Finset.sum_congr rfl fun δ _ => map_sum (rtHom L n W δ) _ _).trans Finset.sum_comm).symm
      refine Finset.sum_congr rfl fun D hDm => ?_
      obtain ⟨α, hα, e⟩ := hD D hDm
      rw [e]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n W s α b (fib α) (Rb b) (hfibTriv α hα) hb (fun y hy => (hfib α hα).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hfib α hα).1 γ hγ)) (fun y hy => (hRb b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hRb b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ⟩
  rw [hT] at e
  exact e

end GlobalTheory.BiInvScalar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BiInvariantHeckeOpScalarOnSphericalIrreducibleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)), NG.IsIrrRep ρ S → ∀ (s : SplitPlace L) (Ds : Set (GAf L n)), (∀ x ∈ Ds, TrivOutside {s.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → ∀ R : Finset (GAf L n), (∀ γ ∈ R, γ ∈ Ds) → (∀ x ∈ Ds, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK n s.v, NG.rt L n κ f = f) → ∑ γ ∈ R, NG.rt L n γ f = c • f := by
  intro L _ _ _ n W _ _ ρ S hS s Ds hDt hDs R hRD hRu
  exact GlobalTheory.BiInvScalar.biInv_scalar L n W ρ S hS s Ds hDt hDs R hRD hRu
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormCharacterGaloisCofinite
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousResI
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne Pointwise

noncomputable section

namespace GlobalTheory.WeilRes

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E E']
  [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] {A : ValuationSubring Ω}

variable [IsAlgClosure E Ω] [IsAlgClosure E' Ω] {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
  {w' : HeightOneSpectrum (𝓞 E')} (h' : IsPlaceOver A w')

theorem continuous_res : Continuous (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) := by
  refine continuous_of_continuousAt_one (AlgEquiv.restrictScalarsHom E : G E' Ω →* G E Ω) ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp hU
  let b := Module.finBasis E L
  let S : Set Ω := Set.range fun i => (b i : Ω)
  have : Finite S := (Set.finite_range _).to_subtype
  have : Algebra.IsAlgebraic E' Ω := IsAlgClosure.isAlgebraic
  rw [Filter.mem_map]
  refine (krullTopology_mem_nhds_one_iff E' Ω _).mpr ⟨IntermediateField.adjoin E' S,
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral,
    fun σ hσ => hLU ?_⟩
  have hσ' := (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ
  refine (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx => ?_
  have hlin : (AlgEquiv.restrictScalarsHom E σ).toLinearMap ∘ₗ L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => hσ' _ (IntermediateField.subset_adjoin E' S ⟨i, rfl⟩)
  exact LinearMap.congr_fun hlin ⟨x, hx⟩

end GlobalTheory.WeilRes

end
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
open Pointwise

namespace GlobalTheory

theorem trivial_on_ext_of_frob_eq_normChar : ∀ (Ω : Type) [Field Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower K M Ω] (η : HChar K), UpperTheory.V.Published.IsNormChar M η → ∀ χ : G K Ω →* ℂˣ, IsOpen (χ.ker : Set (G K Ω)) → (∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v) → ∀ g : G K Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) → χ g = 1 := by
  intro Ω _ K _ _ _ _ M _ _ _ _ _ _ η hη χ hχo hχ g hg
  classical
  let r : G M Ω →* G K Ω := AlgEquiv.restrictScalarsHom K
  have hr : Continuous r := GlobalTheory.WeilRes.continuous_res
  let u : HeightOneSpectrum (𝓞 M) → HeightOneSpectrum (𝓞 K) := fun w => w.under (𝓞 K)
  have hu : ∀ w : HeightOneSpectrum (𝓞 M), w.asIdeal.LiesOver (u w).asIdeal := fun w => ⟨rfl⟩
  have hS := Filter.eventually_cofinite.1 hχ
  have hT₁ := Filter.eventually_cofinite.1 hη.2.2
  let T : Set (HeightOneSpectrum (𝓞 M)) :=
    {w | ¬ ∀ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f → η.val (w.under (𝓞 K)) ^ f = 1} ∪
      u ⁻¹' {v | ¬ ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A v → IsFrob A (normV v) σ → χ σ = η.val v}
  have hT : T.Finite := hT₁.union (hS.preimage' (f := u) fun v _ => by
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 M)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 M) => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, hu w⟩)
  have hdense := GlobalTheory.Published.chebotarevDegreeOne'.dense (F := M) (Ω := Ω) hT
  let H : Subgroup (G M Ω) := (χ.comp r).ker
  have hHc : IsClosed (H : Set (G M Ω)) := H.isClosed_of_isOpen (by exact hχo.preimage hr)
  have hsub : {σ : G M Ω | ∃ w : HeightOneSpectrum (𝓞 M), w ∉ T ∧ w.asIdeal.inertiaDeg ℤ = 1 ∧
      ∃ B : ValuationSubring Ω, IsPlaceOver B w ∧ IsFrob B (normV w) σ} ⊆ H := by
    rintro σ ⟨w, hw, hd, B, hB, hσ⟩
    have hw1 : ∀ f : ℕ, normV w = normV (u w) ^ f → η.val (u w) ^ f = 1 := by
      by_contra h; exact hw (Or.inl h)
    have hw2 : ∀ (A : ValuationSubring Ω) (σ : G K Ω), IsPlaceOver A (u w) → IsFrob A (normV (u w)) σ →
        χ σ = η.val (u w) := by
      by_contra h; exact hw (Or.inr h)
    have hp : (Ideal.absNorm w.asIdeal).Prime :=
      ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified M).1 w).2 hd
    have hn : Ideal.absNorm (u w).asIdeal = Ideal.absNorm w.asIdeal := by
      haveI := hu w
      have h := Ideal.absNorm_pow_inertiaDeg (u w).asIdeal w.asIdeal
      have h1 := Nat.Prime.eq_one_of_pow (h ▸ hp)
      rw [h1, pow_one] at h
      exact h
    have hnv : normV w = normV (u w) := by
      simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn
      exact hn.symm
    have hBv : IsPlaceOver B (u w) := fun x => by
      have e : algebraMap K Ω (x : K) = algebraMap M Ω ((algebraMap (𝓞 K) (𝓞 M) x : 𝓞 M) : M) := by
        rw [IsScalarTower.algebraMap_apply K M Ω]; rfl
      rw [e]
      exact hB _
    have hrσ : IsFrob B (normV (u w)) (r σ) := by
      refine ⟨?_, fun x hx => ?_⟩
      · have h : σ • B = B := hσ.1
        show (σ.restrictScalars K) • B = B
        ext x
        conv_rhs => rw [← h]
        rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
          ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
        rfl
      · rw [← hnv]; exact hσ.2 x hx
    have h1 : χ (r σ) = η.val (u w) := hw2 B (r σ) hBv hrσ
    have h2 : η.val (u w) ^ 1 = 1 := hw1 1 (by rw [pow_one]; exact hnv)
    rw [pow_one] at h2
    show χ (r σ) = 1
    rw [h1, h2]
  have hall : ∀ τ : G M Ω, τ ∈ H := fun τ => hHc.closure_subset_iff.2 hsub (hdense τ)
  let τ : G M Ω := { g.toRingEquiv with commutes' := hg }
  have hτ : r τ = g := AlgEquiv.ext fun _ => rfl
  have := hall τ
  show χ g = 1
  rw [← hτ]
  exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeTwistedCuspParts
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowModelOfPointModels
noncomputable section

namespace GlobalTheory.RowModelRoad

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.BlockComplement GlobalTheory.IndefiniteRowSideFullHecke.BlockRepresentationsSemisimple

section Twist

variable {Γ O : Type} [Group Γ] [CommRing O] {n : ℕ}

end Twist

section Lift

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

end Lift

section Eig

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) (i : N.Loc)

theorem frobEig_block (θ : A.CG 1) (t : ℕ) (w : PlE H) (b : ℂ) (hu : A.unr (A.locG θ w))
    (hb : A.frobEig (A.locG θ w) = {b}) :
    A.unr (spehLoc N A ⟨1, θ, t⟩ w) ∧ A.frobEig (spehLoc N A ⟨1, θ, t⟩ w) =
      ((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => b * ((normV w : ℕ) : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ) := by
  unfold spehLoc
  dsimp only
  induction List.range t with
  | nil => exact ⟨A.lpZero_unr w, by simp [A.frobEig_zero]⟩
  | cons k l ih =>
    have h1 := (A.unr_tw _ (((t : ℝ) - 1) / 2 - k)).2 hu
    refine ⟨(A.unr_sum _ _).2 ⟨h1, ih.1⟩, ?_⟩
    refine (A.frobEig_sum _ _ h1 ih.1).trans ?_
    rw [ih.2, A.frobEig_tw _ _ hu, hb]
    simp

end Eig

variable {D : D7}

end GlobalTheory.RowModelRoad
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.EigStrCalc

theorem odd_rank (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

theorem isSplitPl_of_under (D : D7) (w : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : IsSplitPl D.host w := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := h
  rw [GlobalTheory.Mem.GoodPlace.isSplitPl_iff]
  by_cases hw : w = P
  · subst hw
    exact ⟨Q, hPQ, HeightOneSpectrum.ext (by simpa [HeightOneSpectrum.under, Ideal.under] using hQ)⟩
  · exact ⟨P, hw, HeightOneSpectrum.ext (by simpa [HeightOneSpectrum.under, Ideal.under] using hP)⟩

theorem normV_eq_absNorm {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    normV w = Ideal.absNorm w.asIdeal := by
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.EigStrCalc

namespace GlobalTheory.EigStrCalc

theorem inv_block (q : ℕ) (z : ℂ) (t : ℕ) :
    (((List.range t : List ℕ) : Multiset ℕ).map
        fun k : ℕ => z⁻¹ * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - k : ℝ)) : ℂ)).map (fun a : ℂ => a⁻¹) =
      GlobalTheory.DownLift.str q z t := by
  unfold GlobalTheory.DownLift.str
  have hr : (Multiset.range t) = (Multiset.range t).map (fun k => t - 1 - k) := by
    rw [← Finset.range_val, ← Finset.image_val_of_injOn]
    · rw [show (Finset.range t).image (fun k => t - 1 - k) = Finset.range t from ?_]
      ext k; simp only [Finset.mem_image, Finset.mem_range]; constructor
      · rintro ⟨j, hj, rfl⟩; omega
      · intro hk; exact ⟨t - 1 - k, by omega, by omega⟩
    · intro a ha b hb h; simp only [Finset.coe_range, Set.mem_Iio] at ha hb; simp only at h; omega
  rw [Multiset.map_map]
  conv_rhs => rw [hr, Multiset.map_map]
  have hcoe : ((List.range t : List ℕ) : Multiset ℕ) = Multiset.range t := rfl
  rw [hcoe]
  refine Multiset.map_congr rfl fun k hk => ?_
  rw [Multiset.mem_range] at hk
  simp only [Function.comp_apply]
  rw [mul_inv, inv_inv, ← Complex.cpow_neg]
  congr 2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast
  ring

end GlobalTheory.EigStrCalc

namespace GlobalTheory.EigStrCalc

theorem unr_of_speh {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
    (θ : A.CG 1) (t : ℕ) (ht : 1 ≤ t) (w : PlE H) (h : A.unr (spehLoc N A ⟨1, θ, t⟩ w)) :
    A.unr (A.locG θ w) := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  unfold spehLoc at h
  simp only at h
  rw [List.range_succ_eq_map] at h
  exact (A.unr_tw _ _).1 ((A.unr_sum _ _).1 h).1

end GlobalTheory.EigStrCalc
end
