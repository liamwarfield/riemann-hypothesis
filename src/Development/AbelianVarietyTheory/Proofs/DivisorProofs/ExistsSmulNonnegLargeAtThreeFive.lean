module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRuleAnyLevel
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv

open GlobalTheory.IntCuspLat

namespace GlobalTheory.LargeCover

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem factorisation_pow (Xo : Moduli Dw l) (N ℓ : ℕ) (hodd : Odd N) (hMN : l.M ∣ N) (hp : ℓ.Prime) :
    ∃ (u n' Bn j : ℕ) (β : 𝓞 E), u ∣ l.M ∧ Nat.Coprime n' ℓ ∧ (N : 𝓞 E) = β * u * n' ∧ β * H.bar β = (Bn : 𝓞 E) ∧
      u ^ 2 * Bn = ℓ ^ j ∧ ∀ (T : Over Xo.X) (t : T ⟶ Xo.univ.t.G), KilledBy Xo l.Mb (t ^ N) →
        t ^ (N ^ 2) = 1 ∧ (t ≫ Xo.univ.t.act.act β) ^ (n' ^ 2 * u ^ 2) = 1 := by
  have hN : N ≠ 0 := by rintro rfl; exact absurd hodd (by decide)
  have hM : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨e, n', hn', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN ℓ hp.ne_one
  obtain ⟨a, m, hm', hMa⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM ℓ hp.ne_one
  have hcop : Nat.Coprime n' ℓ := ((hp.coprime_iff_not_dvd).2 hn').symm
  have hcm : Nat.Coprime m ℓ := ((hp.coprime_iff_not_dvd).2 hm').symm
  have hdv : ℓ ^ a * m ∣ ℓ ^ e * n' := by rw [← hMa, ← hNe]; exact hMN
  obtain ⟨k, hk⟩ := (hcm.pow_right e).dvd_of_dvd_mul_left ((Dvd.intro_left _ rfl).trans hdv)
  have hae : a ≤ e := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1
    ((hcop.symm.pow_left a).dvd_of_dvd_mul_right ((Dvd.intro _ rfl).trans hdv))
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hae
  refine ⟨ℓ ^ a, n', ℓ ^ (2 * b), 2 * (a + b), (ℓ : 𝓞 E) ^ b, ⟨m, hMa⟩, hcop, ?_, ?_, by ring, fun T t ht => ⟨?_, ?_⟩⟩
  · rw [hNe]; push_cast; ring
  · rw [map_pow, map_natCast]; push_cast; ring
  · obtain ⟨k', hk'⟩ := hMN
    have := GlobalTheory.TorsFac.kill Xo t N ht (N : 𝓞 E)
      (by rw [hk', Nat.cast_mul]; exact l.Mb.mul_mem_right _ (GlobalTheory.TorsFac.M_mem l))
    rw [← GlobalTheory.TorsFac.act_nat, ← this]
    congr 2
    push_cast; ring
  · have := GlobalTheory.TorsFac.kill Xo t N ht (l.M * k) (l.Mb.mul_mem_right _ (GlobalTheory.TorsFac.M_mem l))
    rw [GlobalTheory.TorsFac.act_pow, ← this]
    congr 2
    rw [hNe, hMa, hk]; push_cast; ring

theorem class_bound_any_level (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N l.M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (((l.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T.Fr) *
      (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P)) := by
  letI := io.toAlgebra
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [(htp b).1]; exact GlobalTheory.ShortBound.levPt_killed Xo _ _
  obtain ⟨u, n', Bn, j, β₀, hu, h1, h2, h3, h4, h5⟩ := factorisation_pow Xo N ℓ hL.1 hL.2.1 hℓ
  have hA : (u : 𝓞 E) * H.bar (u : 𝓞 E) = ((u ^ 2 : ℕ) : 𝓞 E) := by rw [map_natCast]; push_cast; ring
  have h := sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP z tp F
    hz hg (fun b => (h5 _ _ (hk b)).1) hF htr n' (u ^ 2) Bn j _ β₀ h1 h2 hA h3 h4 (fun b => (h5 _ _ (hk b)).2)
  obtain ⟨m, hm⟩ := hu
  rw [GlobalTheory.ShortBound.nrm_nat, map_mul, map_pow, map_natCast, _root_.mul_assoc] at h
  rw [hm, mul_pow, Nat.cast_mul, _root_.mul_comm ((u ^ _ : ℕ) : T.Fr), _root_.mul_assoc, nval_mul, Nat.cast_pow u]
  calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
    _ ≤ _ := add_le_add (nval_natCast_nonneg e _) h

end Point


open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions in
theorem exists_smul_nonneg_of_shortRule_any_level (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)] (hlev : d.IsLev)
    (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (hroot : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1)
    (hwi : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q))
    (Λ : GenLat D.host.E n) (N : ℕ) (hU : Λ.Unimod) (hTM : Λ.TrivAt d.l₂.M) (hN : Λ.LevOK N d.l₂.M)
    (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w) (x0 : Fin n → Dw.La)
    (g : Rul Xo c) (hsec : g ∈ sec Xo c w n) (hR : IsShortRule Xo c d Λ N x0 P g) :
    ∃ t : c.F, t ≠ 0 ∧ ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → Λ.TrivAt ℓ →
      ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (t • g) := by
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  have hM0 : d.l₂.M ≠ 0 := by have := d.l₂.three_le; omega
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  haveI := Nat.finite_of_card_ne_zero hc0
  have hS : ∀ p ∈ D.host.condN.primeFactors, p ≠ 0 := fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  obtain ⟨X, hX⟩ : ∃ X : ℕ, X = (NumberField.discr D.host.E).natAbs * Formalism.L2.Pj.DF Dw w := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = ∏ p ∈ D.host.condN.primeFactors, p ^ X := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ (hS q hq)
  refine ⟨betaH (Dw := Dw) c Λ * ((Nat.card (Fin n → LevQ Dw d.l₂) * (Q * d.l₂.M ^ Formalism.L2.Pj.DF Dw w) : ℕ) : c.F),
    mul_ne_zero hβ (by exact_mod_cast mul_ne_zero hc0 (mul_ne_zero hQ0 (pow_ne_zero _ hM0))), ?_⟩
  rintro la ℓ hℓ hmem htr _ ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩
  show 0 ≤ nval Tc.V e (evI yI _)
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot Λ N hU hTM hN w P hP x0 g hsec hR Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have hu : ¬ IsUnit (ℓ : T'.V) := fun hu => by
    have h1 := vV_natCast T' hu
    have h2 := ho'.2 (ℓ : c.F)
    rw [map_natCast, h1] at h2
    have h3 := vLa_pos_of_mem la hℓ.ne_zero hmem
    have h4 : (0 : ℤ) < ((r * e : ℕ) : ℤ) := by exact_mod_cast he'
    exact (mul_pos h4 h3).ne h2
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  have key := fun q => class_bound_any_level d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (fun b => levRep (q b)) (htp q) (hF q) htr
  rw [pow_one] at hζ
  rw [← nval_bc iT hr hiT e, evI_smul, map_mul, hval, ← hio, hζ, _root_.one_mul]
  have := Fintype.ofFinite (Fin n → LevQ Dw d.l₂)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
  refine le_nval_sum T' _ _ _ _ fun q _ => ?_
  have hq := key q
  letI := io₂.toAlgebra
  generalize (∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b))
    (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P)) = Sm at hq ⊢
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hc1 : ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) ≠ 0 := by exact_mod_cast hc0
  have hQ1 : (Q : T'.Fr) ≠ 0 := by exact_mod_cast hQ0
  have hQv : 0 ≤ nval T'.V (r * e) ((Q : T'.Fr) * (((d.l₂.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T'.Fr) *
      (io₂ (((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ *
        ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * Sm))) := by
    rw [nval_mul, nval_of_ne hQ1]
    refine le_trans ?_ (add_le_add le_rfl hq)
    rw [← EReal.coe_add, EReal.coe_nonneg, ← sub_eq_add_neg, sub_nonneg, hQ, vV_prod_pow T' X _ hS, Int.cast_sum,
      Finset.sum_div]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : (0 : ℝ) ≤ (vV T'.V (p : T'.Fr) : ℝ) / ((r * e : ℕ) : ℝ) :=
      div_nonneg (by exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p) (Nat.cast_nonneg _)
    have h2 : D.host.vdH p ≤ ((NumberField.discr D.host.E).natAbs : ℝ) :=
      (div_le_self (Nat.cast_nonneg _) (by exact_mod_cast Module.finrank_pos)).trans
        (by
          have h : padicValNat p (NumberField.discr D.host.E).natAbs ≤
              (NumberField.discr D.host.E).natAbs := by
            rw [Nat.padicValNat_def]
            exact Nat.multiplicity_le_self _
          exact_mod_cast h)
    have h3 := D.host.vdH_nonneg p
    have h4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) := Nat.cast_nonneg _
    rw [Int.cast_mul, Int.cast_natCast, mul_div_assoc (X : ℝ), hX, Nat.cast_mul (NumberField.discr D.host.E).natAbs]
    have h5 := mul_nonneg (mul_nonneg h1 h3) h4
    have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h1) h4
    linarith
  refine le_trans (add_nonneg (GlobalTheory.ShortBound.nval_nonneg (V := T'.V) (r * e) (map_isIntegral_int io₂ (hwi x0 q))) hQv)
    (le_of_eq ?_)
  rw [← nval_mul]
  congr 1
  simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
  generalize (io₂ ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree))⁻¹ = a1
  generalize ((Λ.mIdx N (Dw.p + Dw.q) : ℕ) : T'.Fr)⁻¹ = a2
  field_simp

end GlobalTheory.LargeCover
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LargeCover

open IsDedekindDomain Formalism.MainNotions GlobalTheory.IntCuspLat


set_option maxHeartbeats 1000000 in
theorem exists_smul_nonneg_of_dvd (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o) (w : ℕ)
    (hw : ∀ (u : D.host.E) (n : ℕ), 0 < n → u ^ n = 1 → u ^ w = 1) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n)
    (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n) (hla : ∀ σ k τ i, (w : ℤ) ∣ laU (Y.U σ) a n k τ i)
    (f : Rul Y.d.Xo₂ Y.d.c₂) (hf : f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n) :
    ∃ s : 𝓞 Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  let σ : Y.d.c₂.F →+* ℂ := Y.d.c₂.F.val.toRingHom
  have hσ : GoodEmb Y.d.c₂ σ := rfl
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hU : Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) := (Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)
  have hpq : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := hU.1
  have hA : Y.d.l₂.A = 1 := hG.lev.2
  have hC := GlobalTheory.ChartFree.chartIndep
  have hP : ∀ k, PrincUpTo ((Y.U σ).X k) Y.d.l₂.M (laU (Y.U σ) a n k) := fun k =>
    princUpTo_of_root _ _ w hw _ (hla σ k)
      (GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _ _ hU hA hr k)
  obtain ⟨_, hW⟩ := hG.modelW σ hσ
  have hGm : ∀ k k', ((Y.U σ).X k).Gm = ((Y.U σ).X k').Gm ∧ ((Y.U σ).X k).ξ0 = ((Y.U σ).X k').ξ0 :=
    fun k k' => ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  have hχ := fun k => hG.chiTriv σ hσ a n hdom k
  have hf' := (mem_cusp _ _ _ a n f).1 hf
  have h1 : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := hpq ▸ hr
  have hL : Out.Laws := GlobalTheory.firstFiveLaws.1
  have hB : Out.SecBaseChangeSt := hL.secBaseChange
  have hnr : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n := by
    have h0 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    have : D.R.r ≤ Module.finrank ℚ D.host.E * D.R.r := Nat.le_mul_of_pos_left _ h0
    omega
  have hd : ∃ d : DeltaDat Y.d.Xo₂ Y.d.c₂ n, d.IsLev ∧ (∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂) ∧
      d.cδ = 1 ∧ d.pd = 1 ∧ d.l₂.A = Y.d.l₂.A ∧ ∃ ph x₀, d.PhiPin ph 1 x₀ := by
    obtain ⟨d, e1, -, e2, -, -, hδ, hlev, hnab⟩ :=
      GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ Y.d.Xo₂ Y.d.c₂ h1 n 1 ⊤ Y.d.l₂ Y.d.Xo₂ Y.d.c₂ rfl
        ⟨dvd_rfl, le_rfl, dvd_rfl⟩ (Nat.mul_one _).symm (Nat.coprime_one_left _) (Ideal.mul_top _).symm
        (top_sup_eq _)
    obtain ⟨f, ph, x₀, hpin⟩ := GlobalTheory.exists_phiPin_of_character _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev hnr 1
    exact ⟨{ d with φδ := f }, hlev, hnab, hδ, e1, congrArg (·.A) e2, ph, x₀, hpin⟩
  obtain ⟨d, hlev, hnab, hδ, hpe, hAe, ph, x₀, hpin⟩ := hd
  have hT : AllTest d.Xo₂ d.c₂ := GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ d.l₂ d.Xo₂ d.c₂
  obtain ⟨_, nab, -⟩ := GlobalTheory.CanonConn.exists_isNab hL _ _ _ _ Y.d.Xo₂ Y.d.c₂
  have hone : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y = 1 :=
    fun k _ _ y => by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
  have hunit : GlobalTheory.Dict.UnitC d := fun A y => by
    have : evR d.Xo₂ d.c₂ d.cδ y = 1 := by
      rw [hδ]
      exact evalAt_one _ _ _ (hT _ _)
    rw [this, norm_one]
  have h3 : ¬ 3 ∣ d.pd := by rw [hpe]; decide
  have htie : d.PsiTie 1 := by
    intro k g ρ _ _ _ _ K _ _ _ y y' _
    change evR d.Xo₂ d.c₂ d.cδ y' =
      algebraMap d.c₂.F K (d.eF ((1 : Y.d.c₂.Fˣ) : Y.d.c₂.F)) * evR d.Xo₂ d.c₂ d.cδ y
    rw [hone K y, hone K y']
    simp
  have hind := (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.lawsFieldsSeparately.2.1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ σ
    D.R.r _ hU a n).1
  refine exists_smul_nonneg_of_span (fun la => isVal_valSet la)
    (fun b => shortGen Y.d.Xo₂ Y.d.c₂ nab b 0 a n d) (fun b hb => ?_) fun b hb g hg => ?_
  · have htot : ShortValTot Y.d.Xo₂ Y.d.c₂ nab b 0 a n d :=
      GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d (GlobalTheory.levelMaps_closed hL _ _ _ h1)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ Y.d.Xo₂ Y.d.c₂).2.2.1
        (GlobalTheory.Frames.allTest_of_secBaseChange hB _ _ _ _ Y.d.Xo₂ Y.d.c₂)
        (GlobalTheory.Frames.algebraic_laws hB _ _ _ _ _ _).2.2.1 hT hlev hAe hnab (fun _ => ⟨ph, 1, x₀, hpin, htie⟩)
        nab b 0 a
    have hsp := holSub0_le_span_shortGen_upto hC _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d σ D.R.r _ hσ hU hr hA hGm
      hlev hnab hunit h3 (fun _ => ⟨ph, 1, x₀, hpin⟩) nab b 0 a hb hdom hn hP hχ htot
    refine GlobalTheory.mem_span_of_map_mem_span_image (Formalism.L2.PjFree.rdU (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)))
      (sec Y.d.Xo₂ Y.d.c₂ a n) hind (shortGen Y.d.Xo₂ Y.d.c₂ nab b 0 a n d) (fun g hg => hg.1) hf'.1 (hsp ?_)
    exact ⟨hf'.2 _ hσ, fun k x hx => dif_neg hx⟩
  · obtain ⟨hsec, Λ, N, x0, P, hUn, hTb, hTM, hN, -, hPl, hR⟩ := hg
    obtain ⟨inst, hnab⟩ := hnab
    obtain ⟨t, ht, hb'⟩ := exists_smul_nonneg_of_shortRule_any_level D _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev hnab
      (fun k _ _ y => by rw [hone k y, one_pow])
      (GlobalTheory.PlaceInt.datum_isIntegral _ _ _ _ Y.d.Xo₂ Y.d.c₂ n d hlev ph 1 x₀ hpin)
      Λ N hUn hTM hN a P hPl x0 g hsec hR
    exact ⟨t, N, ht, hN.1.pos, fun la ℓ hℓ hm hor =>
      hb' la ℓ hℓ hm (hor.elim (trivAt_of_dvd hTb) (trivAt_of_not_dvd hUn hN hℓ))⟩

theorem exists_smul_nonneg_all (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hdom : Dom a n) (hn : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n)
    (f : Rul Y.d.Xo₂ Y.d.c₂) (hf : f ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n) :
    ∃ s : 𝓞 Y.d.c₂.F, s ≠ 0 ∧ ∀ la, ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la, 0 ≤ v (s • f) := by
  have hmul : CuspMul Y.d.Xo₂ Y.d.c₂ Y.U := cusp_mul_of_M5 ReciprocityTheory.ChartRestriction.G.FD.siegelSpaceAlgebra_holds _
  have hD : ∀ k : ℕ, Dom (k • a) (k * n) := fun k =>
    ⟨fun τ i i' hi => Nat.mul_le_mul_left k (hdom.1 τ hi), hdom.2.mul_left k⟩
  have hpow : ∀ k : ℕ, f ^ (k + 1) ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U ((k + 1) • a) ((k + 1) * n) := fun k => by
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      rw [pow_succ, succ_nsmul a (k + 1), Nat.succ_mul (k + 1)]
      exact hmul _ _ _ _ _ _ (hD _) hdom ih hf
  obtain ⟨w, hw0, hw⟩ := exists_pow_root_eq_one D.host.E
  obtain ⟨k, rfl⟩ : ∃ k, w = k + 1 := ⟨w - 1, by omega⟩
  have h2 : ((k + 1 : ℕ) : ℤ) ∣ (((k + 1) * n / 2 : ℕ) : ℤ) := by
    obtain ⟨m, hm⟩ := hdom.2
    rw [hm, ← two_mul, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
    exact Int.natCast_dvd_natCast.2 (dvd_mul_right _ _)
  have h1 : ∀ x, ((k + 1 : ℕ) : ℤ) ∣ ((((k + 1) • a) x : ℕ) : ℤ) := fun x =>
    Int.natCast_dvd_natCast.2 (dvd_mul_right (k + 1) (a x))
  obtain ⟨s, hs, h⟩ := exists_smul_nonneg_of_dvd D T j Y e o hG (k + 1) hw _ _ (hD (k + 1))
    (hn.trans (Nat.le_mul_of_pos_left _ hw0)) (fun σ c τ i => by
      unfold laU
      split_ifs
      · exact (h1 _).add h2
      · exact (h1 _).neg_right.sub h2) _ (hpow k)
  exact ⟨s, hs, fun la v hv => nonneg_of_pow (fun la => isVal_valSet la) hv s f _ (h la v hv)⟩

end GlobalTheory.LargeCover
