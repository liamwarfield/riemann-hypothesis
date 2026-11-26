module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepVectorLocalPureTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateReferenceCharactersGoodEmbeddings
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

theorem linearIndependent_rows_map {K L : Type*} [Field K] [Field L] (e : K →+* L) {n m : ℕ}
    (a : Fin n → Fin m → K) (ha : LinearIndependent K a) :
    LinearIndependent L fun c k => e (a c k) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K a).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 ha.fintypeLinearCombination_injective)
  have hj : ∀ c j, g (a c) j = if c = j then 1 else 0 := fun c j => by
    have := congrFun (LinearMap.congr_fun hg (Pi.single c 1)) j
    simpa [Pi.single_apply, eq_comm] using this
  have hg' : ∀ (x : Fin m → K) j, g x j = ∑ k, x k * g (fun j' => if k = j' then 1 else 0) j := fun x j => by
    conv_lhs => rw [pi_eq_sum_univ x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.linearIndependent_iff]
  intro μ hμ j
  have h0 : ∀ k, ∑ c, μ c * e (a c k) = 0 := fun k => by
    have := congrFun hμ k
    simpa [Finset.sum_apply] using this
  calc μ j = ∑ c, μ c * e (g (a c) j) := by simp [hj]
    _ = ∑ c, ∑ k, μ c * e (a c k * g (fun j' => if k = j' then 1 else 0) j) :=
        Finset.sum_congr rfl fun c _ => by rw [hg' (a c) j, map_sum, Finset.mul_sum]
    _ = ∑ k, e (g (fun j' => if k = j' then 1 else 0) j) * ∑ c, μ c * e (a c k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul]
        ring
    _ = 0 := by simp [h0]

theorem realRd_faithful : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), ν ≠ 0 → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _) → (S.A ((j : ℕ) + 1)).IsKsForm → Faithful (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hν hU hW hv hK
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add (f := _)]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let B : Module.Basis (Fin m) (NX.KB S i b) (NX.Fm S i ((j : ℕ) + 1) b) :=
    Algebra.TensorProduct.basis (NX.KB S i b) bK
  intro n v hvi
  let w : Fin n → NX.Fm S i ((j : ℕ) + 1) b := fun c => YS.eF i _ b (Nat.le_add_left _ _) j.2 (v c)
  have hw0 : LinearIndependent (FractionRing (D.ntw.O i)) w :=
    hvi.map' (YS.eF i _ b (Nat.le_add_left _ _) j.2).toLinearMap (YS.eF i _ b (Nat.le_add_left _ _) j.2).ker
  have hw1 : LinearIndependent (NX.KB S i b) w := hw0
  have hw : LinearIndependent (NX.KB S i b) fun c => B.equivFun (w c) :=
    hw1.map' B.equivFun.toLinearMap B.equivFun.ker
  have hr := linearIndependent_rows_map (ρ.e i b) (fun c => B.equivFun (w c)) hw
  let Ψ : (Fin m → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) := ν⁻¹ • Fintype.linearCombination ℂ φ
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun z hz => ?_
    have h0 : Fintype.linearCombination ℂ φ z = 0 := by
      have := hz
      simp only [Ψ, LinearMap.smul_apply, smul_eq_zero, inv_eq_zero, hν, false_or] at this
      exact this
    exact hφ.fintypeLinearCombination_injective (h0.trans (map_zero _).symm)
  suffices key : (fun c => realRd YS v₀ hρ i j b ν (v c)) = Ψ ∘ fun c k => ρ.e i b (B.equivFun (w c) k) by
    rw [key]; exact hr.map' Ψ hΨ
  funext c
  change ν⁻¹ • evK YS v₀ hρ i j b (w c) = ν⁻¹ • Fintype.linearCombination ℂ φ _
  congr 1
  rw [Fintype.linearCombination_apply]
  conv_lhs => rw [← B.sum_equivFun (w c)]
  refine (map_sum (evK YS v₀ hρ i j b) _ _).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show B k = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bK k : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) from
    Algebra.TensorProduct.basis_apply _ _]
  change evK YS v₀ hρ i j b ((B.equivFun (w c) k • (1 : NX.KB S i b)) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1))) = _
  rw [smul_eq_mul, mul_one]
  refine (evK_tmul YS v₀ hρ i j b _ _).trans ?_
  exact congrArg _ (congrArg (evW YS v₀ j) (hbK k))

end GlobalTheory.SeriesTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

def flipIdx (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) : ℕ :=
  ∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((m : ℕ) : 𝓞 D.host.E)})) ^ (V.rank * W.rank)

def flipScal (χW : (AE D)ˣ →* Circle) (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (x : (AE D)ˣ) : ℂ :=
  ((χW x : Circle) : ℂ)⁻¹ * ((Real.sqrt (flipIdx V W T m : ℝ) : ℝ) : ℂ)⁻¹

def IsFlipDet (V : HSp D) (e : AE D) (m : ℕ) (x : (AE D)ˣ) : Prop :=
  (x : AE D) * (e * (m : AE D) ^ V.rank + (1 - e)) = 1

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinPartMulIncAMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.HeckeDetChar

open Formalism.L2.JoinChr
open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem place_eq {e : AE D} {P P' : Pl D.host.E} (h : IsIdemAt e P) (h' : IsIdemAt e P') : P = P' := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [h.2 x hx, h'.2 x hx]

theorem finPart_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : finPart D e ∈ intAE D := by
  by_contra hc
  have := (he.2 1 one_ne_zero).2 (by
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem finPart_mul_incA_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) {x : D.host.E}
    (hx : P.valuation D.host.E x ≤ 1) : finPart D (e * incA D x) ∈ intAE D := by
  obtain ⟨n, d, h⟩ := P.exists_primeCompl_mul_eq_of_integer x hx
  have hd : (d : 𝓞 D.host.E) ∉ P.asIdeal := d.2
  have hd0 : (d : 𝓞 D.host.E) ≠ 0 := fun h0 => hd (h0 ▸ zero_mem _)
  have hdE : ((d : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h0; apply hd0; exact RingOfIntegers.ext h0
  have hxe : x = (n : D.host.E) * ((d : 𝓞 D.host.E) : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hdE]; exact h
  have h1 : finPart D (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D :=
    not_not.1 (mt (he.2 _ hd0).2 hd)
  rw [hxe, RingHom.map_mul (incA D), show e * (incA D (n : D.host.E) * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) =
    incA D (n : D.host.E) * (e * incA D (((d : 𝓞 D.host.E) : D.host.E)⁻¹)) by ring, RingHom.map_mul (finPart D)]
  exact GlobalTheory.HeckeConj.mul_mem_intAE D (GlobalTheory.SplitIndex.finPart_incA_mem n) h1

theorem idem_mul_eq_zero {Q : Finset (Pl D.host.E)} (hS : SplitSet Q) {P : Pl D.host.E}
    (hoff : Bridge.SplitOff P (Q : Set (Pl D.host.E))) {e : AE D} (he : IsIdemAt e P) :
    (idem Q + cA D (idem Q)) * e = 0 := by
  have hc : IsIdemAt (cA D e) (conjPl P) := GlobalTheory.MovedIdem.isIdemAt_conj he fun _ => Iff.rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_eq_zero fun Q' hQ' => ?_
  have he' := hS.isIdemAt hQ'
  rw [add_mul]
  have a1 : idemAt Q' * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 he.1 with h | h
    · rw [h] at he'
      exact absurd (place_eq he he' ▸ hQ' : P ∈ (Q : Set (Pl D.host.E))) hoff.2.1
    · exact h
  have a2 : cA D (idemAt Q') * e = 0 := by
    rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he'.1 hc.1 with h | h
    · rw [h] at he'
      have hPQ := place_eq hc he'
      refine absurd ?_ (hoff.2.2 Q' hQ')
      rw [← hPQ]
      ext x
      rw [Formalism.L2.Col.mem_conjIdeal]
      rfl
    · have := congrArg (cA D) h
      rwa [map_mul, GlobalTheory.MovedIdem.cA_cA, map_zero] at this
  rw [a1, a2, add_zero]

theorem chi_eq_one {χ : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)} (hχ : GlobalTheory.ExportSeries.UnramOutside χ Q)
    {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) (hQ : (idem Q + cA D (idem Q)) * e = 0) (x : (AE D)ˣ)
    (y y' : AE D) (hx : (x : AE D) = 1 + e * (y - 1)) (hx' : ((x⁻¹ : (AE D)ˣ) : AE D) = 1 + e * (y' - 1))
    (hy : finPart D (e * y) ∈ intAE D) (hy' : finPart D (e * y') ∈ intAE D) : χ x = 1 := by
  have key : ∀ w : AE D, finPart D (e * w) ∈ intAE D → finPart D (1 + e * (w - 1)) ∈ intAE D := fun w hw => by
    rw [show 1 + e * (w - 1) = 1 - e + e * w by ring, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one]
    exact add_mem (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) (finPart_mem he)) hw
  refine hχ x ?_ ?_ ?_ ?_
  · rw [hx, RingHom.map_add (f := _), RingHom.map_one, RingHom.map_mul, GlobalTheory.StepVec.infPart_idemAt he, zero_mul, add_zero]
  · rw [hx]; exact key y hy
  · rw [hx']; exact key y' hy'
  · rw [hx, mul_add, mul_one, ← mul_assoc, hQ, zero_mul, add_zero]

theorem locE_pow {e : AE D} (he : e * e = e) (a : AE D) (k : ℕ) :
    (1 + e * (a - 1)) ^ k = 1 + e * (a ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    linear_combination (a ^ k - 1) * (a - 1) * he

theorem isPlIdem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : IsPlIdem D e P := by
  obtain ⟨⟨h1, h2, v, ε, hv, hs⟩, h3⟩ := he
  exact ⟨h1, ⟨v, ε, hv, Or.inl ⟨h2, hs⟩⟩, h3⟩

theorem locU_inv {e : AE D} (he : e * e = e) (k : D.host.Eˣ) :
    (((locU he k)⁻¹ : (AE D)ˣ) : AE D) = locE D e ((k⁻¹ : D.host.Eˣ) : D.host.E) := by
  have hmul : locU he k * locU he k⁻¹ = 1 := by
    apply Units.ext
    rw [Units.val_mul, locU_val, locU_val, locE_mul_locE he, Units.mul_inv, Units.val_one]
    simp [locE]
  rw [inv_eq_of_mul_eq_one_right hmul, locU_val]

theorem val_unif {P : Pl D.host.E} {ϖ : 𝓞 D.host.E} (hP : ϖ ∈ P.asIdeal) (hP2 : ϖ ∉ P.asIdeal ^ 2) :
    P.valuation D.host.E (ϖ : D.host.E) = WithZero.exp (-1 : ℤ) := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hP2 (zero_mem _)
  rw [show (ϖ : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E ϖ from rfl, P.valuation_of_algebraMap]
  have a1 := (P.intValuation_lt_one_iff_mem ϖ).2 hP
  have a2 := (P.intValuation_le_pow_iff_mem ϖ 2).not.2 hP2
  rw [P.intValuation_eq_exp_neg_multiplicity hϖ0] at a1 a2 ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at a1
  rw [WithZero.exp_le_exp] at a2
  congr 1
  push_cast at a2
  omega

theorem chi_detAt : ∀ {D : D7} {χ : (AE D)ˣ →* Circle} {c : Formalism.L2.Host.HChar D.host.E}, ChrEq χ c →
    ∀ {Q : Finset (Pl D.host.E)}, GlobalTheory.ExportSeries.UnramOutside χ Q → GlobalTheory.ExportSeries.SplitSet Q → ∀ {P : Pl D.host.E},
    Bridge.SplitOff P (Q : Set (Pl D.host.E)) → ∀ {V : HSp D} {k : ℕ} {α : GA D V}, IsHeckeAt V P k α →
    ∀ {z : (AE D)ˣ}, IsDetAt (idemAt P) V α z → ((χ z : Circle) : ℂ) = ((c.val P : ℂˣ) : ℂ) ^ k := by
  intro D χ c hχc Q hU hS P hoff V k α hα z hz
  obtain ⟨e, ϖ, he, hϖP, hϖP2, hH⟩ := hα
  rw [idemAt_eq he] at hz
  obtain ⟨-, -, -, -, u, u', hu, hu', huu, hdet⟩ := hH
  have hQe := idem_mul_eq_zero hS hoff he
  have hee : e * e = e := he.1.1
  have hv := val_unif hϖP hϖP2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.exp_ne_zero hv.symm
  set ϖU : D.host.Eˣ := Units.mk0 (ϖ : D.host.E) hϖ0 with hϖU

  let wU : (AE D)ˣ := ⟨1 + e * (u - 1), 1 + e * (u' - 1),
    by linear_combination (u - 1) * (u' - 1) * hee + huu,
    by linear_combination (u - 1) * (u' - 1) * hee + huu⟩
  have hw : χ wU = 1 := chi_eq_one hU he hQe wU u u' rfl rfl
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu)
    (by rw [RingHom.map_mul]; exact GlobalTheory.HeckeConj.mul_mem_intAE D (finPart_mem he) hu')

  have hz' : z = locU hee ϖU ^ k * wU := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, locU_val, locE, locE_pow hee, hz]
    show e * (mt V α).det + (1 - e) = (1 + e * (incA D (ϖ : D.host.E) ^ k - 1)) * (1 + e * (u - 1))
    linear_combination hdet - (incA D (ϖ : D.host.E) ^ k - 1) * (u - 1) * hee

  have h1 : ((χ (locU hee ϖU) : Circle) : ℂ) = ((c.locK P ϖU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) ϖU _ (locU_val hee ϖU)

  set rU : D.host.Eˣ := ϖU * (Formalism.L2.Host.unif P)⁻¹ with hrU
  have hvπ : P.valuation D.host.E ((Formalism.L2.Host.unif P : D.host.Eˣ) : D.host.E) = WithZero.exp (-1 : ℤ) := by
    have := Formalism.L2.Host.unif_spec P
    unfold Formalism.L2.Host.IsUnifAt at this
    rw [← this]
    show _ = Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) _)
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _).symm
  have hvr : P.valuation D.host.E (rU : D.host.E) = 1 := by
    rw [hrU, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvπ, hϖU, Units.val_mk0, hv]
    exact mul_inv_cancel₀ (WithZero.exp_ne_zero)
  have hr1 : χ (locU hee rU) = 1 := by
    refine chi_eq_one hU he hQe _ (incA D (rU : D.host.E)) (incA D ((rU⁻¹ : D.host.Eˣ) : D.host.E)) rfl
      (locU_inv hee rU) (finPart_mul_incA_mem he hvr.le) (finPart_mul_incA_mem he ?_)
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvr, inv_one]
  have hr2 : ((χ (locU hee rU) : Circle) : ℂ) = ((c.locK P rU : ℂˣ) : ℂ) :=
    hχc.2 P e (isPlIdem he) rU _ (locU_val hee rU)
  rw [hr1] at hr2
  have hval : ((c.locK P ϖU : ℂˣ) : ℂ) = ((c.val P : ℂˣ) : ℂ) := by
    have : ϖU = rU * Formalism.L2.Host.unif P := by rw [hrU, inv_mul_cancel_right]
    rw [this, map_mul, Units.val_mul, ← hr2, Formalism.L2.Host.HChar.val]
    simp
  rw [hz', map_mul, map_pow, hw, mul_one, Circle.coe_pow, h1, hval]

end GlobalTheory.HeckeDetChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeight
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseLiftWeight

theorem c_eq {D : D7} {T0 : Type} {L : LevCh D T0} {μ0 : T0} {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)}
    (hL : L.Is μ0) (hB : B.Good) (hmu : B.mu0 = L.mu0 ((j : ℕ) + 1)) (τ : D.what₂.Tau) :
    B.w.c τ = GlobalTheory.ConjTwist.liftC D j τ := by
  have h1 := hB.inf τ
  rw [hmu] at h1
  have h2 := GlobalTheory.Mem.HeckeExp.hasInfExp_unique h1 (GlobalTheory.ConjRefChar.reference_lift_character_exponent_neg_base hL j τ)
  have hs := hB.sig τ
  have hp : B.w.p τ = ((Wc D j).sig (tauE D τ)).1 := congrArg Prod.fst hs
  have hq : B.w.q τ = ((Wc D j).sig (tauE D τ)).2 := congrArg Prod.snd hs
  have h3 := GlobalTheory.ConjTwist.liftC_cast D j τ
  rw [hp, hq] at h2
  have h4 : (B.w.c τ : ℚ) = (GlobalTheory.ConjTwist.liftC D j τ : ℚ) := by
    rw [h3]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.pS, GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.qS] at *
    linarith
  exact_mod_cast h4

theorem lam_eq : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), L.Is μ0 → B.Good → B.mu0 = L.mu0 ((j : ℕ) + 1) → (∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) → (∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) → B.w.lam = FWT.lamV D j := by
  intro D T0 L μ0 j B hL hB hmu hap ham
  funext τ
  have hs := hB.sig τ
  have hp : B.w.p τ = ((Wc D j).sig (tauE D τ)).1 := congrArg Prod.fst hs
  have hq : B.w.q τ = ((Wc D j).sig (tauE D τ)).2 := congrArg Prod.snd hs
  have hc := c_eq hL hB hmu τ
  have e1 := hB.wt.lam_eq τ
  have e2 := (GlobalTheory.ConjTwist.liftWeight_good D j).lam_eq τ
  rw [hp, hq, hap τ, ham τ, hc] at e1
  have key : (B.w.lam τ).w = (FWT.lamV D j τ).w := funext fun a => (e1 a).trans (e2 a).symm
  generalize B.w.lam τ = x at key
  generalize FWT.lamV D j τ = y at key
  cases x
  cases y
  cases key
  rfl

end GlobalTheory.BaseLiftWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodBaseDataWeightEqLiftCoeffModuleWeightStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_baseData_weight_eq_lift_coeff_module_weight : ∀ (D : D7) (T0 : Type) (L : LevCh D T0) (μ0 : T0) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)), L.Is μ0 → B.Good → B.mu0 = L.mu0 ((j : ℕ) + 1) → (∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ) → (∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ) → B.w.lam = FWT.lamV D j := by
  first | exact @GlobalTheory.BaseLiftWeight.lam_eq | exact GlobalTheory.BaseLiftWeight.lam_eq | (intros; apply GlobalTheory.BaseLiftWeight.lam_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.ActProof
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem parLev_eq_of {n : ℕ} {LL : Type} [CommRing LL] (hc : CMData D.host.F D.host.E) (J : Matrix (Fin n) (Fin n) D.host.E)
    (β : GL (Fin n) (D.host.E ⊗[D.host.F] Af D.host.F)) (L L' : LevDat D.host.E LL n) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q)
    (hb : (blkOf L.r L.t : Fin n → ℕ) = blkOf L'.r L'.t) (hb2 : (blk2 L.r : Fin n → ℕ) = blk2 L'.r) :
    parLev hc J β L = parLev hc J β L' := by
  unfold parLev
  rw [hP, hQ, hb, hb2]

theorem blkOf_eq_zero {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem twoBlockSizes_eq_zero_of_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_twoBlockSizes_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) : g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [twoBlockSizes_eq_zero_of_le h] at hik
  exact absurd hik (lt_irrefl _)

variable (Rl : RealDat3 D A3 Ks) (j : Fin D.R.m)

theorem levChi_flagL (κ : GA D (Wc D j)) : levChi (Wc D j) (Rl.βW j) (flagL (Rl.datWp j Rl.triv)) κ = 1 := by
  unfold levChi levFn
  have h1 : (flagL (Rl.datWp j Rl.triv)).P.chi = 1 := rfl
  have hs : (flagL (Rl.datWp j Rl.triv)).s = 0 := rfl
  have hq : (flagL (Rl.datWp j Rl.triv)).Q = ∅ := rfl
  rw [h1, subgroupCharExtension_one_apply, hs, hq]
  simp

theorem hasType_of_mem_wall {σ : D.what₂.LL →+* ℂ} {F : MMap (Rl.MW j σ)} (hF : F ∈ Rl.toRealDat.Wall j σ)
    (v : (Rl.MW j σ).Vec) : HasType (Wc D j) (Rl.βW j) (flag1L (Rl.datWp j Rl.triv)) (F v) := by
  have key : ∀ F' ∈ Rl.toRealDat.Wall j σ, ∀ (v : (Rl.MW j σ).Vec), ∀ κ ∈ levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv),
      ∀ h, F' v (h * κ) = levChi (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) κ * F' v h := by
    intro F' hF'
    induction hF' using Submodule.span_induction with
    | mem x hx => exact fun v κ hκ h => hx.lev v κ hκ h
    | zero => intro v κ _ h; simp only [MultilinearMap.zero_apply, Pi.zero_apply, mul_zero]
    | add x y _ _ hx hy =>
      intro v κ hκ h
      rw [MultilinearMap.add_apply, Pi.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]
    | smul a x _ hx =>
      intro v κ hκ h
      rw [MultilinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul, smul_eq_mul, mul_left_comm]
  exact fun κ hκ h => key F hF v κ hκ h

theorem isLift_transfer {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hp : RealPin Rl cG ρ) (i : D.ntw.Tw) (b : Bool)
    (g : G0g D.nd) (κ : GA D (Wc D j))
    (h : IsLevelLift (Wc D j) (ρ.B i j b).F.βT (ρ.B i j b).G.levT (ρ.eG i j b g) κ) :
    IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g) κ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hp.frT] at h2 h3
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (ρ.B i j b).G.levT =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    apply parLev_eq_of
    · exact hp.Pg i j b
    · rfl
    · exact (blkOf_eq_zero le_rfl).trans (blkOf_eq_zero hr).symm
    · exact (twoBlockSizes_eq_zero_of_le le_rfl).trans (twoBlockSizes_eq_zero_of_le hr).symm
  refine ⟨h1, hpar ▸ h2, ?_⟩
  funext PP
  apply Units.ext
  ext a c
  have hPP : PP.1 ∈ (ρ.B i j b).G.Pg := (hp.Pg i j b).symm ▸ PP.2
  have hg := hp.grp i j b g PP.1 hPP PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
  rw [← h3] at hg
  have hg2 : Units.val (cG.symm g PP) a c =
      Units.val (rTup (Rl.βW j) (ρ.B i j b).G.levT (finE (Wc D j) κ) ⟨PP.1, hPP⟩)
        (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c) := hg.symm
  rw [hg2]
  unfold rTup
  erw [upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le le_rfl _)]
  rfl

theorem sg0_eq_embLL (Rl : RealDat3 D A3 Ks) : sg0 D A3.A = D.what₂.embLL := by
  ext c
  exact congrArg (fun f : D.what₂.LL →+* ℂ => f c) (Links.sgAt_mk _ Rl.hv0)

theorem evW_rho (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (g' : S.G) (κ : GA D (Wc D j)) (hκ : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm (S.eG g')) κ)
    (z : S.WL ((j : ℕ) + 1)) (x : GA D (Wc D j)) :
    evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ g' z) x =
      D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi g' : D.what₂.LLˣ) : D.what₂.LL) * evW YS v₀ j z (x * κ) := by
  have hgeq : Rl.eG ((YS.fi j).eG g') = cG.symm (S.eG g') := by
    rw [← YS.geq j g', MulEquiv.symm_apply_apply]
  have hκ' : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) κ := hgeq ▸ hκ
  set F := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e z)) with hFdef
  have hmem : F ∈ Rl.toRealDat.Wall j (sg0 D A3.A) := (hW j _).2.1 ▸ LinearMap.mem_range_self _ _
  have hT := hasType_of_mem_wall Rl j hmem (v₀ j _)
  have hs := level_action_spec hT ⟨κ, hκ'⟩ κ hκ' x
  rw [levChi_flagL, inv_one, one_mul] at hs
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ g' z))) (v₀ j _) x = _
  rw [(YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi]
  change sg0 D A3.A _ * (actG0 (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) (F (v₀ j _))) x = _
  rw [hs]
  exact congrArg (· * F (v₀ j _) (x * κ)) (congrArg (fun f : D.what₂.LL →+* ℂ => f _) (sg0_eq_embLL Rl))

end GlobalTheory.SeriesTie.ActProof

namespace GlobalTheory.SeriesTie
open Formalism.IndefR.Lev Formalism.L2.DIV
open scoped TensorProduct

theorem actRead_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → ActRead (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hU hW
  intro g κ hκ f x
  have hκ' := ActProof.isLift_transfer Rl j hp i b g κ hκ
  change (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 (D.nexp.actG i _ b g f))) x =
    (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * κ)
  rw [YS.act, Pi.smul_apply, Pi.smul_apply]
  congr 1
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 f = y
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearEquiv.map_zero, map_zero]; rfl
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, Pi.add_apply, hy, hz, map_add, Pi.add_apply]
  | tmul a f0 =>
    have hg : S.eG (S.eG.symm g) = g := S.eG.apply_symm_apply g
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evK_tmul, evK_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have h2 := ActProof.evW_rho Rl j hU hW YS v₀ (S.eG.symm g) κ (hg.symm ▸ hκ') (Subtype.val f0) x
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    change ρ.e i b _ * evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)) x = _
    rw [h2]
    erw [map_mul, map_inv₀, he]
    field_simp

end GlobalTheory.SeriesTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.SeriesTie

noncomputable section

namespace GlobalTheory.ChoiceAdm

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

theorem star_eq_conj (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

abbrev cnj (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem cnj_coe (x : 𝓞 D.host.E) : ((cnj D x : 𝓞 D.host.E) : D.host.E) = D.host.conj x := rfl

theorem isConjPl_of_lev {P P' : Pl D.host.E} (h : Lev.IsConjPl P P') : IsConjPl D.host P P' := by
  have hle : P.asIdeal ≤ P'.asIdeal.comap (cnj D) := fun c hc => by
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : cnj D c = c' := RingOfIntegers.ext (by rw [cnj_coe, h2, star_eq_conj])
    rw [Ideal.mem_comap, e]
    exact h1
  have heq := P.isMaximal.eq_of_le (Ideal.comap_ne_top _ P'.isPrime.ne_top) hle
  intro x y hxy
  have e : y = cnj D x := RingOfIntegers.ext hxy
  rw [e, ← Ideal.mem_comap, ← heq]

theorem not_lev_self {P : Pl D.host.E} (h : IsSplitPl D.host P) : ¬ Lev.IsConjPl P P := fun hc =>
  GlobalTheory.SeriesTie.ne_of_split h (isConjPl_of_lev hc) rfl

theorem exists_idem {P : Pl D.host.E} (h : IsSplitPl D.host P) : ∃ e, IsIdemAt e P := by
  refine GlobalTheory.MovedIdem.exists_isIdemAt P fun hP => ?_
  obtain ⟨x, hx, hy⟩ := h
  refine hy (cnj D x) rfl ?_
  rw [← hP]
  exact Ideal.subset_span ⟨x, hx, by
    change ((cnj D x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E)
    rw [cnj_coe, star_eq_conj]⟩

theorem lev_of_eq_cA {i j : Pl D.host.E} {a b : Formalism.L2.Theta.AE D} (ha : IsIdemAt a i) (hb : IsIdemAt b j)
    (e : a = cA D b) : Lev.IsConjPl j i := by
  have hc : Lev.IsConjPl j (GlobalTheory.IdemSupport.cP j) := fun c hc =>
    ⟨GlobalTheory.IdemSupport.cO D c, by
      show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) ∈ j.asIdeal
      rwa [show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) = c from RingOfIntegers.ext (star_star (c : D.host.E))], rfl⟩
  have h2 : IsIdemAt (cA D b) (GlobalTheory.IdemSupport.cP j) :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 j _ b hb hc
  rw [← e] at h2
  have hij : i = GlobalTheory.IdemSupport.cP j := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [ha.2 x hx, h2.2 x hx]
  rw [hij]
  exact hc

open Classical in
theorem splitSet_union {P H : Finset (Pl D.host.E)} (hP : SplitSet P) (hH : ∀ p ∈ H, ∃ e, IsIdemAt e p)
    (hc : ∀ p ∈ P ∪ H, ∀ p' ∈ P ∪ H, p ∈ H ∨ p' ∈ H → ¬ Lev.IsConjPl p p') : SplitSet (P ∪ H) := by
  classical
  have hid : ∀ p ∈ P ∪ H, IsIdemAt (idemAt p) p := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact hP.isIdemAt h
    · obtain ⟨e, he⟩ := hH p h
      rw [idemAt_eq he]
      exact he
  refine ⟨idem (P ∪ H), ⟨idemAt, hid, rfl⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  by_cases hh : i ∈ H ∨ j ∈ H
  · rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hid i hi).1 (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hid j hj).1) with e | e
    · exact absurd (lev_of_eq_cA (hid i hi) (hid j hj) e) (hc j hj i hi hh.symm)
    · exact e
  · push_neg at hh
    have hi' : i ∈ P := (Finset.mem_union.1 hi).resolve_right hh.1
    have hj' : j ∈ P := (Finset.mem_union.1 hj).resolve_right hh.2
    exact hP.mul_conj hi' hj'

end GlobalTheory.ChoiceAdm

end

namespace GlobalTheory.ChoiceAdm


open Classical in
theorem adm_half_of_good_of_split_disjoint : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good →
    ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)), (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) →
      Disjoint Q (X.S0 i) → (ρ.B i j b).admitted (half (ρ.ch i) Q) := by
  intro D N X ρ hρ i j b Q hsplit hdisj
  classical
  have hG := hρ.base i j b
  have hdeQ : (ρ.B i j b).de.Q = half (ρ.ch i) (X.pD i) := by rw [hρ.delta i j b]; rfl
  have deS0 : ∀ P ∈ (ρ.B i j b).de.Q, P ∈ X.S0 i := fun P hP => by
    rw [hdeQ] at hP
    exact X.primes_subset_exceptional i (mem_half.1 hP).1
  have PgS0 : ∀ P ∈ (ρ.B i j b).G.Pg, P ∈ X.S0 i := fun P hP => by
    obtain ⟨k, hk⟩ := hρ.Pg i j b P hP
    exact Finset.mem_coe.1 (X.placesOver_subset_exceptional i k hk)
  have hH : ∀ P ∈ half (ρ.ch i) Q, P ∉ X.S0 i := fun P hP h =>
    Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 h

  have hcS0 : ∀ P ∈ half (ρ.ch i) Q, ∀ P' ∈ X.S0 i, ¬ Lev.IsConjPl P P' ∧ ¬ Lev.IsConjPl P' P := by
    intro P hP P' hP'
    refine ⟨fun hc => hH P hP ?_, fun hc => hH P hP ?_⟩
    · exact hρ.goodSetup_badPlaces_conj i P' hP' P (GlobalTheory.GalChar.isConjPl_symm (isConjPl_of_lev hc))
    · exact hρ.goodSetup_badPlaces_conj i P' hP' P (isConjPl_of_lev hc)
  have hA : ∀ P ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q, P ∈ X.S0 i := fun P hP =>
    (Finset.mem_union.1 hP).elim (PgS0 P) (deS0 P)
  refine ⟨⟨⟨(ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q ∪ half (ρ.ch i) Q, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  · exact Finset.union_subset (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right
  · refine splitSet_union ?_ (fun p hp => exists_idem (hsplit p (mem_half.1 hp).1)) ?_
    · obtain ⟨P0, h1, h2, h3⟩ := hG.places.split
      exact h3.mono (Finset.union_subset h1 h2)
    · intro p hp p' hp' hh hc
      by_cases h1 : p ∈ half (ρ.ch i) Q
      · by_cases h2 : p' ∈ half (ρ.ch i) Q
        · by_cases e : p = p'
          · subst e
            exact not_lev_self (hsplit p (mem_half.1 h1).1) hc
          · exact ((hρ.ch i).pair p p' (isConjPl_of_lev hc) e).1 (mem_half.1 h1).2 (mem_half.1 h2).2
        · have : p' ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q := (Finset.mem_union.1 hp').resolve_right h2
          exact (hcS0 p h1 p' (hA p' this)).1 hc
      · have hpA : p ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q := (Finset.mem_union.1 hp).resolve_right h1
        have h2 : p' ∈ half (ρ.ch i) Q := hh.resolve_left h1
        exact (hcS0 p' h2 p (hA p hpA)).2 hc
  · refine Finset.disjoint_union_right.2 ⟨hG.places.disj, Finset.disjoint_left.2 fun p hp hq => hH p hq (PgS0 p hp)⟩
  · intro PP hPP PP' hPP'
    rcases hPP with h | h
    · exact hG.places.prime PP (Or.inl h) PP' hPP'
    · rcases Finset.mem_union.1 h with h | h
      · exact hG.places.prime PP (Or.inr h) PP' hPP'
      · refine hρ.goodSetup_count_eq_zero_off_badPlaces i PP' fun hS => ?_
        rcases hPP' with e | hc
        · exact hH PP h (e ▸ hS)
        · exact (hcS0 PP h PP' hS).1 hc
  · exact Finset.disjoint_left.2 fun p hp hq => hH p hq (deS0 p hp)

end GlobalTheory.ChoiceAdm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChosenPlacesAdmissibleGoodSetupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chosenPlaces_admissible_goodSetup : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)), (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) → Disjoint Q (X.S0 i) → (ρ.B i j b).admitted (half (ρ.ch i) Q) := by
  first | exact @GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint | exact GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint | (intros; apply GlobalTheory.ChoiceAdm.adm_half_of_good_of_split_disjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplit
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDetValue

open GlobalTheory.SplitHecke

section Local

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem valued_unit (u : (v.adicCompletionIntegers F)ˣ) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) u) = 1 := by
  by_contra hne
  exact (GlobalTheory.SplitUnif.mem_max v u).2 (lt_of_le_of_ne (u : v.adicCompletionIntegers F).2 hne) u.isUnit

theorem valued_irreducible {p : v.adicCompletionIntegers F} (hp : Irreducible p) :
    Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) p) = WithZero.exp (-1) := by
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  let p₀ : v.adicCompletionIntegers F := ⟨algebraMap F (Fv F v) t, GlobalTheory.SplitUnif.map_mem v _ t⟩
  have hp₀ : Valued.v (p₀ : Fv F v) = WithZero.exp (-1) := (hφ t).trans ht
  obtain ⟨w, hw⟩ := IsDiscreteValuationRing.associated_of_irreducible _ hp
    (GlobalTheory.SplitUnif.irreducible_of_valued v p₀ hp₀)
  have := congrArg (fun y : v.adicCompletionIntegers F => Valued.v (y : Fv F v)) hw
  change Valued.v ((p : Fv F v) * (w : v.adicCompletionIntegers F)) = Valued.v (p₀ : Fv F v) at this
  rw [map_mul, hp₀] at this
  have hw1 := valued_unit v w
  rw [← this]
  change _ = _ * Valued.v (algebraMap (v.adicCompletionIntegers F) (Fv F v) w)
  rw [hw1, mul_one]
  rfl

theorem card_residue_eq :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  have hφ : ∀ s : 𝓞 F, Valued.v (algebraMap F (Fv F v) s) = v.intValuation s := fun s =>
    (v.valuedAdicCompletion_eq_valuation' _).trans (HeightOneSpectrum.valuation_of_algebraMap v s)
  exact GlobalTheory.SplitUnif.card_residueField v (algebraMap F (Fv F v)) v (fun _ => rfl) fun s => by
    rw [hφ, HeightOneSpectrum.intValuation_lt_one_iff_mem]

end Local

section Chart

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

theorem chi_of_unit_gen (hπ : Chart e v π) {x d : (AE D)ˣ} (hx1 : (1 - e) * (x : AE D) = 1 - e)
    (hd1 : (1 - e) * (d : AE D) = 1 - e) {A : Type} [CommGroup A] {χ : (AE D)ˣ →* A}
    (hχ : ∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D →
      finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) {u : (Ov D v)ˣ}
    (h1 : π (d : AE D) = π (x : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u) : χ d = χ x := by
  have h3 : π ((x⁻¹ * d : (AE D)ˣ) : AE D) = algebraMap (Ov D v) (Fv D.host.F v) u := by
    rw [Units.val_mul, π.map_mul, h1, ← mul_assoc, ← π.map_mul, Units.inv_mul, π.map_one, one_mul]
  have h4 := hχ (x⁻¹ * d) ?_ ((hπ.2.2.2 _).2 ⟨u, h3.symm⟩) ((hπ.2.2.2 _).2 ⟨(u⁻¹ : (Ov D v)ˣ), ?_⟩)
  · rwa [χ.map_mul, χ.map_inv, inv_mul_eq_one, eq_comm] at h4
  · have h5 : (1 - e) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 - e := by
      conv_lhs => rw [← hx1, mul_assoc, Units.mul_inv, mul_one]
    rw [Units.val_mul, ← mul_assoc, h5, hd1]
  · rw [map_units_inv, map_units_inv, h3]

end Chart


set_option maxHeartbeats 1000000 in
theorem det_modulus_chi : ∀ (D : D7) (V : HSp D) (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ (k : ℕ) (α : GA D V), IsHeckeElt V e (ϖ : D.host.E) k α → ∀ k₁ ∈ Mult.locPart V (KsphC V ∅) e, ∀ k₂ ∈ Mult.locPart V (KsphC V ∅) e, ∀ z : (AE D)ˣ, IsDetAt e V (k₁ * α * k₂) z → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = (((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ k)⁻¹ ∧ ∀ (A : Type) [CommGroup A] (χ : (AE D)ˣ →* A), (∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D → finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) → χ z = χ x ^ k := by
  intro D V P e hP ϖ hϖ hϖ2 x hx k α hα k₁ hk₁ k₂ hk₂ z hz
  have he := hP.1
  obtain ⟨v, π, hπ⟩ := GlobalTheory.T.exists_place_chart_of_splitIdempotent e he
  obtain ⟨⟨p, hpϖ, hp⟩, hq⟩ := GlobalTheory.T.splitChart_uniformiser_and_residueCard e P v π hP hπ ϖ hϖ hϖ2
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_splitFrame_selfDualLattice_completion e v π he hπ V
  have st := GlobalTheory.T.mem_hyperspecial_iff_gInt_of_suppAt_split e v π he hπ V β hβ
  have hH : Hk (Ov D v) p k (rho V π β (k₁ * α * k₂)) := by
    rw [map_mul, map_mul]
    exact (GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π he hπ V β hβ (ϖ : D.host.E) p k α hpϖ hα).mul ((st _ hk₁.2).1 hk₁.1)
      ((st _ hk₂.2).1 hk₂.1)
  obtain ⟨u, hu⟩ := hH.2.2
  have hx1 : (1 - e) * (x : AE D) = 1 - e := by
    rw [hx]
    exact one_sub_mul_idem he.1 _
  have hx2 : π x = algebraMap (Ov D v) (Fv D.host.F v) p := by
    rw [hx, map_add π, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero, hpϖ]
  have hz1 : (1 - e) * (z : AE D) = 1 - e := by
    rw [hz]
    exact one_sub_mul_idem he.1 _
  have hz2 : π (z : AE D) = algebraMap (Ov D v) (Fv D.host.F v) (p ^ k * u) := by
    rw [rho_val, Matrix.det_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul] at hu
    rw [hz, map_add π, π.map_mul, π.map_sub, π.map_one, hπ.map_e he.1, one_mul, sub_self, add_zero]
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    exact hu
  refine ⟨?_, fun A _ χ hχ => ?_⟩
  · rw [GlobalTheory.SplitLinear.absFin_split D e v π he hπ z hz1, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    have e1 : ((Units.map π.toMonoidHom z : (Fv D.host.F v)ˣ) : Fv D.host.F v) = π (z : AE D) := rfl
    have e2 : Ideal.absNorm v.asIdeal = Ideal.absNorm P.asIdeal := by
      rw [← card_residue_eq, hq]
    have hv1 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) p) = WithZero.exp (-1) := valued_irreducible v hp
    have hv2 : Valued.v (algebraMap (Ov D v) (Fv D.host.F v) u) = 1 := valued_unit v u
    rw [e1, hz2, map_mul, map_mul, map_pow, map_pow, hv1, hv2, mul_one, e2,
      ← WithZero.exp_nsmul, WithZero.log_exp, nsmul_eq_mul, mul_neg_one, _root_.zpow_neg, zpow_natCast]
  · have h1 : π (z : AE D) = π ((x ^ k : (AE D)ˣ) : AE D) * algebraMap (Ov D v) (Fv D.host.F v) u := by
      rw [hz2, Units.val_pow_eq_pow_val, π.map_pow, hx2, ← RingHom.map_pow, ← RingHom.map_mul]
    have h2 : ∀ j : ℕ, (1 - e) * ((x ^ j : (AE D)ˣ) : AE D) = 1 - e := fun j => by
      induction j with
      | zero => rw [pow_zero, Units.val_one, mul_one]
      | succ j ih => rw [pow_succ, Units.val_mul, ← mul_assoc, ih, hx1]
    exact (chi_of_unit_gen hπ (h2 k) hz1 hχ h1).trans (χ.map_pow x k)

end GlobalTheory.SplitDetValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modulus_unramifiedChar_det_heckeDoubleCoset_split : ∀ (D : D7) (V : HSp D) (P : Pl D.host.E) (e : AE D), IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ x : (AE D)ˣ, (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) → ∀ (k : ℕ) (α : GA D V), IsHeckeElt V e (ϖ : D.host.E) k α → ∀ k₁ ∈ Mult.locPart V (KsphC V ∅) e, ∀ k₂ ∈ Mult.locPart V (KsphC V ∅) e, ∀ z : (AE D)ˣ, IsDetAt e V (k₁ * α * k₂) z → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D z = (((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ k)⁻¹ ∧ ∀ (A : Type) [CommGroup A] (χ : (AE D)ˣ →* A), (∀ y : (AE D)ˣ, (1 - e) * (y : AE D) = 1 - e → finPart D (e * (y : AE D)) ∈ intAE D → finPart D (e * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D → χ y = 1) → χ z = χ x ^ k := by
  first | exact @GlobalTheory.SplitDetValue.det_modulus_chi | exact GlobalTheory.SplitDetValue.det_modulus_chi | (intros; apply GlobalTheory.SplitDetValue.det_modulus_chi <;> assumption)
end
end
