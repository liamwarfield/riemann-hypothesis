module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMatrixOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselSecondBasePointCharacterTrivialDepthLattic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPower

@[expose] public section

attribute [-instance] UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete
  UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIntegralInvNegXi0
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.StairFrameFJ

private theorem isIntegral_sqrtMinusD' (D : D7) : IsIntegral ℤ D.host.sqrtMinusD := by
  refine IsIntegral.of_pow (n := 2) two_pos ?_
  have hsq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
    unfold Host.sqrtMinusD
    exact D.host.sqd_sq
  rw [hsq]
  refine IsIntegral.neg ?_
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := (D.host.d : ℤ)))

theorem isIntegral_inv_neg_xi0 (D : D7) : IsIntegral ℤ (-D.host.xi0)⁻¹ := by

  unfold Host.xi0
  rw [neg_div, neg_neg, one_div, inv_inv]
  refine IsIntegral.mul ?_ (isIntegral_sqrtMinusD' D)
  simpa using (isIntegral_algebraMap (R := ℤ) (A := D.host.E) (x := ((Ideal.absNorm D.host.ccK : ℕ) : ℤ)))

private theorem mem_integer_of_isIntegral_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {y : k} (hy : IsIntegral ℤ y) : y ∈ 𝒪[k] := by
  have h2 : IsIntegral 𝒪[k] y := hy.tower_top
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hz ▸ z.2

theorem exists_inv {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {x : D.host.E} (hx : x ≠ 0) (h : IsIntegral ℤ x⁻¹) :
    ∃ u : 𝒪[k], (u : k) * p.pr (incA D x) = 1 := by
  have hy : IsIntegral ℤ (p.pr (incA D x⁻¹)) := h.map ((p.pr.comp (incA D)).toIntAlgHom)
  refine ⟨⟨_, mem_integer_of_isIntegral_int hy⟩, ?_⟩
  show p.pr (incA D x⁻¹) * p.pr (incA D x) = 1
  rw [← map_mul, ← map_mul, inv_mul_cancel₀ hx, map_one, map_one]

theorem exists_frame : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : 𝒪[k]),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} ∧
  (∃ u : 𝒪[k], (u : k) * p.pr (incA D (-D.host.xi0)) = 1) ∧
  (∃ u : 𝒪[k], (u : k) * p.pr (incA D (star (-D.host.xi0))) = 1) ∧
  Function.Injective j ∧
  (∀ r i, β.b i (j r) = (ϖ : k) ^ (G.pl.depth sc v * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) ∧
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) := by
  unfold OnStd All
  intro D hq T L μ₀ hL sc G W M _ F _ σ h' v hv
  obtain ⟨k, _, _, _, _, p, hpv, hpe⟩ := GlobalTheory.LatticeMembershipValuation.exists_splitPoint_at_S0 G.pl hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  obtain ⟨β, j, hβ, hj, hcol, horth⟩ := GlobalTheory.LatticeMembershipValuation.exists_stairFrame (p := p) hq hL G hv (2 * σ + 2) (by omega) h'
    hpv hpe hϖ
  have hx0 : D.host.xi0 ≠ 0 := by
    exact GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hs : IsIntegral ℤ (star (-D.host.xi0))⁻¹ := by
    have h1 : IsIntegral ℤ (star (-D.host.xi0)⁻¹) :=
      (isIntegral_inv_neg_xi0 D).map ((starRingEnd D.host.E).toIntAlgHom)
    rwa [star_inv₀] at h1
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, p, β, j, ϖ, hpv, hpe, hβ,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ,
    exists_inv p (neg_ne_zero.2 hx0) (isIntegral_inv_neg_xi0 D),
    exists_inv p (star_ne_zero.2 (neg_ne_zero.2 hx0)) hs, hj, hcol, ?_⟩
  intro m hm r
  have hmr := horth m hm r
  have hf : (fun x => p.pr (incA D x)) = ⇑(p.pr.comp (incA D)) := rfl
  rw [hf, Matrix.map_mul, Matrix.mul_assoc] at hmr
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply] using hmr

end GlobalTheory.StairFrameFJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameLatticeFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameLatticeFunctional
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.DepthColumn

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul_right (p : GlobalTheory.FinPl.SplitPt D k) (x : k) (b : AE D) : p.sec x * b = p.sec (x * p.pr b) := by
  have h1 : p.sec x = p.e * p.sec x := by
    have := p.sec_pr (p.sec x)
    rwa [p.pr_sec] at this
  have h2 := p.sec_pr (p.sec x * b)
  rw [map_mul, p.pr_sec, ← mul_assoc, ← h1] at h2
  exact h2.symm

theorem sec_mem_idV (p : GlobalTheory.FinPl.SplitPt D k) {I : GlobalTheory.SeeSaw.FI D} {a : D.host.E} (ha : a ∈ I) (ha0 : a ≠ 0) {c : k}
    (hc : valuation k c ≤ valuation k (p.pr (incA D a))) : p.sec c ∈ GlobalTheory.SeeSaw.idV I p.v := by
  have h0 : p.pr (incA D a) ≠ 0 := (map_ne_zero_iff (p.pr.comp (incA D)) (p.pr.comp (incA D)).injective).2 ha0
  have key : ∀ y ∈ GlobalTheory.SeeSaw.idV (1 : GlobalTheory.SeeSaw.FI D) p.v, incA D a * y ∈ GlobalTheory.SeeSaw.idV I p.v := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, hαv, b, hb, rfl⟩ := hy
      rw [GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul]
      refine AddSubgroup.subset_closure ⟨α, hα, hαv, _, ?_, rfl⟩
      have := FractionalIdeal.mul_mem_mul (S := (𝓞 D.host.E)⁰) ha hb
      rwa [mul_one] at this
    | zero => rw [mul_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
    | neg a _ ha => rw [mul_neg]; exact neg_mem ha
  have hint : c / p.pr (incA D a) ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ hc zero_le'
  have h1 := key _ ((GlobalTheory.SeeSaw.idV_one_eq_intAt D p.v _).2 ⟨p.sec_mem_idAt _, (p.int_iff _).1 hint⟩)
  rwa [mul_comm, sec_mul_right, div_mul_cancel₀ _ h0] at h1

def prInt (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) :
    𝓞 D.host.E →+* 𝒪[k] :=
  ((p.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] fun x => p.pr_incA_int_mem he x

theorem coe_prInt (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (x : 𝓞 D.host.E) : (prInt p he x : k) = p.pr (incA D (x : D.host.E)) := rfl

theorem mem_iff_lt (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (x : 𝓞 D.host.E) : x ∈ PP.asIdeal ↔ valuation k (p.pr (incA D (x : D.host.E))) < 1 := by
  rw [p.mem_iff_val_lt he, ← p.prF_toEAf he]
  rfl

theorem val_eq_one (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    {x : 𝓞 D.host.E} (hx : x ∉ PP.asIdeal) : valuation k (p.pr (incA D (x : D.host.E))) = 1 :=
  le_antisymm (p.pr_incA_int_mem he x) (not_lt.1 fun h => hx ((mem_iff_lt p he x).2 h))

theorem prInt_mem_pow (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (n : ℕ) {x : 𝓞 D.host.E} (hx : x ∈ PP.asIdeal ^ n) : prInt p he x ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n := by
  have h1 : PP.asIdeal.map (prInt p he) ≤ IsLocalRing.maximalIdeal 𝒪[k] :=
    Ideal.map_le_iff_le_comap.2 fun y hy => Ideal.mem_comap.2
      ((GlobalTheory.FinPl.SplitPt.mem_max_iff_val_lt_one _).2 ((mem_iff_lt p he y).1 hy))
  have h2 := Ideal.mem_map_of_mem (prInt p he) hx
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem coord_mem_pow (p : GlobalTheory.FinPl.SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    {S : HSp D} {ι : Type} [Fintype ι] [DecidableEq ι] (β : GlobalTheory.FinPl.Frame p S ι) {L : Lat S}
    (hL : β.IsLat L (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k))) {𝔪 : Ideal (𝓞 D.host.E)} {n : ℕ}
    (h𝔪 : 𝔪 ≤ PP.asIdeal ^ n) {Y : Fin S.rank → AE D}
    (hY : Y ∈ GlobalTheory.FinPl.latMul S {a | a ∈ ((𝔪 : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)} L (· = p.v)) (r : ι) :
    ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n, (z : k) = (β.b' *ᵥ fun j => p.pr (Y j)) r := by
  induction hY using AddSubgroup.closure_induction with
  | mem Y hY =>
    obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hY
    obtain ⟨m, hm, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 D.host.E)⁰).1 ha
    set Y₀ : Fin S.rank → AE D := fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i) with hY₀
    have h0 : Y₀ ∈ latV S L (· = p.v) := AddSubgroup.subset_closure ⟨α, hα, hαv, 1, rfl, x, hx, rfl⟩
    have h1 := GlobalTheory.UpMem.smul_mem_latMul S {1} L (· = p.v) p.e (GlobalTheory.UpMem.finPart_e_int p) _ h0
    have h2 : (β.b' *ᵥ fun j => p.pr (Y₀ j)) ∈ Submodule.pi Set.univ fun _ : ι => (1 : Submodule 𝒪[k] k) := by
      rw [hL, Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec]
      simp only [p.sec_pr]
      exact h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (h2 r (Set.mem_univ r))
    refine ⟨prInt p he m * o, Ideal.mul_mem_right _ _ (prInt_mem_pow p he n (h𝔪 hm)), ?_⟩
    have e : (fun j => p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (algebraMap (𝓞 D.host.E) D.host.E m * x j))) =
        (prInt p he m : k) • fun j => p.pr (Y₀ j) := by
      funext j
      rw [Pi.smul_apply, smul_eq_mul, coe_prInt, ← map_mul, hY₀, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, one_mul]
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, ← ho, smul_eq_mul]
    rfl
  | zero => exact ⟨0, zero_mem _, by simp [Matrix.mulVec, dotProduct]⟩
  | add Y Y' _ _ h h' =>
    obtain ⟨z, hz, e⟩ := h
    obtain ⟨z', hz', e'⟩ := h'
    refine ⟨z + z', add_mem hz hz', ?_⟩
    push_cast
    rw [e, e', ← Pi.add_apply, ← Matrix.mulVec_add]
    congr 1
    funext j
    simp only [Pi.add_apply, map_add]
  | neg Y _ h =>
    obtain ⟨z, hz, e⟩ := h
    refine ⟨-z, neg_mem hz, ?_⟩
    push_cast
    rw [e, ← Pi.neg_apply, ← Matrix.mulVec_neg]
    congr 1
    funext j
    simp only [Pi.neg_apply, map_neg]

theorem pow_mem_pow_fr {I : GlobalTheory.SeeSaw.FI D} {a : D.host.E} (ha : a ∈ I) (n : ℕ) : a ^ n ∈ I ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact FractionalIdeal.one_mem_one _
  | succ n ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih ha

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem exists_mem_modul (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) (p : GlobalTheory.FinPl.SplitPt D k)
    (he : Formalism.L2.NTheta.IsIdemAt p.e (P.w v)) {ϖ : k} (hϖ : valuation k ϖ < 1) :
    ∃ m ∈ P.modul sc, m ≠ 0 ∧ valuation k ϖ ^ P.depth sc v ≤ valuation k (p.pr (incA D (m : D.host.E))) := by
  classical
  have hex : ∀ u ∈ P.S0, ∃ t ∈ (P.w u).asIdeal, t ≠ 0 ∧
      (if u = v then valuation k ϖ else 1) ≤ valuation k (p.pr (incA D (t : D.host.E))) := by
    intro u hu
    split_ifs with h
    · subst h
      obtain ⟨t, ht, ht2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self (P.w u).asIdeal (P.w u).ne_bot (P.w u).isPrime.ne_top 2 le_rfl)
      obtain ⟨⟨q, hq⟩, -⟩ := GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p _ he t 1 ht ht2
        fun h1 => (P.w u).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
      refine ⟨t, ht, fun h0 => ht2 (h0 ▸ zero_mem _), ?_⟩
      rw [hq]
      exact GlobalTheory.FinPl.SplitPt.val_le_unif q hϖ
    · have hne : P.w u ≠ P.w v := fun e => h (by rw [← P.under_w hu, e, P.under_w hv])
      obtain ⟨t, ht, ht'⟩ := Set.not_subset.1 fun hle : ((P.w u).asIdeal : Set (𝓞 D.host.E)) ⊆ (P.w v).asIdeal =>
        hne (GlobalTheory.IdemSupport.eq_of_le hle)
      exact ⟨t, ht, fun h0 => ht' (h0 ▸ zero_mem _), (val_eq_one p he ht').ge⟩
  choose! t ht ht0 htv using hex
  refine ⟨∏ u ∈ P.S0, t u ^ P.depth sc u, Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow (ht u hu) _,
    Finset.prod_ne_zero_iff.2 fun u hu => pow_ne_zero _ (ht0 u hu), ?_⟩
  rw [← coe_prInt p he, map_prod]
  push_cast
  rw [map_prod]
  calc valuation k ϖ ^ P.depth sc v = ∏ u ∈ P.S0, (if u = v then valuation k ϖ else 1) ^ P.depth sc u := by
        rw [Finset.prod_eq_single_of_mem v hv fun u _ h => by rw [if_neg h, one_pow], if_pos rfl]
    _ ≤ _ := Finset.prod_le_prod' fun u hu => by
        rw [map_pow, SubmonoidClass.coe_pow, map_pow, coe_prInt]
        exact pow_le_pow_left' (htv u hu) _

theorem sec_mem_stairId {μ0 : T} (hq : OffQ D) (hL : L.Is μ0) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    (p : GlobalTheory.FinPl.SplitPt D k) (hpv : p.v = v) (he : Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v)) {ϖ : k} (hϖ : valuation k ϖ < 1)
    (c : ℕ) (q : Fin c) :
    p.sec (ϖ ^ (G.pl.depth sc v * (q.1 + 1))) ∈ GlobalTheory.SeeSaw.idV (stairId (G.pl.stA sc) (G.pl.stAbar sc) c q) v := by
  classical
  have hw : G.pl.w v ∈ G.pl.W0 := (GlobalTheory.DepthFix.mem_orthogonal_frame_iff G).2 ⟨v, hv, rfl⟩
  have hb := Good.badInt_notMem hL (G := G) (t := μ0) hq (fun P hP => absurd
    (show (L.xiH μ0).UnrAt P by rw [hL.xi_base]; exact fun x _ => rfl) ((hL.Q_ram μ0 P).2 (Or.inl hP)))
    (Finset.mem_union_left _ hw)
  have h2q : ((D.host.QS * D.host.q : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal :=
    fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro _ rfl))
  have hN : ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal :=
    fun h => hb (GlobalTheory.HalfCompare.mem_of_dvd h (Dvd.intro_left _ rfl))
  have hn : ((Ideal.absNorm D.host.𝔟 : ℕ) : 𝓞 D.host.E) ∉ (G.pl.w v).asIdeal := fun hm => by
    obtain ⟨l, hl, hP⟩ := GlobalTheory.HalfCompare.exists_prime_under (G.pl.w v)
    exact h2q ((hP _).2 ((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hl).1 ((hP _).1 hm)))
  obtain ⟨m, hm, hm0, hmv⟩ := exists_mem_modul (sc := sc) G.pl hv p he hϖ
  have h1 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  have h2 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := ne_zero_of_conj h1.1 h1.2
  have hmb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    intro h
    have h4 := h2.1
    rw [Places.stA, h, _root_.inv_zero, mul_zero] at h4
    exact h4 rfl
  set N : 𝓞 D.host.E := ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) with hNdef
  set n : 𝓞 D.host.E := ((Ideal.absNorm D.host.𝔟 : ℕ) : 𝓞 D.host.E) with hndef
  have hA : (N : D.host.E) ∈ G.pl.stA sc := by
    have e1 : (1 : D.host.E) ∈ ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ :=
      (FractionalIdeal.mem_inv_iff hmb).2 fun y hy => by
        rw [one_mul]; exact FractionalIdeal.coeIdeal_le_one hy
    have := FractionalIdeal.mul_mem_mul (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.normCc_mem_AA D) e1
    rw [mul_one] at this
    simpa [hNdef, Places.stA] using this
  have hB : ((n * m : 𝓞 D.host.E) : D.host.E) ∈ (G.pl.stAbar sc)⁻¹ := by
    have e1 : (n : D.host.E) ∈ (D.host.AAbar : GlobalTheory.SeeSaw.FI D)⁻¹ :=
      (FractionalIdeal.mem_inv_iff hAb).2 fun y hy => by
        obtain ⟨o, ho⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem _) ((h1.2 y).1 hy)
        refine (FractionalIdeal.mem_one_iff _).2 ⟨GlobalTheory.IdemSupport.cO D o, ?_⟩
        change star (algebraMap _ D.host.E o) = _
        rw [ho, star_mul', star_star, star_natCast, mul_comm]
        simp [hndef]
    rw [Places.stAbar, mul_inv, inv_inv]
    push_cast
    exact FractionalIdeal.mul_mem_mul e1 (FractionalIdeal.mem_coeIdeal_of_mem _ hm)
  have ha : ((N ^ (c - q.1) * (n * m) ^ (q.1 + 1) : 𝓞 D.host.E) : D.host.E) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) c q := by
    rw [stairId, ← inv_pow, RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_pow]
    exact FractionalIdeal.mul_mem_mul (pow_mem_pow_fr hA _) (pow_mem_pow_fr hB _)
  have hN0 : N ≠ 0 := fun h => hN (h ▸ zero_mem _)
  have hn0 : n ≠ 0 := fun h => hn (h ▸ zero_mem _)
  subst hpv
  refine sec_mem_idV p ha (fun h => ?_) ?_
  · exact mul_ne_zero (pow_ne_zero _ hN0) (pow_ne_zero _ (mul_ne_zero hn0 hm0)) (RingOfIntegers.coe_eq_zero_iff.1 h)
  · rw [← coe_prInt p he]
    simp only [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, coe_prInt, val_eq_one p he hN,
      val_eq_one p he hn, one_pow, one_mul, pow_mul]
    exact pow_le_pow_left' hmv _

theorem col_eq {S S₀ U : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Mx D U.rank ρ) (q : Fin ρ) :
    (fun j => x j q) = d.extX U x *ᵥ fun i => d.jX i q := by
  rw [HypDec.extX_apply, ← Matrix.mulVec_mulVec]
  have e : (d.pX *ᵥ fun i => d.jX i q) = fun i => (d.pX * d.jX) i q := rfl
  rw [e, HypDec.pX_jX]
  funext j
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]

theorem col_mem_depth : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k)
    (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank)) (ϖ : 𝒪[k]),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} →
  ∀ a ∈ (pcFB W F σ h h').A₁, ∀ (q : Fin (σ + 1)) i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) = (ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1) *
      (β.b' *ᵥ fun j => p.pr (a j q)) i := by
  intro D hq T L μ0 hL sc G W M _ F hF σ h h' v hv k _ _ _ _ p β ϖ hpv he hlat hmax a ha q i
  obtain ⟨e, hE, -⟩ := W.cosVec_is
  obtain ⟨hc, hJ, -⟩ := hF.hJ (σ + 1) h
  have hw : G.pl.w v ∈ G.pl.W0 := (GlobalTheory.DepthFix.mem_orthogonal_frame_iff G).2 ⟨v, hv, rfl⟩
  have hpe : p.pr e = 1 := by
    have := congrArg p.pr (GlobalTheory.DiagLiftFix.idemSum_mul hE hw he)
    rwa [map_mul, GlobalTheory.FrameAt.pr_e, mul_one] at this
  have hϖ : valuation k (ϖ : k) < 1 :=
    (GlobalTheory.FinPl.SplitPt.mem_max_iff_val_lt_one _).1 (hmax ▸ Ideal.mem_span_singleton_self ϖ)
  have hξ : p.pr (incA D (-D.host.xi0)) ≠ 0 :=
    (map_ne_zero_iff (p.pr.comp (incA D)) (p.pr.comp (incA D)).injective).2 (neg_ne_zero.2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  set s : k := (ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1) with hs
  have hy : p.sec s • (fun j => (F.dJ (σ + 1) h).jX j q) =
      fun j => p.sec ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1))) *
        incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a j ⟨q.1, by omega⟩) := by
    funext j
    have e1 : p.sec s * incA D ((-D.host.xi0) ^ (q.1 + 1)) = p.sec ((ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1))) := by
      rw [sec_mul_right, map_pow, map_pow, hs, mul_assoc, ← mul_pow, inv_mul_cancel₀ hξ, one_pow, mul_one]
    simp only [Pi.smul_apply, smul_eq_mul, HypDec.jX, GlobalTheory.MixModel.rat, hJ, colsOf, Matrix.map_apply, map_mul]
    rw [← mul_assoc, e1]
    rfl
  have hΛ : G.Λ (.grid (2 * σ + 2 + 1) 0) = (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).lat
      (G.Λ (.core (2 * (σ + 1) + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)) :=
    G.sp.colLat _ _ _
  have hmem : p.sec s • (fun j => (F.dJ (σ + 1) h).jX j q) ∈
      latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v) := by
    rw [hy, hΛ]
    exact (GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v _).1.2
      (sec_mem_stairId hq hL G hv p hpv he hϖ _ _)
  have hu : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a ∈ latRow G (2 * σ + 2) := ha
  have hY := GlobalTheory.DepthRowLem.mulVec_mem_latMul _ (hu.2 e hE) hmem
  have hle : G.pl.modul sc ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := Ideal.prod_le_inf.trans (Finset.inf_le hv)
  subst hpv
  obtain ⟨z, hz, hz'⟩ := coord_mem_pow p he β hlat hle hY i
  refine ⟨z, hz, hz'.trans ?_⟩
  have e2 := col_eq (U := G.V (.grid (2 * σ + 2) 0)) (F.dJ (σ + 1) h) a q
  have e4 : s * (β.b' *ᵥ fun j => p.pr (a j q)) i = (β.b' *ᵥ (s • fun j => p.pr (a j q))) i := by
    rw [Matrix.mulVec_smul]
    rfl
  rw [e4]
  refine congrArg (fun y => (β.b' *ᵥ y) i) (funext fun j => ?_)
  have e3 : ((e • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a) *ᵥ (p.sec s • fun j => (F.dJ (σ + 1) h).jX j q)) j =
      e * (p.sec s * a j q) := by
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, ← e2]
    rfl
  refine (congrArg p.pr e3).trans ?_
  rw [map_mul, map_mul, hpe, p.pr_sec, one_mul]
  rfl

end GlobalTheory.DepthColumn

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFrameLatticeFunctionalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_frame_lattice_functional : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k)
    (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank)) (ϖ : 𝒪[k]),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} →
  ∀ a ∈ (pcFB W F σ h h').A₁, ∀ (q : Fin (σ + 1)) i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) = (ϖ : k) ^ (G.pl.depth sc v * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1) *
      (β.b' *ᵥ fun j => p.pr (a j q)) i := by
  first | exact @GlobalTheory.DepthColumn.col_mem_depth | exact GlobalTheory.DepthColumn.col_mem_depth | (intros; apply GlobalTheory.DepthColumn.col_mem_depth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FunctionalEquationLocalLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.ConjClause

open GlobalTheory.FinPl (SplitPt Frame)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_int (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w) {a : AE D}
    (ha : finPart D a ∈ intAE D) : p.pr a ∈ 𝒪[k] := by
  have h := p.val_prF_le_one he ⟨_, GlobalTheory.IdemRes.toEAf_mem_of_finPart ha⟩
  rw [p.prF_toEAf] at h
  exact h

theorem pr_tmul_int (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (b : 𝓞 D.host.E) :
    p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (b : D.host.E)) ∈ 𝒪[k] :=
  pr_int p he (AddSubgroup.subset_closure ⟨α, hα, b, rfl⟩)

def prInt (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w) :
    𝓞 D.host.E →+* 𝒪[k] :=
  ((p.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] fun z => by
    have h := p.val_prF_le_one he (Formalism.L2.DIV.oToS D.host.F D.host.E z)
    have e : p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E z : EAf D) = p.pr (incA D (z : D.host.E)) :=
      p.prF_toEAf he (incA D (z : D.host.E))
    rw [e] at h
    exact h

theorem mem_iff_prInt (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    (z : 𝓞 D.host.E) : z ∈ w.asIdeal ↔ prInt p he z ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
  have e : p.prF he (Formalism.L2.DIV.oToS D.host.F D.host.E z : EAf D) = p.pr (incA D (z : D.host.E)) :=
    p.prF_toEAf he (incA D (z : D.host.E))
  rw [p.mem_iff_val_lt he, e, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rfl

theorem exists_mem_pow (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {x : D.host.E} {n : ℕ} (hx : w.valuation D.host.E x ≤ WithZero.exp (-(n : ℤ))) :
    ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n, (z : k) = p.pr (incA D x) := by
  have h1 : w.valuation D.host.E x ≤ 1 := hx.trans (by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  obtain ⟨a, s, has⟩ := w.exists_primeCompl_mul_eq_of_integer x h1
  have hs : w.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E s) = 1 := by
    rw [w.valuation_of_algebraMap, w.intValuation_eq_one_iff]; exact s.2
  have ha : a ∈ w.asIdeal ^ n := by
    have h2 := congrArg (w.valuation D.host.E) has
    rw [map_mul, hs, mul_one, w.valuation_of_algebraMap] at h2
    rw [← w.intValuation_le_pow_iff_mem, ← h2]
    exact hx
  have hu : IsUnit (prInt p he s) := by
    by_contra h
    exact s.2 ((mem_iff_prInt p he s).2 h)
  obtain ⟨u, hu⟩ := hu
  have hle : Ideal.map (prInt p he) (w.asIdeal ^ n) ≤ IsLocalRing.maximalIdeal 𝒪[k] ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun z hz => Ideal.mem_comap.2 ((mem_iff_prInt p he z).1 hz)) n
  refine ⟨prInt p he a * ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]), Ideal.mul_mem_right _ _ (hle (Ideal.mem_map_of_mem _ ha)), ?_⟩
  have e1 : ((prInt p he a : 𝒪[k]) : k) = p.pr (incA D x) * ((u : 𝒪[k]) : k) := by
    rw [hu]
    change (p.pr.comp (incA D)) (algebraMap _ _ a) = (p.pr.comp (incA D)) x * (p.pr.comp (incA D)) (algebraMap _ _ s.1)
    rw [← map_mul, has]
  have e2 : ((u : 𝒪[k]) : k) * (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  rw [Subring.coe_mul, e1, mul_assoc, e2, mul_one]

theorem tmul_eq' (α : AF D.host.F) (x : D.host.E) :
    (α ⊗ₜ[D.host.F] x : AE D) = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D x := by
  change _ = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem pair_int (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {S : HSp D} {Λ : Lat S} (hΛ : IsSelfDualC S Λ) {t : Fin S.rank → D.host.E} (ht : t ∈ Λ) {P : GlobalTheory.FinPl.Pl D → Prop}
    {y : Fin S.rank → AE D} (hy : y ∈ latV S Λ P) :
    (∑ l, ∑ j, p.pr (incA D (star (t j))) * p.pr (incA D (S.gram j l)) * p.pr (y l)) ∈ 𝒪[k] := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    obtain rfl : a = 1 := ha
    obtain ⟨b, hb⟩ := (hΛ.2 x).1 hx t ht
    convert pr_tmul_int p he hα b using 1
    rw [hb, tmul_eq', Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [one_mul, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    rw [tmul_eq' _ (x _), map_mul]
    ring
  | zero => simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    simp only [Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  | neg x _ hx =>
    convert neg_mem hx using 1
    simp only [Pi.neg_apply, map_neg, mul_neg, Finset.sum_neg_distrib]

theorem pair_col_int (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {S : HSp D} {Λ : Lat S} (hΛ : IsSelfDualC S Λ) {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    (hβ : β.IsLat Λ (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k))) {t : Fin S.rank → D.host.E} (ht : t ∈ Λ) (i : n) :
    ((fun j => p.pr (incA D (star (t j)))) ᵥ* (S.gram.map (fun c => p.pr (incA D c)) * β.b)) i ∈ 𝒪[k] := by
  have h1 := (hβ (Pi.single i 1)).1 fun l _ => by
    by_cases h : l = i
    · subst h; rw [Pi.single_eq_same]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne h]; exact zero_mem _
  convert pair_int p he hΛ ht h1 using 1
  rw [Finset.sum_comm]
  simp only [p.pr_sec, mulVec_single_one, vecMul, dotProduct, Matrix.mul_apply, map_apply, Finset.mul_sum, mul_assoc]
  rfl

def rowVal {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {a b : ℕ} {n : Type} (ε : Fin b → A) (M : Matrix (Fin a) n R)
    (i : n) : Matrix (Fin a) (Fin b) A →+ R where
  toFun u := ((fun j => f (∑ m, u j m * ε m)) ᵥ* M) i
  map_zero' := by simp [vecMul, dotProduct]
  map_add' x y := by
    simp only [vecMul, dotProduct, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem vecMul_const_mul {R : Type} [CommRing R] {a : ℕ} {n : Type} (x : R) (g : Fin a → R) (M : Matrix (Fin a) n R) (i : n) :
    ((fun j => x * g j) ᵥ* M) i = x * (g ᵥ* M) i := by
  simp only [vecMul, dotProduct, Finset.mul_sum, mul_assoc]

theorem comp_mul_three {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (g : A →+* A) {x y t x' y' t' : A}
    (hx : g x = x') (hy : g y = y') (ht : g t = t') : f x' * f y' * f t' = (f.comp g) (x * (y * t)) := by
  rw [RingHom.comp_apply, g.map_mul, g.map_mul, hx, hy, ht, f.map_mul, f.map_mul, mul_assoc]

theorem rowVal_rank_one {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (g : A →+* A) {a b : ℕ} {n : Type}
    {u : Matrix (Fin a) (Fin b) A} {ε : Fin b → A} {x y x' y' : A} {t t' : Fin a → A}
    (hu : ∀ j, ∑ m, u j m * ε m = x * (y * t j)) (hx : g x = x') (hy : g y = y') (ht : ∀ j, g (t j) = t' j)
    (M : Matrix (Fin a) n R) (i : n) :
    f x' * f y' * ((fun j => f (t' j)) ᵥ* M) i = rowVal (f.comp g) ε M i u := by
  rw [← vecMul_const_mul]
  refine congrArg (fun g => (g ᵥ* M) i) (funext fun j => ?_)
  rw [hu]
  exact comp_mul_three f g hx hy (ht j)

theorem rowVal_col {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (g : A →+* A) {a b ρ : ℕ} {n : Type}
    {u : Matrix (Fin a) (Fin b) A} {j : Matrix (Fin b) (Fin ρ) A} {y : Matrix (Fin a) (Fin ρ) A} (hy : y = u * j) {q : Fin ρ}
    {x x' : A} {N : ℕ} {ε : Fin b → A} (hj : ∀ m, j m q = x ^ N * ε m) (hx : g x = x') (M : Matrix (Fin a) n R) (i : n) :
    ((fun l => f (g (∑ m, u l m * ε m))) ᵥ* M) i * f x' ^ N = ((fun l => f (g (y l q))) ᵥ* M) i := by
  rw [mul_comm, ← vecMul_const_mul]
  refine congrArg (fun g => (g ᵥ* M) i) (funext fun l => ?_)
  rw [← hx, ← map_pow, ← map_pow, ← map_mul, ← map_mul, hy, Matrix.mul_apply, Finset.mul_sum]
  simp only [hj, mul_left_comm]


set_option maxHeartbeats 1000000 in
theorem functional_mem (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e w)
    {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {Λ : Lat T} (hΛ : IsSelfDualC T Λ) {n : Type} [Fintype n] [DecidableEq n]
    (β : Frame p T n) (hβ : β.IsLat Λ (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)))
    (ε : Fin S.rank → D.host.E) (J : Ideal 𝒪[k])
    (hJ : ∀ c ∈ D.host.AA, ∀ s ∈ LS, ∃ z ∈ J, (z : k) = p.pr (incA D (star (c * ∑ m, (∑ l, star (s l) * S.gram l m) * ε m))))
    {P : GlobalTheory.FinPl.Pl D → Prop} {u : WO S T} (hu : u ∈ latO S T LS (Λ : Set _) P) (i : n) :
    ∃ z ∈ J, (z : k) = ((fun j => p.pr (cA D (∑ m, u j m * incA D (ε m)))) ᵥ*
      (T.gram.map (fun c => p.pr (incA D c)) * β.b)) i := by
  change ∃ z ∈ J, (z : k) = rowVal (p.pr.comp (cA D)) (fun m => incA D (ε m))
    (T.gram.map (fun c => p.pr (incA D c)) * β.b) i u
  induction hu using AddSubgroup.closure_induction with
  | mem u hu =>
    obtain ⟨α, hα, -, c, hc, s, hs, t, ht, rfl⟩ := hu
    obtain ⟨z, hz, hz'⟩ := hJ c hc s hs
    have h1 : p.pr (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ 𝒪[k] := by
      have h := pr_tmul_int p he hα 1
      rwa [RingOfIntegers.coe_eq_algebraMap, map_one] at h
    refine ⟨⟨_, h1⟩ * z * ⟨_, pair_col_int p he hΛ β hβ ht i⟩,
      J.mul_mem_right _ (J.mul_mem_left _ hz), ?_⟩
    have e : ∀ j, (∑ m, (pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t j * ∑ l, star (s l) * S.gram l m) : AE D) * incA D (ε m)) =
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) *
          (incA D (c * ∑ m, (∑ l, star (s l) * S.gram l m) * ε m) * incA D (t j)) := fun j => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, Finset.mul_sum, Finset.sum_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [tmul_eq', mul_assoc, ← map_mul]
      congr 2
      ring
    have e1 : cA D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) = pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E) := by
      change pairA D.host.F 0 α ⊗ₜ[D.host.F] (star (1 : D.host.E)) = _
      rw [star_one]
    have e2 : ∀ x, cA D (incA D x) = incA D (star x) := fun _ => rfl
    rw [Subring.coe_mul, Subring.coe_mul, hz']
    exact rowVal_rank_one p.pr (cA D) (ε := fun m => incA D (ε m))
      (u := Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ l, star (s l) * S.gram l j)) (t := fun j => incA D (t j)) (t' := fun j => incA D (star (t j))) e e1
      (e2 (c * ∑ m, (∑ l, star (s l) * S.gram l m) * ε m)) (fun j => e2 (t j)) _ i
  | zero => exact ⟨0, zero_mem _, (map_zero _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨z, hz, hz'⟩ := hx
    obtain ⟨z', hy, hy'⟩ := hy
    refine ⟨z + z', add_mem hz hy, ?_⟩
    rw [Subring.coe_add, hz', hy']
    exact (AddMonoidHom.map_add _ _ _).symm
  | neg x _ hx =>
    obtain ⟨z, hz, hz'⟩ := hx
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [Subring.coe_neg, hz']
    exact (AddMonoidHom.map_neg _ _).symm

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem valuation_stair {μ₀ : T} (hL : L.Is μ₀) (hq : OffQ D) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    {c : ℕ} (r : Fin c) {a x : D.host.E} (ha : a ∈ D.host.AA) (hx : x ∈ stairId (G.pl.stA sc) (G.pl.stAbar sc) c r) :
    (G.pl.w v).valuation D.host.E (star a * x) ≤ WithZero.exp (-((G.pl.depth sc v * (r.1 + 1) : ℕ) : ℤ)) := by
  classical
  have hw : G.pl.w v ∈ G.pl.W0 := by
    unfold Places.W0
    convert Finset.mem_image_of_mem G.pl.w hv
  have hloc : G.pl.w v ∈ locPl G μ₀ := Finset.mem_union_left _ hw
  have hb := Good.badInt_notMem hL (G := G) (t := μ₀) hq (fun P hP => absurd
    (show (L.xiH μ₀).UnrAt P by rw [hL.xi_base]; exact fun x _ => rfl) ((hL.Q_ram μ₀ P).2 (Or.inl hP))) hloc
  obtain ⟨c1, c2⟩ := count_AA_AAbar _ hb
  obtain ⟨n1, n2⟩ := GlobalTheory.SecondBaseChar.st_ne (sc := sc) G.pl
  obtain ⟨-, m1, m2⟩ := GlobalTheory.SecondBaseChar.ideals_ne D
  have d1 : FractionalIdeal.count D.host.E (G.pl.w v) (G.pl.stA sc) = 0 := by
    rw [Places.stA, FractionalIdeal.count_mul _ _ m1 (right_ne_zero_of_mul n1), FractionalIdeal.count_inv, c1,
      count_modulBar G hloc, neg_zero, add_zero]
  have d2 : FractionalIdeal.count D.host.E (G.pl.w v) (G.pl.stAbar sc) = -(G.pl.depth sc v : ℤ) := by
    rw [Places.stAbar, FractionalIdeal.count_mul _ _ m2 (right_ne_zero_of_mul n2), FractionalIdeal.count_inv, c2,
      count_modul, cosExp, if_pos hw, G.pl.under_w hv, zero_add]
  have h1 := GroundTheory.Global.valuation_le_of_mem_fractionalIdeal (G.pl.w v) hx
  rw [count_stairId n1 n2, d1, d2] at h1
  have h2 := GroundTheory.Global.valuation_le_of_mem_fractionalIdeal (G.pl.w v)
    (((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.2 (star a)).2 (by rwa [star_star]))
  rw [c2, neg_zero, WithZero.exp_zero] at h2
  rw [map_mul]
  refine (mul_le_mul' h2 h1).trans_eq ?_
  rw [one_mul]
  congr 1
  push_cast
  ring

theorem star_pair {B : HSp D} {c : ℕ} (a : Matrix (Fin B.rank) (Fin c) D.host.E) (s : Fin B.rank → D.host.E) (q : Fin c) :
    star (∑ m, (∑ l, star (s l) * (negSp B).gram l m) * a m q) = -((aᴴ * B.gram) *ᵥ s) q := by
  have hG : ∀ l m, star (B.gram l m) = B.gram m l := fun l m => congrFun (congrFun (gram_conjTranspose B) m) l
  simp only [negSp_gram, Matrix.neg_apply, star_sum, star_mul', star_star, star_neg, hG, mulVec, dotProduct, Matrix.mul_apply,
    conjTranspose_apply, Finset.sum_mul, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem functional_col {μ₀ : T} (hL : L.Is μ₀) (hq : OffQ D) (G : GridData L sc) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ G.pl.S0)
    (p : SplitPt D k) (he : Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v)) {A B B₀ S : HSp D} {c ρ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1))
    (Λ₀ : Lat A) (y : HypDec B B₀ ρ) (hy : IsAuxiliaryVectorWittDec d y) {LB : Lat B}
    (hB : LB = d.lat Λ₀ (stairId (G.pl.stA sc) (G.pl.stAbar sc) c)) {Λ : Lat S} (hΛ : IsSelfDualC S Λ)
    {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n)
    (hβ : β.IsLat Λ (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k))) {a : Mx D S.rank ρ}
    (ha : y.extX S a ∈ latO (negSp B) S (LB : Set _) (Λ : Set _) fun _ => True) (q : Fin ρ) (i : n) :
    ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ (G.pl.depth sc v * (c - q.1)),
      (z : k) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) =
        ((fun j => p.pr (cA D (a j q))) ᵥ* (S.gram.map (fun c => p.pr (incA D c)) * β.b)) i := by
  obtain ⟨hc, hE, -⟩ := hy
  subst hB
  have hq1 := q.2
  let r : Fin c := ⟨q.1, by omega⟩
  have hr : r.rev.1 + 1 = c - q.1 := by rw [Fin.val_rev]; change _ - (q.1 + 1) + 1 = _; omega
  have hrev : r.rev.rev ≠ r.rev := fun e => by
    have := congrArg (fun t : Fin c => t.1 + 1) e
    simp only [Fin.rev_rev] at this
    rw [hr] at this
    change q.1 + 1 = _ at this
    omega
  obtain ⟨z, hz, hz'⟩ := functional_mem p he hΛ β hβ (S := negSp B) (fun m => d.a m r)
    (IsLocalRing.maximalIdeal 𝒪[k] ^ (G.pl.depth sc v * (c - q.1))) (fun a ha s hs => by
      have h1 := GlobalTheory.SecondBaseChar.coef_mem d _ _ r.rev hrev hs
      rw [Fin.rev_rev] at h1
      have h2 := valuation_stair hL hq G hv r.rev ha h1
      rw [hr, ← Valuation.map_neg, ← mul_neg, ← star_pair d.a s r, ← star_mul'] at h2
      exact exists_mem_pow p he h2) ha i
  refine ⟨z, hz, ?_⟩
  have e1 : a = (y.extX S a : Mx D _ _) ⬝ y.jX := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have e2 : ∀ m, y.jX m q = incA D (-D.host.xi0) ^ (q.1 + 1) * incA D (d.a m r) := fun m => by
    rw [← (incA D).map_pow, ← (incA D).map_mul]
    exact congrArg (incA D) (congrFun (congrFun hE m) q)
  have e3 : cA D (incA D (-D.host.xi0)) = incA D (star (-D.host.xi0)) := rfl
  exact (congrArg (· * _) hz').trans (rowVal_col p.pr (cA D) e1 e2 e3 _ i)

theorem functional_equation_local_lattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.FinPl.SplitPt D k)
    (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank)) (ϖ : 𝒪[k]),
  p.v = v → Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) →
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) →
  IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} →
  ∀ a ∈ (pcFB W F σ h h').A₁, ∀ (q : Fin (σ + 1)) i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v,
    (z : k) * (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) =
      ((fun j => p.pr (cA D (a j q))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) i := by
  intro D hq T L μ₀ hL sc G W M _ F hF σ h h' v hv k _ _ _ _ p β ϖ _ he hβ hϖ a ha q i
  have hsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  obtain ⟨z, hz, hz'⟩ := functional_col hL hq G hv p he _ _ _ (hF.hJ (σ + 1) h)
    (G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)) hsd β hβ (a := a) ha.1 q i
  have hq1 := q.2
  have e : 2 * (σ + 1) + 1 - 1 - q.1 = 2 * σ + 1 - q.1 + 1 := by omega
  rw [e, mul_add, mul_one, pow_add, hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton_mul] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  refine ⟨y, hϖ ▸ hy, Eq.trans ?_ hz'⟩
  rw [Subring.coe_mul, SubmonoidClass.coe_pow, mul_comm (y : k)]

end GlobalTheory.ConjClause

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameDiagonal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem GlobalTheory.FrameFB.frame_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b = ι a → a = Fin.last σ ∧ b = Fin.last σ) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ*
    ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcFB W F σ h h').A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨k, _, _, _, _, p, β, j, ϖ, hpv, hid, hlat, hmax, ⟨u₁, hu₁⟩, ⟨u₂, hu₂⟩, hj, hcol, hperp⟩ :=
    GlobalTheory.StairFrameFJ.exists_frame D hq T L μ0 hL sc G W M hM F hF σ h' v hv
  have hϖ : (ϖ : k) ≠ 0 := by
    intro h0
    have h0' : ϖ = 0 := Subtype.ext h0
    have : IsLocalRing.maximalIdeal 𝒪[k] = ⊥ := by rw [hmax, h0', Ideal.span_singleton_eq_bot.2 rfl]
    exact IsDiscreteValuationRing.not_a_field _ this
  obtain ⟨hs, ht⟩ := GlobalTheory.FrameScale.clauses D hq T L μ0 hL sc G W M hM F hF σ h' k p β j (ϖ : k) (G.pl.depth sc v) hϖ hj hcol hperp
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, p, β,
    fun q => j ⟨q.1, by omega⟩, fun q => j ⟨2 * σ - q.1, by omega⟩, _, _, hpv, hid, hlat, ?_, ?_, ?_, hs, ht, ?_⟩
  · intro a b hab
    have := hj hab
    exact Fin.ext (by simpa using congrArg Fin.val this)
  · intro a b hab
    have := congrArg Fin.val (hj hab)
    simp at this
    exact Fin.ext (by omega)
  · intro a b hab
    have := congrArg Fin.val (hj hab)
    simp at this
    constructor <;> exact Fin.ext (by simp; omega)
  · intro a ha
    have hu2 : (p.pr (incA D (star (-D.host.xi0)))) ≠ 0 := right_ne_zero_of_mul_eq_one hu₂
    refine ⟨fun q i => ?_, fun q i => ?_⟩
    · obtain ⟨z, hz, hz'⟩ := GlobalTheory.T.split_frame_lattice_functional D hq T L μ0 hL sc G W M hM F hF σ h h' v hv k p β ϖ hpv hid hlat hmax a ha q i
      exact ⟨z, hz, hz'⟩
    · obtain ⟨z, hz, hz'⟩ := GlobalTheory.ConjClause.functional_equation_local_lattice D hq T L μ0 hL sc G W M hM F hF σ h h' v hv k p β ϖ hpv hid hlat hmax a ha q i
      refine ⟨z * (if q.1 = σ then -1 else 1), Ideal.mul_mem_right _ _ hz, ?_⟩
      clear hperp hcol hs ht hlat
      have hϖn : (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) ≠ 0 := pow_ne_zero _ hϖ
      have hx : (p.pr (incA D (star (-D.host.xi0)))) ^ (q.1 + 1) ≠ 0 := pow_ne_zero _ hu2
      rw [← hz']
      generalize (p.pr (incA D (star (-D.host.xi0)))) ^ (q.1 + 1) = X at hx ⊢
      generalize (ϖ : k) ^ (G.pl.depth sc v * (2 * σ + 1 - q.1)) = Y at hϖn ⊢
      by_cases hqσ : q.1 = σ
      · simp only [hqσ, if_true]
        push_cast
        field_simp
      · simp only [hqσ, if_false]
        push_cast
        field_simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameDiagonalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_frame_diagonal : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * σ + 2) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b = ι a → a = Fin.last σ ∧ b = Fin.last σ) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ*
    ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcFB W F σ h h').A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  first | exact @GlobalTheory.FrameFB.frame_fb | exact GlobalTheory.FrameFB.frame_fb | (intros; apply GlobalTheory.FrameFB.frame_fb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelElementOffPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.CosetFJ

theorem besselOrbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v), ∀ (u : UX D (σ + 1)), ∀ a ∈ (pcFB W F σ h h').A₁, MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1) - xFB F σ h' - a) → ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) k ⬝ xFB F σ h' - mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1)) := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv g hg u a ha hoff
  obtain ⟨k, _, _, _, _, p, β, ι, ι', s, t, hpv, hidem, hlat, hι, hι', hιι, hX, hΦ, hA⟩ :=
    GlobalTheory.T.split_local_frame_diagonal D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  obtain ⟨ha1, ha2⟩ := hA a ha
  subst hpv
  obtain ⟨k₀, hk₀, hoff'⟩ := GlobalTheory.T.splitPlace_tuples_one_orbit_mod_uniformizer_power D k p _ σ β (xFB F σ h') ι ι' s t (G.pl.depth sc p.v) (G.pl.depth_pos sc _) hι hι' hιι
    hX hΦ g hg u a ha1 ha2 hoff
  have hsd : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  refine ⟨β.gl _, GlobalTheory.T.framedCongruenceElement_mem_principalCongruence D hQ T L μ0 hL sc G W M hM (.grid (2 * σ + 2) 0) hsd p.v hv k p rfl hidem _ β hlat k₀ hk₀, ?_, hoff'⟩
  exact ((GlobalTheory.FrameAt.frame_facts D k p _ _ β).1 _).2 ⟨_, rfl⟩

end GlobalTheory.CosetFJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelElementOffPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_element_off_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v), ∀ (u : UX D (σ + 1)), ∀ a ∈ (pcFB W F σ h h').A₁, MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1) - xFB F σ h' - a) → ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt (G.V (.grid (2 * σ + 2) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * σ + 2) 0)) k ⬝ xFB F σ h' - mt (G.V (.grid (2 * σ + 2) 0)) g⁻¹ ⬝ (xFB F σ h' ⬝ u.1.1)) := by
  first | exact @GlobalTheory.CosetFJ.besselOrbit_at_badPlace_eq_congruenceTranslate | exact GlobalTheory.CosetFJ.besselOrbit_at_badPlace_eq_congruenceTranslate | (intros; apply GlobalTheory.CosetFJ.besselOrbit_at_badPlace_eq_congruenceTranslate <;> assumption)
end
