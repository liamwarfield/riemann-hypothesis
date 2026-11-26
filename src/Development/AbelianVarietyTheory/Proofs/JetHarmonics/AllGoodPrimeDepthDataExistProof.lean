module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtPairsOfPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeFrobeniusOrbitsLabelAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RowDataSuppliedAtSelfConjugatePlaces
public import Development.AutomorphicArithmetic.OrbitLabellings.ExistsPkgCsOfDegreeBoundAtInertPrimes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RestDegAdd
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

private theorem restDeg_add {d : ℕ} [NeZero d] (bgr : ZMod d → Fin 2) (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K)
    (ga : Fin 2 → ZMod d → ℕ → ℕ) :
    RF.restDeg bgr n ga K + ∑ s, n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ s : ZMod d, ∑ k ∈ Finset.Icc 1 K, k * ga g s k := by
  unfold RF.restDeg
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g s => ∑ k ∈ Finset.Icc 1 K, k * ga g s k),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : n * ga (bgr s) s n =
      ∑ g : Fin 2, ∑ k ∈ Finset.Icc 1 K, if g = bgr s ∧ k = n then k * ga g s k else 0 := by
    rw [Finset.sum_eq_single (bgr s), Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

private theorem sum_reps (P : RF.Par) (Z : Finset P.Pl) (h : RF.IsReps P Z) (W : P.Pl → ℕ) :
    ∑ z ∈ Z, ∑ s : ZMod P.d, W (P.pos z s.val) = ∑ z, W z := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => P.pos p.1 p.2.val) (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro p hp q hq hpq
    exact (h (P.pos q.1 q.2.val)).unique ⟨(Finset.mem_product.1 hp).1, hpq⟩ ⟨(Finset.mem_product.1 hq).1, rfl⟩
  · intro z _
    obtain ⟨p, hp, -⟩ := h z
    exact ⟨p, Finset.mem_product.2 ⟨hp.1, Finset.mem_univ _⟩, hp.2⟩

theorem wtHyp_gap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ), 1 ≤ j → j ≤ N.R.m → (∀ z, InPsi H (pl z)) → Dw.p = (N.R.sigW j).1 → Dw.q = (N.R.sigW j).2 → DomW Dw a → ∀ (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (Z : Finset (RPl N.R)) (bgr : ZMod d → Fin 2) (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ)), RF.IsReps (parAt N j d pos) Z → Function.Bijective (fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2) → (∀ z s, tau z (bgr s) s = pl (pos z s.val)) → RF.WtHyp N.R.k N.R.r Z bgr (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) (fun z => RF.alongOrb (parAt N j d pos) z (gapW N pl a)) (fun _ _ => 0) (restOf N Dw pl a) := by
  intro E _ _ _ H Dw N j pl a hj1 hjm hpsi hp hq hdom d _ pos Z bgr tau hZ hbij htau
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
    unfold Datum.mult; split_ifs <;> omega
  have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i)) (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
  have hmain : ∀ z s, gap (Dw.mult (tau z (bgr s) s)) (fun i => a (tau z (bgr s) s, i)) (N.R.k - 1) =
      gapW N pl a (pos z s.val) := by
    intro z s
    rw [htau]
    have hm : Dw.mult (pl (pos z s.val)) = Dw.p := if_pos (hpsi _)
    rw [hm]
    unfold gap gapW
    rw [if_pos (by omega), if_pos (by omega)]
    rfl
  refine ⟨fun z _ g s k hk => (hgs _).1 k hk, fun z _ s => hmain z s, ?_⟩
  have hDF : DF Dw a = ∑ z ∈ Z, ∑ g : Fin 2, ∑ s : ZMod d, ∑ i : Fin (Dw.mult (tau z g s)), a (tau z g s, i) := by
    unfold DF
    rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type,
      ← Finset.sum_coe_sort Z]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.sum_prod_type]
  have key : (∑ z ∈ Z, RF.restDeg bgr (N.R.k - 1)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) N.R.r) +
      (N.R.k - 1) * ∑ z, gapW N pl a z = DF Dw a := by
    have hs : ∑ z ∈ Z, ∑ s : ZMod d, gapW N pl a (pos z s.val) = ∑ z, gapW N pl a z :=
      sum_reps (parAt N j d pos) Z hZ (gapW N pl a)
    rw [hDF, ← hs, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun z _ => ?_
    have := restDeg_add bgr (N.R.k - 1) N.R.r (by omega) (by omega)
      (fun g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i))
    simp only [hmain] at this
    rw [Finset.mul_sum, this]
    exact Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2
  unfold restOf
  rw [← key]
  push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
  simp

end GlobalTheory.RowAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SupplyExtend
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

theorem supply_extend :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (Pl : Type) [Fintype Pl] (Z : Finset Pl) (n m : ℕ) (big : Pl → Fin 2 → ZMod d → Prop) (rk : Pl → Fin 2 → ZMod d → ℕ) (ga : Pl → Fin 2 → ZMod d → ℕ → ℕ) (nW : ℕ) (ν : ℝ), Z.Nonempty → Supply V d Z Finset.univ n m (fun o => big o.1) (fun o => rk o.1) (fun o => ga o.1) nW ν → Supply V d Pl Z n m big rk ga nW ν := by
  intro C _ V d _ Pl _ Z n m big rk ga nW ν hZ h
  obtain ⟨I, J, fI, fJ, X, F, h1, h2, h3⟩ := h
  obtain ⟨z0, hz0⟩ := hZ
  obtain ⟨q, hq⟩ : ∃ q : Pl → Z, ∀ o : Z, q o.1 = o :=
    ⟨fun o => if h : o ∈ Z then ⟨o, h⟩ else ⟨z0, hz0⟩, fun o => by simp [o.2]⟩
  refine ⟨fun o => I (q o), fun o => J (q o), fun o => fI (q o), fun o => fJ (q o), fun o => X (q o),
    fun o => F (q o), fun o => h1 (q o), ?_, ?_⟩
  · intro o ho g s
    have e := h2 (q o) (Finset.mem_univ _) g s
    have e' : (q o).1 = o := congrArg Subtype.val (hq ⟨o, ho⟩)
    simp only [e'] at e
    exact e
  · intro L hA hR hW
    have key := h3 (fun o => L o.1) ?_ ?_ ?_
    · rw [← Finset.sum_coe_sort Z]
      exact key
    · intro o _ p hp
      have e := hA o.1 o.2 p hp
      have gen : ∀ o' : Z, o' = o → p.1.Attains (X o') (F o') p.2 → p.1.Attains (X o) (F o) p.2 := by
        intro o' ho' h'
        subst ho'
        exact h'
      exact gen _ (hq o) e
    · rw [← Finset.sum_coe_sort Z] at hR
      refine le_trans (le_of_eq ?_) hR
      refine Finset.sum_congr rfl fun o _ => ?_
      simp only [(h1 _).1]
    · intro o _ g a k
      have e := hW o.1 o.2 g a k
      have gen : ∀ o' : Z, o' = o → ((L o.1).map fun p => p.1.wt (X o') g a k).sum = ga o.1 g a k →
          ((L o.1).map fun p => p.1.wt (X o) g a k).sum = ga o.1 g a k := by
        intro o' ho' h'
        subst ho'
        exact h'
      exact gen _ (hq o) e

end GlobalTheory.RowAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PackagesExistFrobeniusComplexConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotInPsiConj
set_option autoImplicit false

noncomputable section

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LabSelf

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
theorem conj_conj (τ : E →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
  ext x; simp

theorem rt_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : (starRingEnd ℂ) H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have h0 : H.rt0.re = 0 := by
    by_contra hne
    have h1 : H.rt0.re * H.rt0.im = 0 := by linarith
    have h2 : H.rt0.im = 0 := (mul_eq_zero.1 h1).resolve_left hne
    rw [h2] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨Complex.ext (by simp [h0]) (by simp), fun hz => ?_⟩
  rw [hz] at hre
  simp at hre
  exact H.d_prime.ne_zero hre

theorem inPsi_or_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ) := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have h : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]
    simp
  unfold InPsi
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact Or.inl h
  · right
    rw [h, map_neg, (rt_conj H).1, neg_neg]

theorem not_inPsi_conj (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {τ : E →+* ℂ} (h1 : InPsi H τ) :
    ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h2
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1, (rt_conj H).1] at h2
  exact (rt_conj H).2 (by linear_combination (-1 / 2 : ℂ) * h2)

theorem embK_conj {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {lv : Level H} (c : Coeff lv) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (H.bar x) := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl

theorem zmod_two (s : ZMod 2) : s = 0 ∨ s = 1 := by
  revert s; decide

theorem arithS_tauC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (N : NumDatum) (pl : RPl N.R → (E →+* ℂ)), PlaceTie N c pl → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → V.l = resCharOf la → (∀ x ∈ la.asIdeal, V.MM (ι (io ((x : 𝓞 c.F) : c.F)))) → PhiC N V.l → ∀ n j j' : ℕ, ArithS V io ι (⟨tauC N pl, n, j, j'⟩ : LabS E (RPl N.R)) ∧ Function.Surjective (fun x : RPl N.R × ZMod 2 => tauC N pl x.1 x.2) := by
  intro E _ _ _ H lv c N pl hP la T io C _ _ V ι _ hl hla hC n j j'
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have h10 : ¬ (1 : ZMod 2) = 0 := by decide
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  have t0 : ∀ z, tauC N pl z 0 = pl z := fun z => if_pos rfl
  have t1 : ∀ z, tauC N pl z 1 = ComplexEmbedding.conjugate (pl z) := fun z => if_neg h10
  have hpos : ∀ z, N.pos (resCharOf la) z 1 = z := by
    intro z
    unfold NumDatum.pos
    rw [← hl, hC.1, hC.2]
    simp
  have hfr : ∀ z x, V.MM (emA3 io ι (ComplexEmbedding.conjugate (pl z)) x - emA3 io ι (pl z) x ^ V.l) := by
    intro z x
    obtain ⟨y, hy, he⟩ := hP.frob la (Or.inl (hl ▸ hC.1)) z x
    have h1 := hla y hy
    rw [he, hpos, ← hl, map_sub, map_sub, map_pow, map_pow] at h1
    exact h1
  have hem : ∀ τ x, emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (H.bar x) := by
    intro τ x
    show ι (io (embK c _ x)) = ι (io (embK c τ (H.bar x)))
    rw [embK_conj]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨z, s⟩ ⟨z', s'⟩ h
    dsimp only at h
    rcases zmod_two s with rfl | rfl <;> rcases zmod_two s' with rfl | rfl
    · rw [t0, t0] at h
      rw [hP.inj h]
    · rw [t0, t1] at h
      exact absurd (h ▸ hpsi z) (not_inPsi_conj H (hpsi z'))
    · rw [t1, t0] at h
      exact absurd (h ▸ hpsi z') (not_inPsi_conj H (hpsi z))
    · rw [t1, t1] at h
      have h' := congrArg ComplexEmbedding.conjugate h
      rw [conj_conj, conj_conj] at h'
      rw [hP.inj h']
  · intro z s
    dsimp only
    rcases zmod_two s with rfl | rfl
    · rw [zero_add, t0, t1]
    · rw [h11, t0, t1, conj_conj]
  · intro z s x
    dsimp only
    rcases zmod_two s with rfl | rfl
    · rw [zero_add, t0, t1]
      exact hfr z x
    · rw [h11, t0, t1]
      have h1 := hfr z (H.bar x)
      rwa [← hem, ← hem, conj_conj] at h1
  · have h := hC.1
    unfold NumDatum.cls primeClass at h
    refine hP.unr _ V.l_prime (fun h2 => ?_) (fun hq => ?_) (fun hd => ?_)
    · rw [if_pos h2] at h
      cases h
    · rw [if_pos hq] at h
      split_ifs at h
    · rw [if_pos hd] at h
      split_ifs at h
  · intro τ
    rcases inPsi_or_conj H τ with h | h
    · obtain ⟨z, hz⟩ := (hP.psi _).1 h
      exact ⟨(z, 0), (t0 z).trans hz⟩
    · obtain ⟨z, hz⟩ := (hP.psi _).1 h
      exact ⟨(z, 1), (t1 z).trans (by rw [hz, conj_conj])⟩

end GlobalTheory.LabSelf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PackagesExistFrobeniusComplexConjugation
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.PkgConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

noncomputable def gaC (N : NumDatum) (Dw : Datum H) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ)
    (z : RPl N.R) (s : ZMod 2) : ℕ → ℕ :=
  gap (Dw.mult (tauC N pl z s)) fun i => a (tauC N pl z s, i)

theorem exists_rowFam (hUp : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {Dw : Datum H} {lv : Level H} (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)] :
    AllPts Xo c fun N j l pl a nW ν => PhiC N l →
      Function.Bijective (fun x : RPl N.R × ZMod 2 => tauC N pl x.1 x.2) ∧
      ∃ R : RF.RowFam (parOf N j l) l 2, (∀ z, (R.X z).Alt) ∧
        (∀ z s, (R.X z).rkF 0 s = Dw.mult (tauC N pl z s)) ∧
        @RF.ValBlocksC R.C R.fC R.V (parOf N j l).Pl _ R.I R.J R.fI R.fJ R.X R.F nW (gaC N Dw pl a) ν := by
  intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 _ _ hM _ T io e hover y hy C3 nW ν hν hC
  obtain ⟨C, _, _, V, ι, hVl, hι, hac, hcpl, hla, hunit, hconv⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl
    (hVl ▸ (fun h => h2 (h ▸ N.H.two_mem_small) : resCharOf la ≠ 2)) (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  obtain ⟨hA, hS⟩ := GlobalTheory.LabSelf.arithS_tauC E H lv c N pl hP la T io C V ι hι hVl hla (hVl ▸ hC)
    (N.R.k - 1) j (N.R.m - j)
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
  have hrk : (⟨tauC N pl, N.R.k - 1, j, N.R.m - j⟩ : LabS E (RPl N.R)).RankOK Dw := by
    intro z
    have h10 : ¬ (1 : ZMod 2) = 0 := by decide
    have t0 : tauC N pl z 0 = pl z := if_pos rfl
    have t1 : tauC N pl z 1 = ComplexEmbedding.conjugate (pl z) := if_neg h10
    have m0 : Dw.mult (pl z) = Dw.p := if_pos (hpsi z)
    have m1 : Dw.mult (ComplexEmbedding.conjugate (pl z)) = Dw.q :=
      if_neg (GlobalTheory.LabSelf.not_inPsi_conj H (hpsi z))
    refine ⟨?_, ?_⟩
    · show Dw.mult (tauC N pl z 0) = N.R.k - 1 + j
      rw [t0, m0]; omega
    · show Dw.mult (tauC N pl z 1) = N.R.m - j
      rw [t1, m1, hq']
  obtain ⟨I, J, fI, fJ, X, F, hX, hval⟩ := GlobalTheory.T.rowData_supplied_at_selfConjugate_places hUp E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy
    (RPl N.R) ⟨tauC N pl, N.R.k - 1, j, N.R.m - j⟩ hA hS hrk (by show N.R.m - j < N.R.k - 1; omega) a hdom nW ν
    (hconv y C3 lv.M a nW ν hν)
  refine ⟨⟨hA.inj, hS⟩, { C := C, V := V, hVl := hVl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F, hn := ?_ },
    fun z => (hX z).2.2.1, fun z => (hX z).2.2.2, hval⟩
  intro z
  refine ⟨(hX z).1, (hX z).2.1.trans ?_⟩
  show j + (N.R.m - j) = N.R.m
  omega

private theorem rest_add (n K : ℕ) (h1 : 1 ≤ n) (hK : n ≤ K) (ga : ZMod 2 → ℕ → ℕ) :
    ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 K, (if s = 0 ∧ k = n then (0 : ℝ) else (k : ℝ) * ga s k) =
      ∑ s : ZMod 2, ((∑ k ∈ Finset.Icc 1 K, k * ga s k : ℕ) : ℝ) - (n : ℝ) * ga 0 n := by
  have e : (n : ℝ) * ga 0 n =
      ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 K, if s = 0 ∧ k = n then (k : ℝ) * ga s k else 0 := by
    rw [Finset.sum_eq_single 0, Finset.sum_eq_single n]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_Icc.2 ⟨h1, hK⟩) h
    · intro b _ hb; simp [hb]
    · simp
  rw [e, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem packages_conj : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgPhiCSt Xo c ∧ PkgZeroCSt Xo c := by
  intro hUp E _ _ _ H Dw lv Xo c _
  refine ⟨?_, ?_⟩
  · intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin T io e hover y hy C3 nW ν hν hC T0 θ0 C1 hdeg hrows
    obtain ⟨hbij, R, halt, hrk, hval⟩ := exists_rowFam hUp Xo c hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin
      T io e hover y hy C3 nW ν hν hC
    have hmk := N.R.m_add_three_le_k
    have hp' : Dw.p = N.R.k + j - 1 := hp
    have hq' : Dw.q = N.R.m - j := hq
    have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
    have hpsi : ∀ z, InPsi H (pl z) := fun z => (hP.psi _).2 ⟨z, rfl⟩
    have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
      unfold Datum.mult; split_ifs <;> omega
    have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i))
      (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
    have hmain : ∀ z, gaC N Dw pl a z 0 (N.R.k - 1) = gapW N pl a z := by
      intro z
      have t0 : tauC N pl z 0 = pl z := if_pos rfl
      have hm : Dw.mult (pl z) = Dw.p := if_pos (hpsi _)
      unfold gaC
      rw [t0, hm]
      unfold gap gapW
      rw [if_pos (by omega), if_pos (by omega)]
      rfl
    have hDF : DF Dw a = ∑ z, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 N.R.r, k * gaC N Dw pl a z s k := by
      unfold DF
      rw [← hbij.sum_comp (fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)), Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun s _ => ((hgs _).2 _ (hmul _)).2.symm
    refine ⟨{ R := R, alt := halt, gaC := gaC N Dw pl a, W := gapW N pl a, nW := nW, T := T0, θ0 := θ0,
              rest := restOf N Dw pl a, ν := ν, supp := ?_, main := hmain, rest_eq := ?_, what₂ := hrows,
              deg := hdeg, val := hval }, rfl, rfl⟩
    · intro z s k hk
      rw [hrk]
      exact (hgs _).1 k hk
    · show restOf N Dw pl a = ∑ z : RPl N.R, ∑ s : ZMod 2, ∑ k ∈ Finset.Icc 1 N.R.r,
        (if s = 0 ∧ k = N.R.k - 1 then (0 : ℝ) else (k : ℝ) * gaC N Dw pl a z s k)
      simp only [rest_add (N.R.k - 1) N.R.r (by omega) (by omega), hmain]
      unfold restOf
      rw [hDF, Finset.sum_sub_distrib, ← Finset.mul_sum]
      push_cast [Nat.cast_sub (show 1 ≤ N.R.k by omega)]
      rfl
  · intro hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin T io e hover y hy C3 nW ν hν hC hw s hfirst hrows
    obtain ⟨-, R, -, hrk, hval⟩ := exists_rowFam hUp Xo c hstar N j pl a hj1 hjm hP hp hq hdom la h2 hq2 hd hM hin
      T io e hover y hy C3 nW ν hν hC
    have hmk := N.R.m_add_three_le_k
    have hp' : Dw.p = N.R.k + j - 1 := hp
    have hq' : Dw.q = N.R.m - j := hq
    have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
    have hmul : ∀ τ, Dw.mult τ ≤ N.R.r := fun τ => by
      unfold Datum.mult; split_ifs <;> omega
    have hgs := fun τ => gap_sums (Dw.mult τ) (fun i => a (τ, i))
      (fun i i' hi hi' => hdom τ ⟨i, lt_of_le_of_lt hi hi'⟩ ⟨i', hi'⟩ hi)
    have hcard : Fintype.card (RPl N.R) = N.R.f := by
      simp [RPl, Ranks.f, Ranks.n, ZMod.card, N.R.card_A]
    refine ⟨{ R := R, gaC := gaC N Dw pl a, K := N.R.r, s := s, nW := nW, T := 1, ν := ν, T_one := le_rfl,
              w_nonneg := hw, supp := ?_, first := ?_, what₂ := ?_, val := hval }, rfl⟩
    · intro z σ k hk
      rw [hrk]
      have h := (hgs _).1 k hk
      exact ⟨h.1, h.2, h.2.trans (hmul _)⟩
    · intro z σ
      rcases Nat.eq_zero_or_pos (Dw.mult (tauC N pl z σ)) with h0 | h0
      · refine le_trans (le_of_eq (Finset.sum_eq_zero fun k _ => ?_)) (Nat.zero_le _)
        by_contra hk
        have h := (hgs _).1 k hk
        omega
      · exact le_trans (le_of_eq (((hgs _).2 _ (hmul _)).1 0 h0)) (hfirst _ h0)
    · show 4 * N.R.r * s * Fintype.card (RPl N.R) ≤ nW
      rw [hcard]; exact hrows

end GlobalTheory.PkgConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PackagesExistFrobeniusComplexConjugationStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.packages_exist_frobeniusComplexConjugation : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgPhiCSt Xo c ∧ PkgZeroCSt Xo c := by
  first | exact @GlobalTheory.PkgConj.packages_conj | exact GlobalTheory.PkgConj.packages_conj | (intros; apply GlobalTheory.PkgConj.packages_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimeDepthDataExistsAtPointsProof
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimeDepthDataExistsAtPointsProof
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.LargePkg

theorem not_inPsi_conj {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  unfold InPsi at h h'
  rw [ComplexEmbedding.conjugate_coe_eq, h] at h'
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h'
  have e := H.sqrt_neg_disc_sq
  rw [hr] at e
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem pkg_of_supply (P : RF.Par) (l : ℕ) {C : Type} [Field C] (V : VF C) (hV : V.l = l) (Z : Finset P.Pl)
    (hZ : RF.IsReps P Z) (hw : ∀ z, 0 ≤ P.w z) (big : P.Pl → Fin 2 → ZMod P.d → Prop)
    (rk : P.Pl → Fin 2 → ZMod P.d → ℕ) (b : P.Pl → Fin 2 → ZMod P.d → ℕ → ℕ) (K s nW : ℕ) (ν : ℝ)
    (hK : ∀ z g a, rk z g a ≤ K) (hb : ∀ z g a i j, i ≤ j → j < rk z g a → b z g a j ≤ b z g a i)
    (h0 : ∀ z g a, 0 < rk z g a → b z g a 0 ≤ s * (l - 1)) (hrows : 2 * K * s * Z.card ≤ nW)
    (hS : Supply V P.d P.Pl Z (P.k - 1) P.m big rk (fun z g a => gap (rk z g a) (b z g a)) nW ν) :
    ∃ Pk : RF.PkgZero P l, Pk.ν = ν := by
  obtain ⟨I, J, fI, fJ, X, F, hn, hrk, hval⟩ := hS
  refine ⟨{ R := { C := C, V := V, hVl := hV, I := I, J := J, X := X, F := F, hn := hn }
            Z := Z, hZ := hZ, ga := fun z g a => gap (rk z g a) (b z g a), K := K, s := s, nW := nW, T := 1, ν := ν
            T_one := le_rfl, w_nonneg := hw, supp := ?_, first := ?_, what₂ := hrows, val := hval }, rfl⟩
  · intro z hz g a k hk
    obtain ⟨h1, h2⟩ := (GlobalTheory.RowAt.gap_sums (rk z g a) (b z g a) (hb z g a)).1 k hk
    exact ⟨h1, h2.trans_eq (hrk z hz g a).2.symm, h2.trans (hK z g a)⟩
  · intro z _ g a
    obtain ⟨h1, h2⟩ := GlobalTheory.RowAt.gap_sums (rk z g a) (b z g a) (hb z g a)
    rcases Nat.eq_zero_or_pos (rk z g a) with h | h
    · refine le_of_eq_of_le (Finset.sum_eq_zero fun k _ => ?_) (Nat.zero_le _)
      by_contra hk
      have := h1 k hk
      omega
    · exact le_of_eq_of_le ((h2 K (hK z g a)).1 0 h) (h0 z g a h)

theorem pkg_of_labels (hU : ∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p)
    {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {lv : Level H}
    {Xo : Moduli Dw lv} {c : Coeff lv} [StarRing (𝓞 E)] (hstar : ∀ x : 𝓞 E, star x = H.bar x)
    (N : NumDatum) (j : ℕ) (pl : RPl N.R → (E →+* ℂ)) (a : (E →+* ℂ) × ℕ → ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ N.R.m)
    (hpsi : ∀ z, InPsi H (pl z)) (hp : Dw.p = (N.R.sigW j).1) (hq : Dw.q = (N.R.sigW j).2) (ha : DomW Dw a)
    {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io} (hy : y.IsAlg) (C3 : IntChart T io y)
    {C : Type} [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C) (hι : EmbOK T V ι) {k : ℕ}
    (Y : FBChart C V (𝓞 E) (chD C3.ch)) (hY : IsBC C3 ι k Y) (hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E)
    (nW : ℕ) (ν : ℝ) (hν : (ν : EReal) ≤ nuLocC C3 (eOf T V) k a nW)
    (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) (sel : ZMod d → Fin 2)
    (hsel : (Even d ∧ ∀ s : ZMod d, (0 = sel s ↔ Even s.val)) ∨ ∀ s, 0 = sel s)
    (tau : RPl N.R → Fin 2 → ZMod d → (E →+* ℂ))
    (htau : ∀ z g s, tau z g s = if g = sel s then pl (pos z s.val) else ComplexEmbedding.conjugate (pl (pos z s.val)))
    (Z : Finset (RPl N.R)) (hZ : RF.IsReps (parAt N j d pos) Z) (hne : Z.Nonempty)
    (hbij : Function.Bijective fun x : Z × Fin 2 × ZMod d => tau x.1.1 x.2.1 x.2.2)
    (hfrob : ∀ z g, FrobOrd V io ι (tau z g)) (hw : ∀ z, 0 ≤ N.w j z) (s : ℕ)
    (hs : ∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (V.l - 1)) (hrows : 2 * N.R.r * s * N.R.f ≤ nW) :
    ∃ Pk : RF.PkgZero (parAt N j d pos) V.l, Pk.ν = ν := by
  have hk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq' : Dw.q = N.R.m - j := hq
  let lab : Lab E Z d := ⟨fun o => tau o.1, N.R.k - 1, j, N.R.m - j, fun _ g s => g = sel s⟩
  have hconj : ∀ z s, tau z 1 s = ComplexEmbedding.conjugate (tau z 0 s) := by
    intro z s
    rw [htau, htau]
    generalize sel s = g
    fin_cases g
    · simp
    · have : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ => by
        ext x; simp
      simp [this]
  have hA : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => hconj o.1 s
      frob := fun o g s x => hfrob o.1 g s x
      sep := fun x x' hx => (GlobalTheory.T.cmEmbeddings_integral_and_distinct_mod_maximal E H lv c T io C V ι hι hunr).2 _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.T.exists_idempotent_frobeniusOrbit_unramified E H lv c T io C V ι hι hunr d (tau o.1 g) (hfrob o.1 g) }
  have hR : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s h => ?_, fun g s h => ?_⟩
    · change 1 - g = sel s ↔ ¬ g = sel s
      generalize sel s = g'
      revert g g'
      decide
    · change Dw.mult (tau o.1 g s) = N.R.k - 1 + j
      rw [htau, if_pos (show g = sel s from h), Datum.mult]
      exact (if_pos (hpsi _)).trans (by omega)
    · change Dw.mult (tau o.1 g s) = N.R.m - j
      rw [htau, if_neg (show ¬ g = sel s from h), Datum.mult]
      exact (if_neg (not_inPsi_conj H (hpsi _))).trans hq'
  have h1 := GlobalTheory.T.rowData_supplied_at_pairs_of_places hU E H Dw lv Xo c hstar T io y C3 C V ι hι k Y hY hy hunr Z d lab hA hbij.2 hR
    (show N.R.m - j < N.R.k - 1 by omega) (fun _ => hsel) a ha nW ν hν
  have hm : lab.j + lab.j' = N.R.m := show j + (N.R.m - j) = N.R.m by omega
  rw [hm] at h1
  have h2 := GlobalTheory.RowAt.supply_extend C V d (RPl N.R) Z (N.R.k - 1) N.R.m (fun _ g s => g = sel s)
    (fun z g s => Dw.mult (tau z g s)) (fun z g s => gap (Dw.mult (tau z g s)) fun i => a (tau z g s, i)) nW ν hne h1
  have hcard : Z.card ≤ N.R.f := by
    refine (Finset.card_le_univ Z).trans_eq ?_
    simp [Ranks.f_eq_ord, Formalism.HC.Frame.card_A]
  refine pkg_of_supply (parAt N j d pos) V.l V rfl Z hZ hw (fun _ g s => g = sel s)
    (fun z g s => Dw.mult (tau z g s)) (fun z g s i => a (tau z g s, i)) N.R.r s nW ν ?_ ?_ ?_ ?_ h2
  · intro z g s
    unfold Datum.mult Ranks.r
    split_ifs <;> omega
  · intro z g s i i' h h'
    exact ha (tau z g s) ⟨i, h.trans_lt h'⟩ ⟨i', h'⟩ h
  · intro z g s h
    exact hs _ h
  · exact (Nat.mul_le_mul_left _ hcard).trans hrows

theorem pkgZero : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgZeroSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hT hp hq ha la h2 hlq hld hM _ T io e hO y hy C3 nW ν hν
    hphi hw s hs hrows
  obtain ⟨C, _, _, V, ι, hV, hι, hac, hcpl, hla, hunit, hnu⟩ := GlobalTheory.T.exists_closedComplete_field_over_place E H Dw lv Xo c la T io e hO
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl (hV ▸ ne_two_of_not_small h2)
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  have hν' := hnu y C3 lv.M a nW ν hν
  rw [← hV] at h2 hlq hld hphi hs ⊢
  have hunr := hT.unr V.l V.l_prime h2 hlq hld
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hT.psi _).2 ⟨z, rfl⟩
  by_cases hin : Inert N V.l
  · obtain ⟨Z, hZ, hne, hev, hbij, hfr⟩ := GlobalTheory.T.realPlaceLabelling_inert_frobenius_not_conj E H lv c N pl hT la T io C V ι hι hV hla hin hphi j
    refine ⟨N.ordP V.l, inferInstance, N.pos V.l, pkg_of_labels hU hstar N j pl a hj1 hjm hpsi hp hq ha hy C3 V ι hι Y hY
      hunr nW ν hν' (N.ordP V.l) (N.pos V.l) RF.bg (Or.inl ⟨hev, fun s => ?_⟩) (tauIn N pl V.l) (fun _ _ _ => rfl)
      Z hZ hne hbij (fun z g => (hfr z g).1) hw s hs hrows⟩
    unfold RF.bg
    split_ifs with h <;> simp [h]
  · have hsp : N.cls V.l = PrimeClass.splitK := by
      unfold Inert NumDatum.cls primeClass at *
      rw [if_neg h2, if_neg hlq, if_neg hld] at hin ⊢
      split_ifs at hin ⊢ <;> simp_all
    obtain ⟨d, _, pos, Z, hZ, hne, hbij, hfr⟩ := GlobalTheory.T.cmType_frobenius_orbits_label_at_split_prime E H lv c N pl hT la T io C V ι hι hV hla hsp j
    exact ⟨d, inferInstance, pos, pkg_of_labels hU hstar N j pl a hj1 hjm hpsi hp hq ha hy C3 V ι hι Y hY
      hunr nW ν hν' d pos (fun _ => 0) (Or.inr fun _ => rfl) (tauSp N pl pos) (fun _ _ _ => rfl)
      Z hZ hne hbij hfr hw s hs hrows⟩

end GlobalTheory.LargePkg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimeDepthDataExistsAtPointsProofStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.largePrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgZeroSt Xo c := by
  first | exact @GlobalTheory.LargePkg.pkgZero | exact GlobalTheory.LargePkg.pkgZero | (intros; apply GlobalTheory.LargePkg.pkgZero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthDataExistsAtPointsProof
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthDataExistsAtPointsProof
set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.SplitPackage

theorem not_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    {τ : E →+* ℂ} (h : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h'
  have hd : 0 < H.d := H.d_prime.pos
  have e2 : starRingEnd ℂ (τ (H.rt : E)) = τ (H.rt : E) := by
    have h1 : τ (H.rt : E) = H.rt0 := h
    have h2 : starRingEnd ℂ (τ (H.rt : E)) = H.rt0 := h'
    rw [h2, h1]
  have e3 : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
    have := congrArg (fun z : 𝓞 E => τ (z : E)) H.rt_sq
    simpa using this
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 e2
  rw [hr] at e3
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
  have : (0 : ℝ) < H.d := by exact_mod_cast hd
  nlinarith [sq_nonneg r]

theorem pkgSplit : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSplitSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd' hM _ T io e hov y hy C3 nW ν hν
    hsp Tr θ0 C1 hdeg hrows
  obtain ⟨C, _, _, V, ι, hVl, hι, hac, hcpl, hMM, hunit, hnu⟩ :=
    GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hov
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl
    (by rw [hVl]; intro h; exact h2 (h ▸ N.H.two_mem_small)) (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M (hunit _ hM)
  have hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E :=
    hpl.unr V.l V.l_prime (by rw [hVl]; exact h2) (by rw [hVl]; exact hq') (by rw [hVl]; exact hd')
  obtain ⟨d, _, pos, Z, hZ, hne, hbij, hfr⟩ := GlobalTheory.T.cmType_frobenius_orbits_label_at_split_prime E H lv c N pl hpl la T io C V ι hι hVl hMM
    (by rw [hVl]; exact hsp) j
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hpl.psi _).2 ⟨z, rfl⟩
  have hmk := N.R.m_add_three_le_k
  have hp' : Dw.p = N.R.k + j - 1 := hp
  have hq'' : Dw.q = N.R.m - j := hq
  let lab : Lab E Z d :=
    { tau := fun o => tauSp N pl pos o.1, n := N.R.k - 1, j := j, j' := N.R.m - j, big := fun _ g _ => g = 0 }
  have hsep := (GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' E H lv c T io C V ι hι hunr).2
  have harith : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => by simp [lab, tauSp]
      frob := fun o g s x => hfr o.1 g s x
      sep := fun x x' hx => hsep _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.exists_idempotent_of_unramified_place E H lv c T io C V ι hι hunr d _ (hfr o.1 g) }
  have hrank : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s hg => ?_, fun g s hg => ?_⟩
    · change (1 - g = 0) ↔ ¬ g = 0
      revert g; decide
    · change g = 0 at hg
      change Dw.mult (tauSp N pl pos o.1 g s) = N.R.k - 1 + j
      rw [tauSp, if_pos hg]
      have : Dw.mult (pl (pos o.1 s.val)) = Dw.p := if_pos (hpsi _)
      omega
    · change ¬ g = 0 at hg
      change Dw.mult (tauSp N pl pos o.1 g s) = N.R.m - j
      rw [tauSp, if_neg hg]
      have : Dw.mult (ComplexEmbedding.conjugate (pl (pos o.1 s.val))) = Dw.q :=
        if_neg (not_inPsi_conjugate H (hpsi _))
      omega
  have hsup := GlobalTheory.T.rowData_supplied_at_pairs_of_places hU E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy hunr Z d lab harith hbij.2 hrank
    (by change N.R.m - j < N.R.k - 1; omega) (fun o => Or.inr fun _ => rfl) a hdom nW ν (hnu y C3 lv.M a nW ν hν)
  obtain ⟨I, J, fI, fJ, X, F, hn, hbig, hval⟩ := GlobalTheory.RowAt.supply_extend C V d (RPl N.R) Z (N.R.k - 1) (j + (N.R.m - j))
    (fun _ g _ => g = 0) (fun z g s => Dw.mult (tauSp N pl pos z g s))
    (fun z g s => gap (Dw.mult (tauSp N pl pos z g s)) fun i => a (tauSp N pl pos z g s, i)) nW ν hne hsup
  have hwt := GlobalTheory.RowAt.wtHyp_gap E H Dw N j pl a hj1 hjm hpsi hp hq hdom d pos Z (fun _ => 0) (tauSp N pl pos) hZ hbij
    (fun z s => by simp [tauSp])
  refine ⟨d, inferInstance, pos,
    { R := { C := C, V := V, hVl := hVl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F,
             hn := fun z => ⟨(hn z).1, (hn z).2.trans (by change j + (N.R.m - j) = N.R.m; omega)⟩ }
      Z := Z
      hZ := hZ
      allBig := fun z hz s => ((hbig z hz 0 s).1).2 rfl
      ga := fun z g s => gap (Dw.mult (tauSp N pl pos z g s)) fun i => a (tauSp N pl pos z g s, i)
      W := gapW N pl a
      nW := nW
      T := Tr
      θ0 := θ0
      rest := restOf N Dw pl a
      ν := ν
      wt := ⟨fun z hz g s k hk => ?_, hwt.main, hwt.rest_eq⟩
      what₂ := hrows
      deg := ⟨hdeg.T_one, hdeg.w_pos, hdeg.TW_lo, hdeg.TW_hi, hdeg.th_rng, hdeg.th_m, hdeg.rest_nonneg, hdeg.rest_le⟩
      val := hval }, rfl, rfl⟩
  have h1 := hwt.supp z hz g s k hk
  exact ⟨h1.1, h1.2.trans (hbig z hz g s).2.ge⟩

end GlobalTheory.SplitPackage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthDataExistsAtPointsProofStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSplitSt Xo c := by
  first | exact @GlobalTheory.SplitPackage.pkgSplit | exact GlobalTheory.SplitPackage.pkgSplit | (intros; apply GlobalTheory.SplitPackage.pkgSplit <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthDataExistsAtPointsProof
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthDataExistsAtPointsProof
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.InertPackage

theorem not_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (τ : E →+* ℂ) (h1 : InPsi H τ) : ¬ InPsi H (ComplexEmbedding.conjugate τ) := by
  intro h2
  unfold InPsi at h1 h2
  rw [ComplexEmbedding.conjugate_coe_eq, h1] at h2
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h2
  have e3 := H.sqrt_neg_disc_sq
  rw [hr] at e3
  have e4 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast e3
  have : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

theorem zero_eq_bg_iff {d : ℕ} [NeZero d] (s : ZMod d) : (0 : Fin 2) = RF.bg s ↔ Even s.val := by
  unfold RF.bg
  split_ifs with h <;> simp [h]

theorem pkgInert : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgInertSt Xo c := by
  intro hUp E _ _ _ H Dw lv Xo c _ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hqq hdd hM _ T io e hover y hy C3 nW ν hν
    hin hphi TT θ0 C1 hdeg hrows
  obtain ⟨C, _, _, V, ι, hl, hι, hac, hcpl, hla, hunit, hval⟩ := GlobalTheory.PlaceClosedField.exists_closed_field_over_place E H Dw lv Xo c la T io e hover
  have hν' := hval y C3 lv.M a nW ν hν
  have hMu := hunit lv.M hM
  rw [← hl] at h2 hqq hdd hin hphi hdeg hrows ⊢
  obtain ⟨Y, hY⟩ := GlobalTheory.ChartBaseChange.exists_baseChange E H Dw lv Xo c T io y C3 C V ι hι hac hcpl (ne_two_of_not_small h2)
    (GlobalTheory.QuadTrace.cmHost_idempotent_trace_eq_one E H hstar) lv.M hMu
  have hunr : ¬ (V.l : ℤ) ∣ NumberField.discr E := hpl.unr V.l V.l_prime h2 hqq hdd
  obtain ⟨Z, hZ, hZne, heven, hbij, hfr⟩ := GlobalTheory.InertLabelling.main E H lv c N pl hpl la T io C V ι hι hl hla hin hphi j
  have hpsi : ∀ z, InPsi H (pl z) := fun z => (hpl.psi _).2 ⟨z, rfl⟩
  have hmk := N.R.m_add_three_le_k
  let lab : Lab E Z (N.ordP V.l) :=
    { tau := fun o => tauIn N pl V.l o.1
      n := N.R.k - 1
      j := j
      j' := N.R.m - j
      big := fun _ g s => g = RF.bg s }
  have harith : LabArith V io ι lab :=
    { inj := hbij.1
      conj := fun o s => (hfr o.1 0).2 s
      frob := fun o g => (hfr o.1 g).1
      sep := fun x x' hx => (GlobalTheory.EmbSep.cmEmbeddings_integral_and_distinct_mod_maximal' E H lv c T io C V ι hι hunr).2 _ _ fun h => hx (hbij.1 h)
      unr := fun o g => GlobalTheory.exists_idempotent_of_unramified_place E H lv c T io C V ι hι hunr _ _ (hfr o.1 g).1 }
  have hrank : lab.RankOK Dw := by
    intro o
    refine ⟨fun g s => ?_, fun g s hg => ?_, fun g s hg => ?_⟩
    · show 1 - g = RF.bg s ↔ ¬ g = RF.bg s
      generalize RF.bg s = b
      revert g b
      decide
    · have hg' : g = RF.bg s := hg
      show Dw.mult (tauIn N pl V.l o.1 g s) = N.R.k - 1 + j
      unfold tauIn Datum.mult
      rw [if_pos hg']
      refine (if_pos (hpsi _)).trans ?_
      rw [hp]
      show N.R.k + j - 1 = _
      omega
    · have hg' : ¬ g = RF.bg s := hg
      show Dw.mult (tauIn N pl V.l o.1 g s) = N.R.m - j
      unfold tauIn Datum.mult
      rw [if_neg hg']
      exact (if_neg (not_inPsi_conjugate H _ (hpsi _))).trans hq
  have hsup := GlobalTheory.T.rowData_supplied_at_pairs_of_places hUp E H Dw lv Xo c hstar T io y C3 C V ι hι lv.M Y hY hy hunr Z (N.ordP V.l) lab harith
    hbij.2 hrank (show N.R.m - j < N.R.k - 1 by omega) (fun _ => Or.inl ⟨heven, fun s => zero_eq_bg_iff s⟩) a hdom nW ν hν'
  obtain ⟨I, J, fI, fJ, X, F, hn, hbig, hvb⟩ := GlobalTheory.RowAt.supply_extend C V (N.ordP V.l) (RPl N.R) Z (N.R.k - 1) (j + (N.R.m - j))
    (fun _ g s => g = RF.bg s) (fun z g s => Dw.mult (tauIn N pl V.l z g s))
    (fun z g s => gap (Dw.mult (tauIn N pl V.l z g s)) fun i => a (tauIn N pl V.l z g s, i)) nW ν hZne hsup
  have hwt := GlobalTheory.RowAt.wtHyp_gap E H Dw N j pl a hj1 hjm hpsi hp hq hdom (N.ordP V.l) (N.pos V.l) Z RF.bg (tauIn N pl V.l) hZ hbij
    (fun z s => if_pos rfl)
  refine ⟨{ R := { C := C, V := V, hVl := rfl, I := I, J := J, fI := fI, fJ := fJ, X := X, F := F
                   hn := fun z => ⟨(hn z).1, (hn z).2.trans (by show j + (N.R.m - j) = N.R.m; omega)⟩ }
            Z := Z
            hZ := hZ
            alt := fun z hz => ⟨heven, fun s => ((hbig z hz 0 s).1).trans (zero_eq_bg_iff s)⟩
            ga := fun z g s => gap (Dw.mult (tauIn N pl V.l z g s)) fun i => a (tauIn N pl V.l z g s, i)
            W := gapW N pl a
            nW := nW
            T := TT
            θ0 := θ0
            rest := restOf N Dw pl a
            ν := ν
            wt := ⟨fun z hz g s k' hk => ?_, hwt.main, hwt.rest_eq⟩
            what₂ := hrows
            deg := hdeg
            val := hvb }, rfl, rfl⟩
  have h := hwt.supp z hz g s k' hk
  exact ⟨h.1, h.2.trans_eq (hbig z hz g s).2.symm⟩

end GlobalTheory.InertPackage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthDataExistsAtPointsProofStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrimeDepthDataExistsAtPoints_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgInertSt Xo c := by
  first | exact @GlobalTheory.InertPackage.pkgInert | exact GlobalTheory.InertPackage.pkgInert | (intros; apply GlobalTheory.InertPackage.pkgInert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AllGoodPrimeDepthDataExistProof
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem goodPrime_packages :
    (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) →
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
        (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  intro hU E _ _ _ H Dw lv Xo c _
  exact ⟨GlobalTheory.T.inertPrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).1, GlobalTheory.T.splitPrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c,
    GlobalTheory.T.largePrimeDepthDataExistsAtPoints_proof hU E H Dw lv Xo c, (GlobalTheory.T.packages_exist_frobeniusComplexConjugation hU E H Dw lv Xo c).2,
    (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).1, (UpperTheory.exists_pkgCs_of_degree_bound_at_inert_primes hU E H Dw lv Xo c).2⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.AllGoodPrimeDepthDataExistProofStatement
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.allGoodPrimeDepthDataExist_proof : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], PkgSt Xo c := by
  first | exact @GlobalTheory.goodPrime_packages | exact GlobalTheory.goodPrime_packages | (intros; apply GlobalTheory.goodPrime_packages <;> assumption)
end
