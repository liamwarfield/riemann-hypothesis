module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.MvComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.CycSpecAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.ImportsAlt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.Recip
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.recip :
    UpperTheory.V.Z.Kato.Sym.Recip := by
  classical
  intro Ω _ _ _ ε X s γ S
  choose L hL hLf using X.level
  set M : ℕ := ∏ f ∈ S, L f with hMdef
  have hM : 0 < M := Finset.prod_pos fun f _ => hL f
  have hfix : ∀ f ∈ S, ∀ δ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL δ) f = f := by
    intro f hf δ hδ
    apply hLf f δ
    have hd : L f ∣ M := Finset.dvd_prod_of_mem _ hf
    rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
    obtain ⟨h1, h2, h3, h4⟩ := hδ
    have c1 := congrArg (ZMod.castHom hd (ZMod (L f))) h1
    have c2 := congrArg (ZMod.castHom hd (ZMod (L f))) h2
    have c3 := congrArg (ZMod.castHom hd (ZMod (L f))) h3
    have c4 := congrArg (ZMod.castHom hd (ZMod (L f))) h4
    rw [map_intCast] at c1 c2 c3 c4
    rw [map_one] at c1 c4
    rw [map_zero] at c2 c3
    exact ⟨c1, c2, c3, c4⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have hex : ∀ t : Ω ≃ₐ[ℚ] Ω, ∃ d : ℕ, t ζ = ζ ^ d := fun t => by
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := t ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
    exact ⟨i, hi.symm⟩
  obtain ⟨d, hd⟩ := hex s
  obtain ⟨e, he⟩ := hex s.symm
  have hde : (d : ZMod M) * e = 1 := by
    have h1 : ζ ^ (d * e) = ζ ^ 1 := by
      rw [pow_mul, ← hd, ← map_pow, ← he]; simp
    have h2 := (hζ.isOfFinOrder hM.ne').pow_eq_pow_iff_modEq.mp h1
    rw [← hζ.eq_orderOf] at h2
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    simpa using this
  have hdet : ((en γ 0 0 : ℤ) : ZMod M) * en γ 1 1 - (en γ 0 1 : ℤ) * (en γ 1 0 : ℤ) = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    have := congrArg (Int.cast : ℤ → ZMod M) h
    simpa [en] using this
  let A : SL(2, ZMod M) := ⟨!![(en γ 0 0 : ℤ), e * (en γ 0 1 : ℤ); d * (en γ 1 0 : ℤ), (en γ 1 1 : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet - ((en γ 0 1 : ℤ) : ZMod M) * (en γ 1 0 : ℤ) * hde⟩
  obtain ⟨γ', hγ'⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M A
  have hent : ∀ i j, ((en γ' i j : ℤ) : ZMod M) = A.1 i j := fun i j => by
    rw [← hγ']; rfl
  refine ⟨γ', fun f hf => (X.recip M f hM (hfix f hf) ζ hζ s d (by rw [hd, zpow_natCast]) γ' γ ?_).symm⟩
  rw [hent, hent, hent, hent]
  refine ⟨by simp [A], ?_, by simp [A], by simp [A]⟩
  have : A.1 0 1 = e * (en γ 0 1 : ℤ) := by simp [A]
  rw [this]
  push_cast
  linear_combination -((en γ 0 1 : ℤ) : ZMod M) * hde
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.eqv :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∀ s, Eqv X m M (w s) := by
  classical
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w hT hW s x y hxy
  refine ⟨(hW s x y hxy).1, fun γ => ?_⟩
  have hR := rowB Ω M hL.1
  have hSg := sgB Ω ε X
  have hAd := admB Ω ε X
  have hUτ : ∀ (τ : X.K ≃+* X.K) (s' : Gal(Ω/ℚ)), admitted X τ s' → ∀ a, IsU X a → IsU X (τ a) :=
    fun τ s' h => (hAd.2.2.2.2.2.1 τ s' h).1
  have hgr : ∀ z : Row M, gr M s (gr M s⁻¹ z) = z := by
    intro z
    rw [← (hR.1 s s⁻¹ z).1, mul_inv_cancel, (hR.1 1 1 z).2]
  have hok0 : Ok (gr M s⁻¹ x) (gr M s⁻¹ y) := (hR.2.1 x y hxy).2.2.1 s⁻¹
  have hokγ : Ok (rt x γ) (rt y γ) := (hR.2.1 x y hxy).2.2.2 γ
  have hok1 : Ok (gr M s⁻¹ (rt x γ)) (gr M s⁻¹ (rt y γ)) := (hR.2.1 _ _ hokγ).2.2.1 s⁻¹
  have sx0 := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hok0).1
  have sy0 := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hok0).2.1
  have sx := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hxy).1
  have sy := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hxy).2.1
  have sxγ := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hokγ).1
  have syγ := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hokγ).2.1
  have sx1 := hSg c M hc hc6 hL.1 hL.2.1 _ (hR.2.1 _ _ hok1).1
  have sy1 := hSg d M hd hd6 hL.1 hL.2.2 _ (hR.2.1 _ _ hok1).2.1
  have ga_u : X.gal s (sg X c M (gr M s⁻¹ x)) = sg X c M x := by rw [sx0.2.2.1 s, hgr]
  have ga_v : X.gal s (sg X d M (gr M s⁻¹ y)) = sg X d M y := by rw [sy0.2.2.1 s, hgr]
  have hP := (hT _ _ sx0.1 sy0.1).1
  obtain ⟨S, hSn⟩ := mvNear Ω ε X m hm _ _ _ hP
  obtain ⟨γ', hγ'⟩ := recip Ω ε X s γ
    (insert (sg X c M (gr M s⁻¹ x)) (insert (sg X d M (gr M s⁻¹ y)) S))
  have hB : IsPt X m (sg X c M (rt x γ)) (sg X d M (rt y γ))
      (t (sg X c M (rt x γ)) (sg X d M (rt y γ))) := (hT _ _ sxγ.1 syγ.1).1
  have h2 := (hT _ _ sx.1 sy.1).2 γ
  rw [sx.2.1 γ, sy.2.1 γ] at h2
  have p1 := mvComp Ω ε X m hm (X.gal s) (slR X (ofSL γ)) s 1 (hAd.2.1 s) (hAd.1 _) _ _ _ _ _ hP
    (by rw [ga_u, ga_v]; exact (hT _ _ sx.1 sy.1).1)
    (by
      change IsPt X m (X.sl (ofSL γ) (X.gal s _)) (X.sl (ofSL γ) (X.gal s _)) _
      rw [ga_u, ga_v, sx.2.1 γ, sy.2.1 γ]
      exact hB) _ _ (hW s x y hxy).2 h2
  have a1 := hAd.2.2.2.1 _ _ _ _ (hAd.2.1 s) (hAd.1 (ofSL γ))
  rw [one_mul] at a1 p1
  have e_u : X.sl (ofSL γ') (sg X c M (gr M s⁻¹ x)) = sg X c M (gr M s⁻¹ (rt x γ)) := by
    apply (X.gal s).injective
    rw [← hγ' _ (by simp), ga_u, sx.2.1 γ, sx1.2.2.1 s, hgr]
  have e_v : X.sl (ofSL γ') (sg X d M (gr M s⁻¹ y)) = sg X d M (gr M s⁻¹ (rt y γ)) := by
    apply (X.gal s).injective
    rw [← hγ' _ (by simp), ga_v, sy.2.1 γ, sy1.2.2.1 s, hgr]
  have h3 := (hT _ _ sx0.1 sy0.1).2 γ'
  rw [e_u, e_v] at h3
  have p2 := mvComp Ω ε X m hm (slR X (ofSL γ')) (X.gal s) 1 s (hAd.1 _) (hAd.2.1 s) _ _ _ _ _ hP
    (by
      change IsPt X m (X.sl (ofSL γ') _) (X.sl (ofSL γ') _) _
      rw [e_u, e_v]
      exact (hT _ _ sx1.1 sy1.1).1)
    (by
      change IsPt X m (X.gal s (X.sl (ofSL γ') _)) (X.gal s (X.sl (ofSL γ') _)) _
      rw [e_u, e_v, sx1.2.2.1 s, sy1.2.2.1 s, hgr, hgr]
      exact hB) _ _ h3 (hW s (rt x γ) (rt y γ) hokγ).2
  have a2 := hAd.2.2.2.1 _ _ _ _ (hAd.1 (ofSL γ')) (hAd.2.1 s)
  rw [mul_one] at a2 p2
  rw [map_one, one_pow, one_mul] at p2
  have hfix : ∀ f ∈ insert (sg X c M (gr M s⁻¹ x)) (insert (sg X d M (gr M s⁻¹ y)) S),
      (((X.gal s).trans (slR X (ofSL γ))).trans ((slR X (ofSL γ')).trans (X.gal s)).symm) f = f := by
    intro f hf
    rw [RingEquiv.trans_apply]
    have k : ((X.gal s).trans (slR X (ofSL γ))) f = ((slR X (ofSL γ')).trans (X.gal s)) f := hγ' f hf
    rw [k, RingEquiv.symm_apply_apply]
  have aρ := hAd.2.2.2.1 _ _ _ _ a1 (hAd.2.2.2.2.1 _ _ a2)
  rw [inv_mul_cancel] at aρ
  have near := hSn _ 1 aρ (fun f hf => hfix f (by simp [hf]))
  have p3 := mvComp Ω ε X m hm _ ((slR X (ofSL γ')).trans (X.gal s)) 1 s aρ a2 _ _ _ _ _ hP
    (by rw [hfix _ (by simp), hfix _ (by simp)]; exact hP)
    (by
      rw [hfix _ (by simp), hfix _ (by simp)]
      change IsPt X m (X.gal s (X.sl (ofSL γ') _)) (X.gal s (X.sl (ofSL γ') _)) _
      rw [e_u, e_v, sx1.2.2.1 s, sy1.2.2.1 s, hgr, hgr]
      exact hB) _ _ near p2
  rw [map_one, one_pow, one_mul, mul_one] at p3
  have htr : ((((X.gal s).trans (slR X (ofSL γ))).trans
      ((slR X (ofSL γ')).trans (X.gal s)).symm).trans ((slR X (ofSL γ')).trans (X.gal s)))
      = (X.gal s).trans (slR X (ofSL γ)) := by
    ext f
    simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rw [htr] at p3
  have hC := ((mvEx Ω ε X m hm _ s a1 _ _ _ hP).2.2.2 _
    (by
      change IsPt X m (X.sl (ofSL γ) (X.gal s _)) (X.sl (ofSL γ) (X.gal s _)) _
      rw [ga_u, ga_v, sx.2.1 γ, sy.2.1 γ]
      exact hB) _ _ p3).mp p1
  rw [mul_one] at hC
  have hu : (unU X (slR X (ofSL γ))) (w s x y) = slU X (ofSL γ) (w s x y) := Units.ext rfl
  rw [hu] at hC
  rcases Nat.lt_or_ge 1 m with h1m | h1m
  · haveI : Fact (1 < m) := ⟨h1m⟩
    have hcyc := ((lgB Ω ε X m hm).2.2.2.2.2.2 1 1).2.1
    rw [hcyc, ZMod.val_one, pow_one] at hC
    exact hC
  · obtain rfl : m = 1 := by omega
    exact ⟨(w s (rt x γ) (rt y γ))⁻¹ * slU X (ofSL γ) (w s x y), by group⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.ImportsBis
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.ExponentialInjectivity.GalNear
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private def Nr (X : Tower Ω ε) (f : X.K) : Prop :=
  ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f

private theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp := X.exp.toRingHom.injective

private theorem nr_j (X : Tower Ω ε) : Nr X X.jK := by
  refine ⟨∅, fun s _ => exp_inj X ?_⟩
  ext r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [X.gal_exp, hn, map_intCast]

private theorem nr_c (X : Tower Ω ε) (c : Ω) : Nr X (algebraMap Ω X.K c) := by
  refine ⟨{c}, fun s hs => exp_inj X ?_⟩
  ext r
  rw [X.gal_exp, AlgHom.commutes, HahnSeries.algebraMap_apply']
  by_cases h : r = 0 <;> simp [h, hs c (Finset.mem_singleton_self c)]

private theorem nr_two (X : Tower Ω ε) {f g : X.K} (hf : Nr X f) (hg : Nr X g) :
    ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f ∧ X.gal s g = g := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A ∪ B, fun s hs => ⟨hA s fun z hz => hs z (Finset.mem_union_left _ hz),
    hB s fun z hz => hs z (Finset.mem_union_right _ hz)⟩⟩

private theorem nr_adj (X : Tower Ω ε) (f : X.K) (hf : f ∈ IntermediateField.adjoin Ω {X.jK}) : Nr X f := by
  induction hf using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact nr_j X
  | algebraMap c => exact nr_c X c
  | add x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := nr_two X hx hy
    exact ⟨T, fun s hs => by rw [map_add (f := _), (hT s hs).1, (hT s hs).2]⟩
  | inv x _ hx =>
    obtain ⟨T, hT⟩ := hx
    exact ⟨T, fun s hs => by rw [map_inv₀, hT s hs]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := nr_two X hx hy
    exact ⟨T, fun s hs => by rw [map_mul, (hT s hs).1, (hT s hs).2]⟩

end

theorem UpperTheory.V.Z.Kato.Sym.PC.galNear :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K), ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f := by
  intro Ω _ _ _ ε X f
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  set q : Polynomial X.K := p.map (algebraMap _ X.K) with hq
  have hq0 : q ≠ 0 := Polynomial.map_ne_zero hp0
  have hqf : q.eval f = 0 := by
    rw [hq, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hpf
  have hc : ∀ i, Nr X (q.coeff i) := fun i => by
    rw [hq, Polynomial.coeff_map, IntermediateField.algebraMap_apply]
    exact nr_adj X _ (p.coeff i).2
  have hd : ∀ b, b ≠ f → ∃ r, (X.exp b).coeff r ≠ (X.exp f).coeff r := by
    intro b hb
    by_contra h
    push_neg at h
    exact hb (exp_inj X (HahnSeries.ext (funext h)))
  choose TC hTC using hc
  choose! rr hrr using hd
  refine ⟨(q.support.biUnion TC) ∪ ((q.roots.toFinset.erase f).image (fun b => (X.exp f).coeff (rr b))), ?_⟩
  intro s hs
  have hfix : ∀ i, X.gal s (q.coeff i) = q.coeff i := by
    intro i
    by_cases hi : i ∈ q.support
    · exact hTC i s fun z hz => hs z (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, hz⟩))
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero]
  have hmap : q.map (X.gal s).toRingHom = q := by
    ext i
    rw [Polynomial.coeff_map]
    exact hfix i
  have hroot : q.eval (X.gal s f) = 0 := by
    have h1 : (q.map (X.gal s).toRingHom).eval ((X.gal s).toRingHom f) = (X.gal s).toRingHom (q.eval f) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [hmap, hqf, map_zero] at h1
    exact h1
  by_contra hne
  have hb : X.gal s f ∈ q.roots.toFinset.erase f :=
    Finset.mem_erase.mpr ⟨hne, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq0).mpr hroot)⟩
  have hsz := hs ((X.exp f).coeff (rr (X.gal s f)))
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hb, rfl⟩))
  apply hrr _ hne
  rw [X.gal_exp, hsz]
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

theorem UpperTheory.V.Z.Kato.Sym.PC.loc :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (m c d M : ℕ), 0 < m → 1 < c → 1 < d → Nat.Coprime c 6 → Nat.Coprime d 6 → Lv c d M → ∀ t w, IsSec X m t → IsSymb X m c d M t w → ∃ T : Finset Ω, ∀ s s', (∀ z ∈ T, s z = s' z) → ∀ x y, Ok x y → Cgr m (w s x y) (w s' x y) := by
  intro Ω _ _ _ ε X m c d M hm hc hd hc6 hd6 hL t w ht hw
  unfold Lv at hL
  unfold IsSec at ht
  unfold IsSymb at hw
  obtain ⟨hM, hcM, hdM⟩ := hL
  obtain ⟨hgr, hok, -⟩ := rowB Ω M hM
  obtain ⟨-, hadm, -⟩ := admB Ω ε X
  classical
  haveI : NeZero M := ⟨by omega⟩
  have pt : ∀ a b : Row M, Ok a b → IsPt X m (sg X c M a) (sg X d M b) (t (sg X c M a) (sg X d M b)) := by
    intro a b hab
    exact (ht _ _ (sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1).1 (sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1).1).1
  have loc : ∀ a b : Row M, ∃ T : Finset Ω, ∀ r : Gal(Ω/ℚ), (∀ z ∈ T, r z = z) → Ok a b →
      (X.gal r) (sg X c M a) = sg X c M a ∧ (X.gal r) (sg X d M b) = sg X d M b ∧
      Mv X m (X.gal r) r (t (sg X c M a) (sg X d M b)) (t (sg X c M a) (sg X d M b)) 1 := by
    intro a b
    by_cases hab : Ok a b
    · obtain ⟨T1, h1⟩ := PC.galNear Ω ε X (sg X c M a)
      obtain ⟨T2, h2⟩ := PC.galNear Ω ε X (sg X d M b)
      obtain ⟨S, hS⟩ := mvNear Ω ε X m hm _ _ _ (pt a b hab)
      let Tf : X.K → Finset Ω := fun f => Classical.choose (PC.galNear Ω ε X f)
      refine ⟨T1 ∪ T2 ∪ S.biUnion Tf, fun r hr _ => ⟨h1 r (fun z hz => hr z (by simp [hz])), h2 r (fun z hz => hr z (by simp [hz])), ?_⟩⟩
      refine hS _ r (hadm r) (fun f hf => ?_)
      exact Classical.choose_spec (PC.galNear Ω ε X f) r (fun z hz => hr z (by simp only [Finset.mem_union, Finset.mem_biUnion]; exact Or.inr ⟨f, hf, hz⟩))
    · exact ⟨∅, fun r _ h => absurd h hab⟩
  let G : Row M × Row M → Finset Ω := fun p => Classical.choose (loc p.1 p.2)
  refine ⟨Finset.univ.biUnion G, ?_⟩
  intro s s' hss x y hxy
  set r := s'⁻¹ * s
  set a := gr M s⁻¹ x
  set b := gr M s⁻¹ y
  have hab : Ok a b := (hok x y hxy).2.2.1 s⁻¹
  have hr : ∀ z ∈ G (a, b), r z = z := by
    intro z hz
    have := hss z (Finset.mem_biUnion.2 ⟨(a, b), Finset.mem_univ _, hz⟩)
    show s'⁻¹ (s z) = z
    rw [this]
    exact s'.symm_apply_apply z
  obtain ⟨fa, fb, fm⟩ := Classical.choose_spec (loc a b) r hr hab
  have hsr : s' * r = s := by simp [r]
  have hrs : r * s⁻¹ = s'⁻¹ := by simp [r]
  have inv1 : ∀ (q : Gal(Ω/ℚ)) (e : Row M), gr M q (gr M q⁻¹ e) = e := by
    intro q e
    rw [← (hgr _ _ _).1, mul_inv_cancel, (hgr 1 1 e).2]
  have sa := sgB Ω ε X c M hc hc6 hM hcM a (hok a b hab).1
  have sb := sgB Ω ε X d M hd hd6 hM hdM b (hok a b hab).2.1
  have ex : sg X c M (gr M s'⁻¹ x) = sg X c M a := by
    rw [← hrs, (hgr _ _ _).1, ← sa.2.2.1 r, fa]
  have ey : sg X d M (gr M s'⁻¹ y) = sg X d M b := by
    rw [← hrs, (hgr _ _ _).1, ← sb.2.2.1 r, fb]
  have ws' := (hw s' x y hxy).2
  rw [ex, ey] at ws'
  have ws := (hw s x y hxy).2
  have gx : (X.gal s) (sg X c M a) = sg X c M x := by rw [sa.2.2.1 s, inv1]
  have gy : (X.gal s) (sg X d M b) = sg X d M y := by rw [sb.2.2.1 s, inv1]
  have q1 : IsPt X m ((X.gal r) (sg X c M a)) ((X.gal r) (sg X d M b)) (t (sg X c M a) (sg X d M b)) := by
    rw [fa, fb]
    exact pt a b hab
  have q2 : IsPt X m ((X.gal s') ((X.gal r) (sg X c M a))) ((X.gal s') ((X.gal r) (sg X d M b))) (t (sg X c M x) (sg X d M y)) := by
    rw [← gal_mul_apply, ← gal_mul_apply, hsr, gx, gy]
    exact pt x y hxy
  have comp := mvComp Ω ε X m hm (X.gal r) (X.gal s') r s' (hadm r) (hadm s') _ _ _ _ _ (pt a b hab) q1 q2 _ _ fm ws'
  rw [map_one, one_pow, one_mul] at comp
  have eg : (X.gal r).trans (X.gal s') = X.gal s := by
    ext f
    rw [← hsr, gal_mul_apply]
    rfl
  rw [eg, hsr] at comp
  have q3 : IsPt X m ((X.gal s) (sg X c M a)) ((X.gal s) (sg X d M b)) (t (sg X c M x) (sg X d M y)) := by
    rw [gx, gy]
    exact pt x y hxy
  exact ((mvEx Ω ε X m hm (X.gal s) s (hadm s) _ _ _ (pt a b hab)).2.2.2 _ q3 _ _ comp).1 ws
end
