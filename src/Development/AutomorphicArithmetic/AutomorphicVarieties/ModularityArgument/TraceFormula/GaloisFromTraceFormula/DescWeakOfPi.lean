module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfGalWeak
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.OrbitalCosetFiniteness.StUnit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.QuadraticCharacterNorms.QuadCharNorm
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.StableBlockG
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.USide
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLaplaceFactorisation
public import Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.TermId
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.MultiplicityOneBase.ArchimedeanBaseChangeFirst

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.MuEx
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.muEx : UpperTheory.V.Z.Tf.GlobalTraceComparison.MuEx := PositivityTheory.Rg.BcB.F.Fok.Mu3.muExists
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchUnit
theorem UpperTheory.ConvolutionTheory.G2.matchUnit : UpperTheory.V.Z.Tf.GlobalTraceComparison.MatchUnit := PositivityTheory.Rg.Bc.ArchbcB.B.m1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.NeZeroOfFinprod
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.OrbitNormCounting.PolFin
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

theorem UpperTheory.ConvolutionTheory.G3.polFin :
    UpperTheory.ConvolutionTheory.G3.PolFin := by
  intro E _ _ _ hU n S hS C hC hC1
  choose γ hγ0 hγ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E n w (C w) (hC w)
  let g : Pl E → WithZero (Multiplicative ℤ) := fun w => if C w ⊆ GlobalTheory.LFun.KGL w (n := n) then 1 else γ w
  have hlev : ∀ w : Pl E, IsLevel (thL n w) (GlobalTheory.LFun.KGL w (n := n)) (GlobalTheory.LFun.KGL w (n := n)) := fun w =>
    ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl,
      fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩
  refine (GlobalTheory.BCT.GeoFin.finite_ell_bounded E n S hS g
    (fun w => by by_cases h : C w ⊆ GlobalTheory.LFun.KGL w (n := n) <;> simp [g, h, hγ0])
    (hC1.mono fun w h => by simp [g, h])).subset ?_
  rintro P ⟨hP, hPS⟩
  refine ⟨hP, fun w hw => ?_⟩
  obtain ⟨y, hy, e⟩ := hPS w hw
  rw [← e]
  by_cases h : C w ⊆ GlobalTheory.LFun.KGL w (n := n)
  · simp only [g, if_pos h, inv_one]
    exact GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E n w (hlev w) y (h hy)
  · simp only [g, if_neg h]
    exact hγ w y hy
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.TsupportUnit2
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.ConvolutionTheory.G2.lpol_twist {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ)
    (w : Pl E) (g x : GLw n w) :
    UpperTheory.ConvolutionTheory.G3.lpol w (g⁻¹ * x * thL n w g) = UpperTheory.ConvolutionTheory.G3.lpol w x := by
  unfold UpperTheory.ConvolutionTheory.G3.lpol
  rw [GlobalTheory.BCT.ThBasic.nrmL_twist hU]
  simpa using Matrix.charpoly_units_conj g⁻¹ (nrmL n w x).val

private theorem UpperTheory.ConvolutionTheory.G2.exists_supp {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (a b : ℕ)
    (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (φ : GLw a w × GLw b w → ℂ) (h : stTw2 a b w Q₁ Q₂ φ ≠ 0) :
    ∃ y : GLw a w × GLw b w, φ y ≠ 0 ∧ UpperTheory.ConvolutionTheory.G3.lpol w y.1 = Q₁ ∧ UpperTheory.ConvolutionTheory.G3.lpol w y.2 = Q₂ := by
  by_contra hno
  apply h
  unfold stTw2 clSum
  refine finsum_eq_zero_of_forall_eq_zero fun c => ?_
  split_ifs with hc
  · rw [UpperTheory.ConvolutionTheory.G3.orbZero _ _ _ _ _ ?_, mul_zero]
    rintro y ⟨g, hg⟩
    by_contra hy
    have h1 : y.1 = g.1⁻¹ * c.rep.1 * thL a w g.1 := by rw [hg]; rfl
    have h2 : y.2 = g.2⁻¹ * c.rep.2 * thL b w g.2 := by rw [hg]; rfl
    refine hno ⟨y, hy, ?_, ?_⟩
    · rw [h1, UpperTheory.ConvolutionTheory.G2.lpol_twist hU]; exact hc.1
    · rw [h2, UpperTheory.ConvolutionTheory.G2.lpol_twist hU]; exact hc.2
  · rfl

private theorem UpperTheory.ConvolutionTheory.G2.tsupport_unit2 {E : Type} [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) :
    tsupport (UpperTheory.ConvolutionTheory.G2.unit2 a b w) ⊆ (GlobalTheory.LFun.KGL w (n := a) : Set (GLw a w)) ×ˢ (GlobalTheory.LFun.KGL w (n := b) : Set (GLw b w)) := by
  refine closure_minimal ?_ ((GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2.isClosed.prod
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w b).2.isClosed)
  intro y hy
  by_contra hn
  exact hy (Set.indicator_of_notMem hn _)

theorem UpperTheory.ConvolutionTheory.G2.finP :
    UpperTheory.ConvolutionTheory.G2.FinP := by
  intro E _ _ _ hU a b S hS φ hc hae
  have f₁ := UpperTheory.ConvolutionTheory.G3.polFin E hU a S hS (fun w => Prod.fst '' tsupport (φ w))
    (fun w => (hc w).image continuous_fst) (hae.mono fun w hw => by
      rintro _ ⟨y, hy, rfl⟩
      rw [hw] at hy
      exact (UpperTheory.ConvolutionTheory.G2.tsupport_unit2 a b w hy).1)
  have f₂ := UpperTheory.ConvolutionTheory.G3.polFin E hU b S hS (fun w => Prod.snd '' tsupport (φ w))
    (fun w => (hc w).image continuous_snd) (hae.mono fun w hw => by
      rintro _ ⟨y, hy, rfl⟩
      rw [hw] at hy
      exact (UpperTheory.ConvolutionTheory.G2.tsupport_unit2 a b w hy).2)
  refine (f₁.prod f₂).subset ?_
  rintro ⟨P₁, P₂⟩ ⟨h₁, h₂, h⟩
  refine ⟨⟨h₁, fun w hw => ?_⟩, ⟨h₂, fun w hw => ?_⟩⟩
  · obtain ⟨y, hy, e₁, -⟩ := UpperTheory.ConvolutionTheory.G2.exists_supp hU a b w _ _ (φ w) (h w hw)
    exact ⟨y.1, ⟨y, subset_tsupport _ hy, rfl⟩, e₁⟩
  · obtain ⟨y, hy, -, e₂⟩ := UpperTheory.ConvolutionTheory.G2.exists_supp hU a b w _ _ (φ w) (h w hw)
    exact ⟨y.2, ⟨y, subset_tsupport _ hy, rfl⟩, e₂⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.RealProdS
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.RealProd
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.RealSigned
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


open GlobalTheory.LaplaceChar ReciprocityTheory.ChartRestriction.TR.Weyl in
theorem UpperTheory.ConvolutionTheory.G2.realSigned : ∀ (a b : ℕ) (lam : DomWeight (a + b)) (e : ℤ), Odd e → ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → DomWeight a) (l₂ : ι → DomWeight b) (ε : ι → ℂ), (∀ j, ε j = 1 ∨ ε j = -1) ∧ (∀ j, (infOfWeight (l₁ j)).map (· + (b : ℂ) * e / 2) + (infOfWeight (l₂ j)).map (· + (a : ℂ) * e / 2) = infOfWeight lam) ∧ ∀ Q₁ Q₂ : ℂ[X], Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → (∀ z ∈ (Q₁ * Q₂).roots, ‖z‖ = 1) → ((resultant Q₁ Q₂ / (‖resultant Q₁ Q₂‖ : ℂ)) ^ e * ‖resultant Q₁ Q₂‖) * (starRingEnd ℂ) (chAt lam (Q₁ * Q₂)) = ∑ j, ε j * (starRingEnd ℂ) (chAt (l₁ j) Q₁) * (starRingEnd ℂ) (chAt (l₂ j) Q₂) := by
  intro a b lam e he
  obtain ⟨m, rfl⟩ := he
  set K : ℤ := m + 1 with hK
  refine ⟨{J : Finset (Fin (a + b)) // J.card = a}, inferInstance,
    fun J => selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K),
    fun J => selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K),
    fun J => (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * ((-1 : ℂ) ^ (a * b)) ^ K, ?_, ?_, ?_⟩
  · intro J
    beta_reduce
    rw [← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ (by norm_num)]
    rcases Int.even_or_odd (((((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2 : ℕ) : ℤ)) + ((a * b : ℕ) : ℤ) * K) with h | h
    · exact Or.inl h.neg_one_zpow
    · exact Or.inr h.neg_one_zpow
  · intro J
    beta_reduce
    let F : Fin (a + b) → ℂ := fun j => (lam.w j : ℂ) + ((((a + b : ℕ) : ℂ) - 1) / 2 - ((j : ℕ) : ℂ))
    have hL : (infOfWeight (selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K))).map
        (· + (b : ℂ) * ((2 * m + 1 : ℤ) : ℂ) / 2) = J.1.val.map F := by
      rw [← map_orderEmbOfFin J.1 J.2 F]
      unfold infOfWeight
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, selW, selL, F, Pi.add_apply, delta_apply, hK]
      push_cast
      ring
    have hR : (infOfWeight (selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K))).map
        (· + (a : ℂ) * ((2 * m + 1 : ℤ) : ℂ) / 2) = J.1ᶜ.val.map F := by
      rw [← map_orderEmbOfFin J.1ᶜ (k := b) (by rw [Finset.card_compl, J.2]; simp) F]
      unfold infOfWeight
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun k _ => ?_
      simp only [Function.comp_apply, selW, selR, F, Pi.add_apply, delta_apply, hK]
      push_cast
      ring
    rw [hL, hR, ← Multiset.map_add (f := _), val_add_compl]
    rfl
  · intro Q₁ Q₂ h1 h2 hd1 hd2 hsep hroot
    beta_reduce
    have exists_eq_prod_X_sub_C : ∀ (n : ℕ) (Q : ℂ[X]), Q.Monic → Q.natDegree = n →
        ∃ α : Fin n → ℂ, Q = ∏ i, (X - C (α i)) := by
      intro n
      induction n with
      | zero =>
        intro Q hm hd
        exact ⟨Fin.elim0, by rw [Fin.prod_univ_zero]; exact Polynomial.eq_one_of_monic_natDegree_zero hm hd⟩
      | succ n ih =>
        intro Q hm hd
        obtain ⟨r, hr⟩ := IsAlgClosed.exists_root Q (by
          rw [degree_eq_natDegree hm.ne_zero, hd]; exact_mod_cast Nat.succ_ne_zero n)
        have hdiv : (X - C r) * (Q /ₘ (X - C r)) = Q := mul_divByMonic_eq_iff_isRoot.mpr hr
        have hm' : (Q /ₘ (X - C r)).Monic := (monic_X_sub_C r).of_mul_monic_left (by rw [hdiv]; exact hm)
        have hd' : (Q /ₘ (X - C r)).natDegree = n := by
          rw [natDegree_divByMonic _ (monic_X_sub_C r), hd, natDegree_X_sub_C]; rfl
        obtain ⟨α, hα⟩ := ih _ hm' hd'
        refine ⟨Fin.cons r α, ?_⟩
        rw [Fin.prod_univ_succ, Fin.cons_zero]
        simp only [Fin.cons_succ]
        rw [← hα, hdiv]
    obtain ⟨α, rfl⟩ := exists_eq_prod_X_sub_C a Q₁ h1 hd1
    obtain ⟨β, rfl⟩ := exists_eq_prod_X_sub_C b Q₂ h2 hd2
    have hprod : (∏ i, (X - C (α i))) * ∏ j, (X - C (β j)) = ∏ i, (X - C (Fin.addCases α β i)) := by
      rw [Fin.prod_univ_add]; simp
    rw [hprod] at hsep hroot ⊢
    have htinj : Function.Injective (Fin.addCases α β : Fin (a + b) → ℂ) := separable_prod_X_sub_C_iff.mp hsep
    have hmon : (∏ i, (X - C ((Fin.addCases α β : Fin (a + b) → ℂ) i))).Monic :=
      monic_prod_of_monic _ _ fun j _ => monic_X_sub_C _
    have htn : ∀ i, ‖(Fin.addCases α β : Fin (a + b) → ℂ) i‖ = 1 := fun i => hroot _ (by
      rw [mem_roots hmon.ne_zero, IsRoot, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp))
    have ht0 : ∀ i, (Fin.addCases α β : Fin (a + b) → ℂ) i ≠ 0 := fun i h => by simpa [h] using htn i
    have hα : ∀ i, ‖α i‖ = 1 := fun i => by simpa using htn (Fin.castAdd b i)
    have hβ : ∀ j, ‖β j‖ = 1 := fun j => by simpa using htn (Fin.natAdd a j)
    have hα0 : ∀ i, α i ≠ 0 := fun i h => by simpa [h] using hα i
    have hβ0 : ∀ j, β j ≠ 0 := fun j h => by simpa [h] using hβ j
    have hαinj : Function.Injective α := fun i j h =>
      Fin.castAdd_injective _ _ (htinj (by simpa using h))
    have hβinj : Function.Injective β := fun i j h =>
      Fin.natAdd_injective _ _ (htinj (by simpa using h))
    have hne : ∀ i j, α i ≠ β j := fun i j h => by
      have := htinj (show (Fin.addCases α β : Fin (a + b) → ℂ) (Fin.castAdd b i) = Fin.addCases α β (Fin.natAdd a j) by
        simpa using h)
      have := congrArg Fin.val this
      simp at this
      omega
    rw [chAt_prod_eq_gtChar lam _ htinj ht0]
    simp only [chAt_prod_eq_gtChar _ α hαinj hα0, chAt_prod_eq_gtChar _ β hβinj hβ0]
    rw [resultant_prod α β]
    have hph := GlobalTheory.resultant_phase_unit_circle a b α β hα hβ hne K
    simp only at hph
    rw [show (2 * m + 1 : ℤ) = 2 * K - 1 by rw [hK]; ring, hph]
    set R := ∏ i, ∏ j, (α i - β j) with hRdef

    have hW := weylGT ℂ (a + b) lam.w lam.anti _ ht0
    rw [wden_addCases] at hW
    let α' : Fin a → ℂˣ := fun i => Units.mk0 (α i) (hα0 i)
    let β' : Fin b → ℂˣ := fun j => Units.mk0 (β j) (hβ0 j)
    have hLap := GlobalTheory.weylNumerator_laplace a b α' β' (lam.w + delta (a + b))
    have hLHS : alt (a + b) (lam.w + delta (a + b)) (Fin.addCases α β) =
        (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α' β' i : ℂˣ) ^ (lam.w + delta (a + b)) j : ℂˣ) : ℂ)).det := by
      unfold alt
      congr 1
      ext i j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [α', β', Units.val_zpow_eq_zpow_val]
    have hA : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        (Matrix.of fun i k : Fin a => ((α' i ^ (lam.w + delta (a + b)) (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det =
          wden a α * gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α := by
      intro J
      rw [weylGT ℂ a _ (antitone_select lam (selL J) (selL_strictMono J)) α hα0]
      unfold alt
      congr 1
      ext i k
      simp [α', Units.val_zpow_eq_zpow_val, selL]
    have hB : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        (Matrix.of fun i k : Fin b => ((β' i ^ (lam.w + delta (a + b))
            (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det =
          wden b β * gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β := by
      intro J
      rw [weylGT ℂ b _ (antitone_select lam (selR J) (selR_strictMono J)) β hβ0]
      unfold alt
      congr 1
      ext i k
      simp [β', Units.val_zpow_eq_zpow_val, selR]
    rw [hLHS, hLap] at hW
    simp only [hA, hB] at hW
    rw [← hRdef] at hW
    have hwden : ∀ {c : ℕ} (x : Fin c → ℂ), Function.Injective x → wden c x ≠ 0 := by
      intro c x hx
      unfold wden
      refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j _ => ?_
      split_ifs with h
      · exact sub_ne_zero.mpr (hx.ne h.ne)
      · exact one_ne_zero
    have key : R * gtChar (a + b) lam.w (fun i => Fin.addCases α β i) =
        ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) *
          gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α *
          gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β := by
      apply mul_left_cancel₀ (mul_ne_zero (hwden α hαinj) (hwden β hβinj))
      rw [← mul_assoc, hW, Finset.mul_sum]
      exact Finset.sum_congr rfl fun J _ => by ring
    have hc := congrArg (starRingEnd ℂ) key
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, map_sum, map_pow, map_neg, map_one] at hc
    have hsA : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        gtChar a (selW lam (selL J) (selL_strictMono J) (-(b : ℤ) * K)).w α =
          (∏ i, α i) ^ (-(b : ℤ) * K) * gtChar a (fun k => (lam.w + delta (a + b)) (selL J k) - delta a k) α :=
      fun J => sq_gt_shift a _ _ α hα0
    have hsB : ∀ J : {J : Finset (Fin (a + b)) // J.card = a},
        gtChar b (selW lam (selR J) (selR_strictMono J) (-(a : ℤ) * K)).w β =
          (∏ j, β j) ^ (-(a : ℤ) * K) * gtChar b (fun k => (lam.w + delta (a + b)) (selR J k) - delta b k) β :=
      fun J => sq_gt_shift b _ _ β hβ0
    have hPα : ‖∏ i, α i‖ = 1 := by rw [norm_prod]; simp [hα]
    have hPβ : ‖∏ j, β j‖ = 1 := by rw [norm_prod]; simp [hβ]
    have cA : (starRingEnd ℂ) ((∏ i, α i) ^ (-(b : ℤ) * K)) = ((∏ i, α i) ^ b) ^ K := by
      rw [map_zpow₀, conj_eq_inv_of_norm_one hPα, _root_.inv_zpow', neg_mul, neg_neg, _root_.zpow_mul, zpow_natCast]
    have cB : (starRingEnd ℂ) ((∏ j, β j) ^ (-(a : ℤ) * K)) = ((∏ j, β j) ^ a) ^ K := by
      rw [map_zpow₀, conj_eq_inv_of_norm_one hPβ, _root_.inv_zpow', neg_mul, neg_neg, _root_.zpow_mul, zpow_natCast]
    simp only [hsA, hsB, map_mul, cA, cB]
    calc (starRingEnd ℂ) R * ((-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ K *
          (starRingEnd ℂ) (gtChar (a + b) lam.w fun i => Fin.addCases α β i)
        = ((-1) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ K *
          ((starRingEnd ℂ) R * (starRingEnd ℂ) (gtChar (a + b) lam.w fun i => Fin.addCases α β i)) := by ring
      _ = _ := by
        rw [hc, Finset.mul_sum]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [_root_.mul_zpow, _root_.mul_zpow]
        ring
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.realProd :
    UpperTheory.ConvolutionTheory.G2.RealProd := by
  intro E _ _ _ n a b hab e he lam
  subst hab
  choose ι hι l₁ l₂ ε hε hinf hid using fun v : InfinitePlace E => UpperTheory.ConvolutionTheory.G2.realSigned a b (lam v) (e v) (he v)
  let s : ∀ v, ι v → ℤˣ := fun v j => if ε v j = 1 then 1 else -1
  have hs : ∀ v j, ((s v j : ℤ) : ℂ) = ε v j := by
    intro v j
    by_cases h : ε v j = 1
    · simp [s, h]
    · have h' := (hε v j).resolve_left h
      simp only [s, if_neg h]
      rw [h']; simp
  refine ⟨∀ v, ι v, inferInstance, fun i v => l₁ v (i v), fun i v => l₂ v (i v), fun i => ∏ v, s v (i v),
    fun i v => hinf v (i v), ?_⟩
  rintro P₁ P₂ ⟨hm₁, hd₁, hs₁, hr₁⟩ ⟨hm₂, hd₂, hs₂, hr₂⟩ hc
  have key : ∀ v : InfinitePlace E, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v *
      (starRingEnd ℂ) (chAt (lam v) ((P₁ * P₂).map v.embedding)) =
      ∑ j, ε v j * (starRingEnd ℂ) (chAt (l₁ v j) (P₁.map v.embedding)) *
        (starRingEnd ℂ) (chAt (l₂ v j) (P₂.map v.embedding)) := by
    intro v
    have hR : resultant (P₁.map v.embedding) (P₂.map v.embedding) = v.embedding (resultant P₁ P₂) := by
      rw [natDegree_map, natDegree_map, resultant_map_map]
    have h := hid v (P₁.map v.embedding) (P₂.map v.embedding) (hm₁.map _) (hm₂.map _)
      (by rw [natDegree_map, hd₁]) (by rw [natDegree_map, hd₂])
      (by rw [← Polynomial.map_mul]; exact (hs₁.mul hs₂ hc).map)
      (by
        intro z hz
        rw [roots_mul ((hm₁.map _).mul (hm₂.map _)).ne_zero, Multiset.mem_add] at hz
        exact hz.elim (hr₁ _ z) (hr₂ _ z))
    rw [hR] at h
    rw [Polynomial.map_mul]
    exact h
  unfold chW
  rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun v _ => key v, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Units.coe_prod, Int.cast_prod, hs]
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def emptyW : DomWeight 0 := ⟨fun i => i.elim0, fun i => i.elim0⟩

private theorem chAt_rank_zero (l : DomWeight 0) : chAt l (1 : ℂ[X]) = 1 := by
  have h := GlobalTheory.LaplaceChar.chAt_prod_eq_gtChar l (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  have hw : l.w = (0 : Fin 0 → ℤ) := Subsingleton.elim _ _
  rw [hw, ReciprocityTheory.ChartRestriction.TR.Weyl.gtChar_zero] at h
  simpa using h

private theorem chW_rank_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    (l : InfinitePlace E → DomWeight 0) : chW l (1 : E[X]) = 1 := by
  unfold chW
  simp [chAt_rank_zero]

private theorem infOfWeight_rank_zero (l : DomWeight 0) : infOfWeight l = 0 := by
  simp [infOfWeight]

private theorem eq_one_of_ell_zero {E : Type} [Field E] {P : E[X]} (h : P ∈ Ell E 0) : P = 1 :=
  (Polynomial.Monic.natDegree_eq_zero (show P.Monic from h.1)).mp h.2.1

private theorem phase_one {E : Type} [Field E] [NumberField E] [IsCMField E] (e : InfinitePlace E → ℤ) (v : InfinitePlace E) :
    UpperTheory.ConvolutionTheory.G2.phase e (1 : E) v = 1 := by
  simp [UpperTheory.ConvolutionTheory.G2.phase]

theorem UpperTheory.ConvolutionTheory.G2.realProdS :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ), a + b = n → ∀ e : InfinitePlace E → ℤ, (∀ v, Odd (e v)) →
    ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (l₁ : ι → InfinitePlace E → DomWeight a)
      (l₂ : ι → InfinitePlace E → DomWeight b) (sg : ι → ℤˣ), ((a = 0 ∨ b = 0) → (∃ i₀ : ι, ∀ i, i = i₀) ∧ ∀ i, sg i = 1) ∧
      (∀ i v, (infOfWeight (l₁ i v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ i v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
        infOfWeight (lam v)) ∧
      ∀ P₁ P₂ : E[X], P₁ ∈ Ell E a → P₂ ∈ Ell E b → IsCoprime P₁ P₂ →
        (∏ v, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v) * chW lam (P₁ * P₂) = ∑ i, ((sg i : ℤ) : ℂ) * chW (l₁ i) P₁ * chW (l₂ i) P₂ := by
  intro E _ _ _ n a b hab e he lam
  by_cases hz : a = 0 ∨ b = 0
  · rcases hz with rfl | rfl
    · obtain rfl : b = n := by omega
      refine ⟨Unit, inferInstance, fun _ _ => emptyW, fun _ => lam, fun _ => 1,
        fun _ => ⟨⟨(), fun _ => rfl⟩, fun _ => rfl⟩, ?_, ?_⟩
      · intro _ v
        simp [infOfWeight_rank_zero]
      · intro P₁ P₂ h₁ _ _
        obtain rfl := eq_one_of_ell_zero h₁
        simp [phase_one, chW_rank_zero]
    · obtain rfl : a = n := by omega
      refine ⟨Unit, inferInstance, fun _ => lam, fun _ _ => emptyW, fun _ => 1,
        fun _ => ⟨⟨(), fun _ => rfl⟩, fun _ => rfl⟩, ?_, ?_⟩
      · intro _ v
        simp [infOfWeight_rank_zero]
      · intro P₁ P₂ _ h₂ _
        obtain rfl := eq_one_of_ell_zero h₂
        simp [phase_one, chW_rank_zero]
  · obtain ⟨ι, hι, l₁, l₂, sg, hinf, hid⟩ := UpperTheory.ConvolutionTheory.G2.realProd E n a b hab e he lam
    exact ⟨ι, hι, l₁, l₂, sg, fun h => absurd h hz, hinf, hid⟩
end

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem finsum_exch {α ι : Type} [Fintype ι] (T s : Set α) (hs : s.Finite) (F : α → ℂ) (c : ι → ℂ)
    (G : ι → α → ℂ) (h : ∀ p ∈ T, F p = ∑ i, c i * G i p) (h0 : ∀ i, ∀ p ∈ T, G i p ≠ 0 → p ∈ s) :
    ∑ᶠ p ∈ T, F p = ∑ i, c i * ∑ᶠ p ∈ T, G i p := by
  have hf : (T ∩ s).Finite := hs.inter_of_right T
  have e1 : ∀ i, ∑ᶠ p ∈ T, G i p = ∑ p ∈ hf.toFinset, G i p := fun i => by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
    exact finsum_mem_inter_support_eq' _ _ _ fun p hp => ⟨fun hT => ⟨hT, h0 i p hT hp⟩, fun hT => hT.1⟩
  have e2 : ∑ᶠ p ∈ T, F p = ∑ p ∈ hf.toFinset, F p := by
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf]
    refine finsum_mem_inter_support_eq' _ _ _ fun p hp => ⟨fun hT => ⟨hT, ?_⟩, fun hT => hT.1⟩
    by_contra hn
    apply hp
    rw [h p hT]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [not_not.1 fun hG => hn (h0 i p hT hG), mul_zero]
  simp only [e1, e2, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun p hp => h p (hf.mem_toFinset.1 hp).1

private theorem ne_zero_of_finprod {α : Type} (S : Set α) (g : α → ℂ) (hf : (S ∩ Function.mulSupport g).Finite)
    (h : ∏ᶠ w ∈ S, g w ≠ 0) : ∀ w ∈ S, g w ≠ 0 := by
  intro w hw h0
  apply h
  rw [finprod_mem_eq_prod _ hf]
  refine Finset.prod_eq_zero (i := w) ?_ h0
  simp [hw, Function.mem_mulSupport, h0]

theorem UpperTheory.ConvolutionTheory.G2.g2s :
    UpperTheory.V.Z.Tf.GlobalTraceComparison.G2s := by
  intro E _ _ _ hE n _ μ e hμ lam
  have hle : ∀ a : Fin (n + 1), (a : ℕ) ≤ n := fun a => Nat.lt_succ_iff.1 a.2
  choose ι fι l₁ l₂ sg hu hw hch using fun a : Fin (n + 1) =>
    UpperTheory.ConvolutionTheory.G2.realProdS E n a (n - a) (Nat.add_sub_cancel' (hle a)) e hμ.2.2.2.1 lam
  have key : ∀ a : Fin (n + 1), ((a : ℕ) = 0 ∨ n - a = 0) →
      ∃ i : Σ a, ι a, (i.1 : ℕ) = a ∧ sg i.1 i.2 = 1 ∧ ∀ j : Σ a, ι a, (j.1 : ℕ) = a → j = i := fun a h => by
    obtain ⟨⟨i₀, hi⟩, hs⟩ := hu a h
    refine ⟨⟨a, i₀⟩, rfl, hs i₀, ?_⟩
    rintro ⟨a', j⟩ hj
    obtain rfl : a' = a := Fin.ext hj
    rw [hi j]
  refine ⟨Σ a, ι a, inferInstance, fun i => i.1, fun i => l₁ i.1 i.2, fun i => l₂ i.1 i.2, fun i => sg i.1 i.2,
    fun i => ⟨hle i.1, hw i.1 i.2⟩, key (Fin.last n) (Or.inr (by simp)), key 0 (Or.inl rfl), ?_⟩
  intro S hS K' f φ _ _ hφ
  unfold geomU
  rw [Finset.sum_range, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun a _ => ?_
  obtain ⟨⟨K₁, K₂, -, -, hH, hU⟩, hM⟩ := hφ a (hle a)
  have hU' : ∀ᶠ w in cofinite, φ a w = UpperTheory.ConvolutionTheory.G2.unit2 a (n - a) w := hU
  have hT := UpperTheory.ConvolutionTheory.G2.termId E hE μ e hμ S hS n a (n - a) f (φ a) hU' hM
  refine finsum_exch _ _ (UpperTheory.ConvolutionTheory.G2.finP E hE a (n - a) S hS (φ a) (fun w => (hH w).1) hU') _ _ _ ?_ ?_
  · rintro ⟨P₁, P₂⟩ ⟨h₁, h₂, hc⟩
    have k := hch a P₁ P₂ h₁ h₂ hc
    rw [(hT P₁ P₂ h₁ h₂ hc).2, (GlobalTheory.BCT.KapMul.kap_mul E hE a (n - a) P₁ P₂ h₁ h₂ hc).1]
    calc _ = kap P₁ * kap P₂ * (∏ᶠ w ∈ S, stTw2 a (n - a) w (atPl w P₁) (atPl w P₂) (φ a w)) *
          ((∏ v, UpperTheory.ConvolutionTheory.G2.phase e (resultant P₁ P₂) v) * chW lam (P₁ * P₂)) := by ring
      _ = _ := by
        rw [k, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
  · rintro i ⟨P₁, P₂⟩ ⟨h₁, h₂, hc⟩ hG
    exact ⟨h₁, h₂, ne_zero_of_finprod S _ (hT P₁ P₂ h₁ h₂ hc).1 (right_ne_zero_of_mul hG)⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.WeightRankUnits.MatchSplit
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.ConvolutionTheory.G2.matchSplit : UpperTheory.V.Z.Tf.GlobalTraceComparison.MatchSplit := by
  intro E _ _ _ w hw n a b h μ f ⟨K', hKo, hKl, hf⟩
  obtain rfl : b = n - a := by omega
  have ha : a ≤ n := by omega
  have hL : IsLevel (MonoidHom.id _) (KL n w) K' := ⟨hKo, hKl, fun k hk => hk⟩
  have hμ : IsOpen {x | μ.loc w x = 1} :=
    GroundTheory.Global.isOpen_ker_of_continuous w GroundTheory.Global.Complex.units_noSmallSubgroups (μ.loc w)
      (μ.2.1.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele w))
  obtain ⟨K₁, K₂, -, h₁, h₂, -, -, -, -, -, -, hH⟩ := GlobalTheory.T.exists_block_levels_twistedConstantTerm_split_place E n a ha w hw (μ.loc w) hμ K' hL
  exact ⟨⟨K₁.prod K₂, h₁.1.prod h₂.1, Subgroup.prod_mono h₁.2.1 h₂.2.1, hH f hf⟩, GlobalTheory.T.splitPlace_twistedConstantTerm_matches E n a ha w hw (μ.loc w) K' hL f hf⟩
end

open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem runTh_of_pi (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : PositivityTheory.Rg.BcB.Desc.GrowthPiJ) : RunTh :=
  runTh_of UpperTheory.ConvolutionTheory.G2.uSide UpperTheory.ConvolutionTheory.G2.g2s muEx UpperTheory.ConvolutionTheory.G2.matchUnit UpperTheory.ConvolutionTheory.G2.matchSplit Th.stUnit
    (endoBlockG cuspReadI) (stableBlockG cuspReadI h1 h2 h3 h4 h5)

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
