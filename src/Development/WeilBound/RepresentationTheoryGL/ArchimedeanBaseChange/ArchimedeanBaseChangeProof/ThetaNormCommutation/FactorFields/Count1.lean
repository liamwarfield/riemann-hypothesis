module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TwistedTraceFormulaEllipticExpansion
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.IsLevelKGL
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PInertBase
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PParam

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PGenUnit
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.GenUnitP

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  rw [hR, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun q hq => absurd (Subsingleton.elim q 1) hq)]
  simp

theorem ind_const {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * y * θ (x * k))) =
      fun _ => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * y * θ x) := by
  funext k
  have e : (x * (k : G))⁻¹ * y * θ (x * k) = (k : G)⁻¹ * (x⁻¹ * y * θ x) * θ k := by
    simp only [map_mul, _root_.mul_inv_rev]; group
  rw [e]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from
      K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) (hKθ _ k.2)), Set.indicator_of_mem (show _ ∈ (K : Set G) from hm)]
    rfl
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), Set.indicator_of_notMem]
    intro h
    apply hm
    have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem (hKθ _ k.2))
    simpa [mul_assoc] using this

theorem summand_eq {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    GlobalTheory.TwOrbConj.summand θ K y ((K : Set G).indicator 1) x =
      if x⁻¹ * y * θ x ∈ K then
        (((twCent θ y ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) else 0 := by
  unfold GlobalTheory.TwOrbConj.summand
  rw [ind_const θ K hKθ y x, avg_const]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from hm), if_pos hm]; simp
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), if_neg hm]; simp

end PositivityTheory.Rg.BcB.G3.GenUnitP

theorem PositivityTheory.Rg.BcB.G3.genUnit_pf : PositivityTheory.Rg.BcB.G3.GenUnit := by
  intro G _ _ _ θ K z hKθ hzK huniq hcptK g
  have hidx : ∀ x : G, (rStab fun k : K =>
      (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * z * θ (x * k))).index ≠ 0 := by
    intro x
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.ind_const θ K hKθ z x]
    have : rStab (fun _ : K => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * z * θ x)) = ⊤ := by
      ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
    rw [this, Subgroup.index_top]
    exact one_ne_zero
  rw [GlobalTheory.TwOrbConj.twOrb_twConj G θ K z g ((K : Set G).indicator 1) hidx]
  have hcpt : cptPart (twCent θ z) ≤ twCent θ z ⊓ K :=
    le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1)
      ((Subgroup.closure_le _).2 fun t ht => hcptK t ht.1 ht.2)
  have hval : GlobalTheory.TwOrbConj.summand θ K z ((K : Set G).indicator 1) 1 = 1 := by
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z 1, if_pos (by simpa using hzK),
      GlobalTheory.TwOrbConj.map_conj_self K (K.one_mem), (Subgroup.relIndex_eq_one).2 hcpt]
    simp
  rw [GlobalTheory.TwOrbConj.twOrb_eq, finsum_eq_single _ (DoubleCoset.mk (twCent θ z) K 1)]
  · obtain ⟨t, ht, k, hk, he⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
      (DoubleCoset.out_eq' (DoubleCoset.mk (twCent θ z) K 1)).symm
    rw [he, GlobalTheory.TwOrbConj.summand_rep θ K z _ 1 ht hk, hval]
  · intro q hq
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z]
    split_ifs with hm
    · exfalso
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := huniq _ hm
      symm
      conv_rhs => rw [← DoubleCoset.out_eq' q]
      rw [DoubleCoset.eq]
      exact ⟨t, ht, k, hk, by rw [he]; group⟩
    · rfl
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.SuppPf
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.SuppP
end PositivityTheory.Rg.BcB.G3.SuppP

theorem PositivityTheory.Rg.BcB.G3.supp_pf : PositivityTheory.Rg.BcB.G3.Supp := by
  intro G _ _ θ K y f h
  by_contra hne
  push Not at hne
  apply h
  unfold twOrb avg
  simp only [hne, finsum_zero, mul_zero]
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PSplitSq
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem splitSq_pf (h1 : TensorCompl) : SplitSq := by
  intro E _ _ _ s d hs hcs hd w hw
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  obtain ⟨u, hne, hu⟩ := hw
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) :=
    ⟨u, w, hne, congrArg HeightOneSpectrum.asIdeal hu, rfl⟩
  obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hcm hv rfl
  refine ⟨τ s, ?_⟩
  have key : τ (algebraMap (maximalRealSubfield E) E d) = τ s * τ s := by rw [hd, pow_two, map_mul]
  exact (τ.commutes d).symm.trans key

end PositivityTheory.Rg.BcB.G3

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.Count1Pf
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.BcB.G3.count1_pf (h1 : Param) : Count1 := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    h1 E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two (K i) (L i) (hR i) (hC i) (x i) (hA i)

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PStruct
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.StructP

section Fac

variable {E : Type} [Field E]

abbrev Fac (P : E[X]) : Type := {Q // Q ∈ (UniqueFactorizationMonoid.normalizedFactors P).toFinset}

theorem fac_mem {P : E[X]} (Q : Fac P) : Q.1 ∈ UniqueFactorizationMonoid.normalizedFactors P :=
  Multiset.mem_toFinset.1 Q.2

theorem fac_irr {P : E[X]} (Q : Fac P) : Irreducible Q.1 :=
  UniqueFactorizationMonoid.irreducible_of_normalized_factor _ (fac_mem Q)

instance factIrr {P : E[X]} (Q : Fac P) : Fact (Irreducible Q.1) := ⟨fac_irr Q⟩

theorem fac_monic {P : E[X]} (Q : Fac P) : Q.1.Monic := by
  have h := UniqueFactorizationMonoid.normalize_normalized_factor _ (fac_mem Q)
  rw [← h]
  exact Polynomial.monic_normalize (fac_irr Q).ne_zero

theorem fac_dvd {P : E[X]} (Q : Fac P) : Q.1 ∣ P :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (fac_mem Q)

theorem fac_coprime (P : E[X]) : Pairwise (Function.onFun IsCoprime fun Q : Fac P => Q.1) := by
  intro Q Q' hne
  refine (Irreducible.coprime_iff_not_dvd (fac_irr Q)).2 fun hd => hne ?_
  exact Subtype.ext (Polynomial.eq_of_monic_of_associated (fac_monic Q) (fac_monic Q')
    ((fac_irr Q).associated_of_dvd (fac_irr Q') hd))

theorem nodup_fac {P : E[X]} (hP : P.Separable) : (UniqueFactorizationMonoid.normalizedFactors P).Nodup :=
  (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP.ne_zero).1 hP.squarefree

theorem prod_fac {P : E[X]} (hm : P.Monic) (hP : P.Separable) : ∏ Q : Fac P, Q.1 = P := by
  rw [Finset.prod_coe_sort (UniqueFactorizationMonoid.normalizedFactors P).toFinset (fun Q => Q),
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (nodup_fac hP).dedup, Multiset.map_id']
  have hmon : (UniqueFactorizationMonoid.normalizedFactors P).prod.Monic := by
    simpa using Polynomial.monic_multiset_prod_of_monic (UniqueFactorizationMonoid.normalizedFactors P) (fun Q => Q)
      (fun Q hQ => fac_monic (⟨Q, Multiset.mem_toFinset.2 hQ⟩ : Fac P))
  exact Polynomial.eq_of_monic_of_associated hmon hm (UniqueFactorizationMonoid.prod_normalizedFactors hP.ne_zero)

theorem card_fac {P : E[X]} (hP : P.Separable) : Fintype.card (Fac P) = nfac P := by
  rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (nodup_fac hP)]
  rfl

theorem fac_roots {P : E[X]} (hm : P.Monic) (hr : ∀ τ : E →+* ℂ, ∀ z ∈ (P.map τ).roots, ‖z‖ = 1) (Q : Fac P) :
    ∀ τ : E →+* ℂ, ∀ z ∈ (Q.1.map τ).roots, ‖z‖ = 1 := fun τ z hz =>
  hr τ z (Multiset.mem_of_le (Polynomial.roots.le_of_dvd (hm.map τ).ne_zero (Polynomial.map_dvd τ (fac_dvd Q))) hz)

theorem exists_rep (P : E[X]) (z : ∀ Q : Fac P, AdjoinRoot Q.1) :
    ∃ f : E[X], ∀ Q : Fac P, AdjoinRoot.mk Q.1 f = z Q := by
  have hcop : Pairwise (Function.onFun IsCoprime fun Q : Fac P => (Ideal.span {Q.1} : Ideal E[X])) := by
    intro Q Q' h
    exact (Ideal.isCoprime_span_singleton_iff _ _).2 (fac_coprime P h)
  obtain ⟨x, hx⟩ := (Ideal.quotientInfRingEquivPiQuotient _ hcop).surjective z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨f, fun Q => congrFun hx Q⟩

end Fac

section Ev

variable {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E)

theorem aeval_eq_zero_iff (hs : N.charpoly.Separable) (f : E[X]) :
    aeval N f = 0 ↔ ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 f = 0 := by
  constructor
  · intro h Q
    exact AdjoinRoot.mk_eq_zero.2 ((fac_dvd Q).trans (GlobalTheory.ClassParam.charpoly_dvd_of_aeval N hs f h))
  · intro h
    have hd : ∏ Q : Fac N.charpoly, Q.1 ∣ f :=
      Fintype.prod_dvd_of_coprime (fac_coprime _) fun Q => AdjoinRoot.mk_eq_zero.1 (h Q)
    rw [prod_fac (Matrix.charpoly_monic N) hs] at hd
    obtain ⟨k, rfl⟩ := hd
    rw [map_mul, Matrix.aeval_self_charpoly, zero_mul]

theorem aeval_eq_iff (hs : N.charpoly.Separable) (f g : E[X]) :
    aeval N f = aeval N g ↔ ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 f = AdjoinRoot.mk Q.1 g := by
  rw [← sub_eq_zero, ← map_sub, aeval_eq_zero_iff N hs]
  simp only [map_sub, sub_eq_zero]

variable {F : Type} [Field F] [Algebra F E] {K : Fac N.charpoly → Type} [∀ Q, Field (K Q)] [∀ Q, Algebra F (K Q)]
  (j : ∀ Q : Fac N.charpoly, K Q →+* AdjoinRoot Q.1)

def repOf (a : ∀ Q, K Q) : E[X] := (exists_rep N.charpoly fun Q => j Q (a Q)).choose

theorem repOf_spec (a : ∀ Q, K Q) (Q : Fac N.charpoly) : AdjoinRoot.mk Q.1 (repOf N j a) = j Q (a Q) :=
  (exists_rep N.charpoly fun Q => j Q (a Q)).choose_spec Q

def rhoFun (a : ∀ Q, K Q) : Matrix (Fin n) (Fin n) E := aeval N (repOf N j a)

theorem rhoFun_eq (hs : N.charpoly.Separable) (a : ∀ Q, K Q) (f : E[X])
    (hf : ∀ Q, AdjoinRoot.mk Q.1 f = j Q (a Q)) : rhoFun N j a = aeval N f :=
  (aeval_eq_iff N hs _ _).2 fun Q => (repOf_spec N j a Q).trans (hf Q).symm

def rho (hs : N.charpoly.Separable)
    (hj : ∀ Q x, j Q (algebraMap F (K Q) x) = AdjoinRoot.of Q.1 (algebraMap F E x)) :
    (∀ Q, K Q) →ₐ[F] Matrix (Fin n) (Fin n) E where
  toFun := rhoFun N j
  map_one' := by
    show rhoFun N j 1 = 1
    rw [rhoFun_eq N j hs 1 1 (fun Q => by rw [map_one, Pi.one_apply, map_one]), map_one]
  map_mul' a b := by
    show rhoFun N j (a * b) = rhoFun N j a * rhoFun N j b
    rw [rhoFun_eq N j hs (a * b) (repOf N j a * repOf N j b)
      (fun Q => by rw [map_mul, repOf_spec, repOf_spec, Pi.mul_apply, map_mul]), map_mul]
    rfl
  map_zero' := by
    show rhoFun N j 0 = 0
    rw [rhoFun_eq N j hs 0 0 (fun Q => by rw [map_zero, Pi.zero_apply, map_zero]), map_zero]
  map_add' a b := by
    show rhoFun N j (a + b) = rhoFun N j a + rhoFun N j b
    rw [rhoFun_eq N j hs (a + b) (repOf N j a + repOf N j b)
      (fun Q => by rw [map_add (f := _), repOf_spec, repOf_spec, Pi.add_apply, map_add (f := _)]), map_add (f := _)]
    rfl
  commutes' x := by
    show rhoFun N j _ = _
    rw [rhoFun_eq N j hs _ (C (algebraMap F E x)) (fun Q => by rw [Pi.algebraMap_apply, hj, AdjoinRoot.mk_C]),
      aeval_C, IsScalarTower.algebraMap_apply F E (Matrix (Fin n) (Fin n) E)]

variable (hs : N.charpoly.Separable)
  (hj : ∀ Q x, j Q (algebraMap F (K Q) x) = AdjoinRoot.of Q.1 (algebraMap F E x))

theorem rho_apply (a : ∀ Q, K Q) : rho N j hs hj a = aeval N (repOf N j a) := rfl

theorem rho_injective : Function.Injective (rho N j hs hj) := by
  intro a b hab
  rw [rho_apply, rho_apply] at hab
  have h := (aeval_eq_iff N hs _ _).1 hab
  funext Q
  apply (j Q).injective
  rw [← repOf_spec N j a Q, ← repOf_spec N j b Q]
  exact h Q

theorem rho_comm (a : ∀ Q, K Q) : rho N j hs hj a * N = N * rho N j hs hj a := by
  rw [rho_apply]
  have h : aeval N (repOf N j a * X) = aeval N (X * repOf N j a) := by rw [mul_comm]
  rwa [map_mul, map_mul, aeval_X] at h

theorem rho_span (s : E)
    (hspan : ∀ (Q : Fac N.charpoly) (z : AdjoinRoot Q.1), ∃ (a b : K Q), z = j Q a + AdjoinRoot.of Q.1 s * j Q b)
    (x : Matrix (Fin n) (Fin n) E) (hx : x * N = N * x) :
    ∃ a b, x = rho N j hs hj a + s • (rho N j hs hj b : Matrix (Fin n) (Fin n) E) := by
  obtain ⟨f, rfl⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm N x hs hx.symm
  choose a b hab using fun Q => hspan Q (AdjoinRoot.mk Q.1 f)
  refine ⟨a, b, ?_⟩
  rw [rho_apply, rho_apply]
  have h : s • aeval N (repOf N j b) = aeval N (C s * repOf N j b) := by
    rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one (A := Matrix (Fin n) (Fin n) E) s, smul_mul_assoc, one_mul]
  rw [h, ← map_add (f := _)]
  refine (aeval_eq_iff N hs _ _).2 fun Q => ?_
  rw [hab Q, map_add (f := _), map_mul, repOf_spec, repOf_spec, AdjoinRoot.mk_C]

theorem rho_adj (c : E →+* E) (hc : ∀ x, c (c x) = x) (δ : GL (Fin n) E) (hN : N = (δ * thetaGL n c δ).val)
    (σ : ∀ Q : Fac N.charpoly, AdjoinRoot Q.1 →+* AdjoinRoot Q.1)
    (hσ : ∀ Q x, σ Q (AdjoinRoot.of Q.1 x) = AdjoinRoot.of Q.1 (c x))
    (hσr : ∀ Q, σ Q (AdjoinRoot.root Q.1) * AdjoinRoot.root Q.1 = 1)
    (hσj : ∀ Q a, σ Q (j Q a) = j Q a) (a : ∀ Q, K Q) :
    rho N j hs hj a * (δ.val * GlobalTheory.Tw.Phi n E) = δ.val * GlobalTheory.Tw.Phi n E * ((rho N j hs hj a).map c)ᵀ := by
  rw [rho_apply]
  set f := repOf N j a with hfdef
  have hdet : IsUnit N.det := by
    rw [hN]; exact (Matrix.isUnit_iff_isUnit_det _).1 (δ * thetaGL n c δ).isUnit
  have hdδ : IsUnit δ.val.det := (Matrix.isUnit_iff_isUnit_det _).1 δ.isUnit
  obtain ⟨h, hh⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm N N⁻¹ hs
    (by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.nonsing_inv_mul _ hdet])
  have hroot : ∀ Q : Fac N.charpoly, AdjoinRoot.mk Q.1 h * AdjoinRoot.root Q.1 = 1 := by
    intro Q
    have h1 : aeval N (h * X) = aeval N (1 : E[X]) := by
      rw [map_mul, ← hh, aeval_X (R := E) N, map_one, Matrix.nonsing_inv_mul _ hdet]
    have h2 := (aeval_eq_iff N hs _ _).1 h1 Q
    rwa [map_mul, AdjoinRoot.mk_X, map_one] at h2
  have hpoly : aeval N⁻¹ (f.map c) = aeval N f := by
    rw [hh, ← Polynomial.aeval_comp]
    refine (aeval_eq_iff N hs _ _).2 fun Q => ?_
    have hσroot : σ Q (AdjoinRoot.root Q.1) = AdjoinRoot.mk Q.1 h :=
      mul_right_cancel₀ (right_ne_zero_of_mul_eq_one (hroot Q)) ((hσr Q).trans (hroot Q).symm)
    calc AdjoinRoot.mk Q.1 ((f.map c).comp h)
        = aeval (AdjoinRoot.root Q.1) ((f.map c).comp h) := (AdjoinRoot.aeval_eq _).symm
      _ = aeval (AdjoinRoot.mk Q.1 h) (f.map c) := by rw [Polynomial.aeval_comp, AdjoinRoot.aeval_eq]
      _ = σ Q (aeval (AdjoinRoot.root Q.1) f) := by
        rw [aeval_def, aeval_def, eval₂_map, hom_eval₂, hσroot]
        congr 1
        exact RingHom.ext fun x => (hσ Q x).symm
      _ = AdjoinRoot.mk Q.1 f := by
        rw [AdjoinRoot.aeval_eq, hfdef, repOf_spec N j a Q, hσj]
  let _ : StarRing E :=
    { star := c
      star_involutive := hc
      star_mul := fun x y => by
        show c (x * y) = c y * c x
        rw [map_mul, mul_comm]
      star_add := map_add c }
  have hsr : (starRingEnd E) = c := RingHom.ext fun _ => rfl
  have hnrm : GlobalTheory.Tw.nrm δ.val = N := by
    rw [hN, Units.val_mul]
    show δ.val * (GlobalTheory.Tw.Phi n E * ((δ.val)⁻¹)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ) =
      δ.val * (GlobalTheory.Tw.Phi n E * (c.mapMatrix (δ⁻¹).val)ᵀ * (GlobalTheory.Tw.Phi n E)ᵀ)
    rw [Matrix.coe_units_inv]
    rfl
  have hadj := GlobalTheory.BCT.KapMul.adj_aeval δ f
  rw [hnrm, hsr, hpoly] at hadj
  have hadj' : δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ * δ.val⁻¹ = aeval N f := hadj
  calc aeval N f * (δ.val * GlobalTheory.Tw.Phi n E)
      = (δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * (GlobalTheory.Tw.Phi n E)ᵀ * δ.val⁻¹) * (δ.val * GlobalTheory.Tw.Phi n E) := by
        rw [hadj']
    _ = δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ * ((GlobalTheory.Tw.Phi n E)ᵀ * (δ.val⁻¹ * δ.val) * GlobalTheory.Tw.Phi n E) := by
        simp only [Matrix.mul_assoc]
    _ = δ.val * GlobalTheory.Tw.Phi n E * (aeval N f)ᴴ := by
        rw [Matrix.nonsing_inv_mul _ hdδ, Matrix.mul_one, GlobalTheory.Tw.Model.transpose_mul_Phi, Matrix.mul_one]
    _ = δ.val * GlobalTheory.Tw.Phi n E * ((aeval N f).map c)ᵀ := rfl

end Ev

end PositivityTheory.Rg.BcB.G3.StructP

open PositivityTheory.Rg.BcB.G3.StructP in
theorem PositivityTheory.Rg.BcB.G3.struct_pf (h1 : FactorField) : Struct := by
  intro E _ _ _ s d hs0 hcs hd n δ hP
  obtain ⟨hPm, hPn, hPs, hPr⟩ := hP
  have hdata : ∀ Q : Fac (δ * thE E n δ).val.charpoly, ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : Algebra (maximalRealSubfield E) K) (j : K →+* AdjoinRoot Q.1) (σ : AdjoinRoot Q.1 →+* AdjoinRoot Q.1),
      NumberField.IsTotallyReal K ∧ Module.finrank (maximalRealSubfield E) K = Q.1.natDegree ∧
      (∀ x : (maximalRealSubfield E), j (algebraMap (maximalRealSubfield E) K x) =
        AdjoinRoot.of Q.1 (algebraMap (maximalRealSubfield E) E x)) ∧
      (∀ x : E, σ (AdjoinRoot.of Q.1 x) = AdjoinRoot.of Q.1 (IsCMField.complexConj E x)) ∧
      σ (AdjoinRoot.root Q.1) * AdjoinRoot.root Q.1 = 1 ∧ (∀ a, σ (j a) = j a) ∧
      ∀ z, ∃ a b, z = j a + AdjoinRoot.of Q.1 s * j b :=
    fun Q => h1 E s d hs0 hcs hd Q.1 (fac_monic Q) (fac_roots hPm hPr Q)
  choose K hKf hKn hKa j σ hKr hKdeg hj hσ hσr hσj hspan using hdata
  refine ⟨Fac (δ * thE E n δ).val.charpoly, inferInstance, K, hKf, hKn, hKa, rho _ j hPs hj, card_fac hPs, hKr, ?_, ?_⟩
  · simp_rw [hKdeg]
    rw [← Polynomial.natDegree_prod_of_monic _ _ (fun Q _ => fac_monic Q), prod_fac hPm hPs, hPn]
  · refine ⟨rho_injective _ j hPs hj, ?_, ?_, ?_, ?_⟩
    · show rho _ j hPs hj (algebraMap _ _ d) = _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E (Matrix (Fin n) (Fin n) E), hd,
        Algebra.algebraMap_eq_smul_one]
    · intro a
      exact rho_adj _ j hPs hj (IsCMField.complexConj E).toRingEquiv.toRingHom
        (fun x => IsCMField.complexConj_apply_apply E x) δ rfl σ hσ hσr hσj a
    · intro a
      exact rho_comm _ j hPs hj a
    · intro x hx
      exact rho_span _ j hPs hj s hspan x hx

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PSkewEx
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem skewEx_pf : SkewEx := by
  intro E _ _ _
  obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one (K := E) (AlgEquiv.ext h)
  have hconj : IsCMField.complexConj E (x - IsCMField.complexConj E x) = -(x - IsCMField.complexConj E x) := by
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hmem : (x - IsCMField.complexConj E x) ^ 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  exact ⟨x - IsCMField.complexConj E x, ⟨_, hmem⟩, sub_ne_zero.mpr (Ne.symm hx), hconj, rfl⟩

end PositivityTheory.Rg.BcB.G3

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PAbsSum
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.AbsSumP
end PositivityTheory.Rg.BcB.G3.AbsSumP

theorem PositivityTheory.Rg.BcB.G3.absSum_pf : PositivityTheory.Rg.BcB.G3.AbsSum := by
  intro V C S L A o f D loc m N hA ho hf hD hN hcard
  set T : Set V := {v | ¬ ∀ l ∈ A v, f v l = if l = o v then 1 else 0} with hTdef
  have hT : T.Finite := Filter.eventually_cofinite.mp hf
  let _ : ∀ v, Fintype (A v) := fun v => (hA v).fintype
  obtain ⟨U, hUS, hgood⟩ : ∃ U : Finset V, (∀ v ∈ U, v ∈ S) ∧
      ∀ v, v ∈ S → v ∉ U → ∀ l ∈ A v, f v l = if l = o v then 1 else 0 := by
    refine ⟨hT.toFinset.filter (fun v => v ∈ S), fun v hv => (Finset.mem_filter.mp hv).2, ?_⟩
    intro v hvS hvU
    by_contra h
    exact hvU (Finset.mem_filter.mpr ⟨hT.mem_toFinset.mpr h, hvS⟩)
  have hkey : ∀ c ∈ D, (∏ᶠ v ∈ S, f v (loc c v)) =
      if (∀ v ∈ S, v ∉ U → loc c v = o v) then ∏ v ∈ U, f v (loc c v) else 0 := by
    intro c hc
    obtain ⟨hcA, hcf⟩ := hD c hc
    have hW : {v | ¬ loc c v = o v}.Finite := Filter.eventually_cofinite.mp hcf
    obtain ⟨F, hUF, hFS, hWF⟩ : ∃ F : Finset V, U ⊆ F ∧ (↑F : Set V) ⊆ S ∧
        ∀ v ∈ S, ¬ loc c v = o v → v ∈ F := by
      refine ⟨U ∪ hW.toFinset.filter (fun v => v ∈ S), Finset.subset_union_left, ?_, ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp (Finset.mem_coe.mp hv) with hv | hv
        · exact hUS v hv
        · exact (Finset.mem_filter.mp hv).2
      · intro v hvS hne
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hW.mem_toFinset.mpr hne, hvS⟩)
    have hsupp : S ∩ Function.mulSupport (fun v => f v (loc c v)) ⊆ ↑F := by
      rintro v ⟨hvS, hv1⟩
      rw [Function.mem_mulSupport] at hv1
      rw [Finset.mem_coe]
      by_cases hvU : v ∈ U
      · exact hUF hvU
      · apply hWF v hvS
        intro heq
        apply hv1
        rw [hgood v hvS hvU _ (hcA v), if_pos heq]
    rw [finprod_mem_eq_prod_of_subset _ hsupp hFS]
    rw [← Finset.prod_sdiff hUF]
    have hrest : ∀ v ∈ F \ U, f v (loc c v) = if loc c v = o v then 1 else 0 := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      exact hgood v (hFS hv.1) hv.2 _ (hcA v)
    rw [Finset.prod_congr rfl hrest, Finset.prod_boole]
    have hiff : (∀ v ∈ F \ U, loc c v = o v) ↔ (∀ v ∈ S, v ∉ U → loc c v = o v) := by
      constructor
      · intro h v hvS hvU
        by_contra hne
        exact hne (h v (Finset.mem_sdiff.mpr ⟨hWF v hvS hne, hvU⟩))
      · intro h v hv
        rw [Finset.mem_sdiff] at hv
        exact h v (hFS hv.1) hv.2
    by_cases hc' : ∀ v ∈ S, v ∉ U → loc c v = o v
    · rw [if_pos (hiff.mpr hc'), if_pos hc', one_mul]
    · rw [if_neg (fun h => hc' (hiff.mp h)), if_neg hc', zero_mul]
  let zmap : C → ((v : U) → A v.1) := fun c v =>
    if h : loc c v.1 ∈ A v.1 then ⟨loc c v.1, h⟩ else ⟨o v.1, ho v.1⟩
  let yz : ((v : U) → A v.1) → (∀ v, L v) := fun z v => if h : v ∈ U then (z ⟨v, h⟩).1 else o v
  have hyz_ok : ∀ z, (∀ v, yz z v ∈ A v) ∧ (∀ᶠ v in cofinite, yz z v = o v) := by
    intro z
    refine ⟨fun v => ?_, ?_⟩
    · dsimp only [yz]
      split_ifs with h
      · exact (z ⟨v, h⟩).2
      · exact ho v
    · rw [Filter.eventually_cofinite]
      apply (U.finite_toSet).subset
      intro v hv
      by_contra hvU
      exact hv (by dsimp only [yz]; rw [dite_eq_right (fun h => hvU (Finset.mem_coe.mpr h))])
  have hfibfin : ∀ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v}.Finite := by
    intro z
    have h := hcard (yz z) (hyz_ok z).1 (hyz_ok z).2
    have hne : Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} ≠ 0 := by
      intro h0; rw [h0, zero_mul] at h; exact hN h.symm
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hne)
  set G : Set C := {c | c ∈ D ∧ ∀ v ∈ S, v ∉ U → loc c v = o v} with hGdef
  have hGsub : G ⊆ ⋃ z, {c | c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    rintro c ⟨hcD, hc⟩
    refine Set.mem_iUnion.mpr ⟨zmap c, hcD, fun v hvS => ?_⟩
    dsimp only [yz, zmap]
    by_cases hvU : v ∈ U
    · rw [dite_eq_left hvU, dite_eq_left ((hD c hcD).1 v)]
    · rw [dite_eq_right hvU]; exact hc v hvS hvU
  have hGfin : G.Finite := (Set.finite_iUnion hfibfin).subset hGsub
  have hsuppG : ∀ c, c ∈ D → (∏ᶠ v ∈ S, f v (loc c v)) ≠ 0 → c ∈ G := by
    intro c hcD hne
    rw [hkey c hcD] at hne
    by_contra hcG
    apply hne
    rw [if_neg]
    intro h; exact hcG ⟨hcD, h⟩
  refine ⟨hGfin.subset (fun c hc => hsuppG c hc.1 hc.2), ?_⟩
  have hsum1 : (∑ᶠ c : C, if c ∈ D then ∏ᶠ v ∈ S, f v (loc c v) else 0) =
      ∑ c ∈ hGfin.toFinset, ∏ v : U, f v.1 (zmap c v).1 := by
    rw [finsum_eq_sum_of_support_subset _ (s := hGfin.toFinset) ?_]
    · apply Finset.sum_congr rfl
      intro c hc
      rw [Set.Finite.mem_toFinset] at hc
      obtain ⟨hcD, hcG⟩ := hc
      rw [if_pos hcD, hkey c hcD, if_pos hcG, ← Finset.prod_coe_sort U (fun v => f v (loc c v))]
      apply Finset.prod_congr rfl
      intro v _
      dsimp only [zmap]
      rw [dite_eq_left ((hD c hcD).1 v.1)]
    · intro c hc
      rw [Function.mem_support] at hc
      rw [Set.Finite.coe_toFinset]
      by_cases hcD : c ∈ D
      · rw [if_pos hcD] at hc; exact hsuppG c hcD hc
      · rw [if_neg hcD] at hc; exact absurd rfl hc
  have hmem : ∀ z c, (c ∈ hGfin.toFinset ∧ zmap c = z) ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v) := by
    intro z c
    rw [Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨hcD, hcG⟩, hzc⟩
      refine ⟨hcD, fun v hvS => ?_⟩
      dsimp only [yz]
      by_cases hvU : v ∈ U
      · rw [dite_eq_left hvU, ← hzc]
        dsimp only [zmap]
        rw [dite_eq_left ((hD c hcD).1 v)]
      · rw [dite_eq_right hvU]; exact hcG v hvS hvU
    · rintro ⟨hcD, hc⟩
      refine ⟨⟨hcD, fun v hvS hvU => ?_⟩, ?_⟩
      · rw [hc v hvS]; dsimp only [yz]; rw [dite_eq_right hvU]
      · funext v
        apply Subtype.ext
        dsimp only [zmap]
        rw [dite_eq_left ((hD c hcD).1 v.1)]
        show loc c v.1 = (z v).1
        rw [hc v.1 (hUS v.1 v.2)]
        dsimp only [yz]
        rw [dite_eq_left v.2]
  have hcardfib : ∀ z (s' : Finset C), (∀ c, c ∈ s' ↔ (c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v)) →
      s'.card = Nat.card {c : C // c ∈ D ∧ ∀ v ∈ S, loc c v = yz z v} := by
    intro z s' hs'
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight hs')
  rw [hsum1, ← Finset.sum_fiberwise hGfin.toFinset zmap (fun c => ∏ v : U, f v.1 (zmap c v).1),
    Finset.sum_mul]
  rw [Finset.sum_congr rfl (g := fun z => (N : ℂ) * ∏ v : U, f v.1 (z v).1) ?_, ← Finset.mul_sum]
  swap
  · intro z _
    rw [Finset.sum_congr rfl (g := fun _ => ∏ v : U, f v.1 (z v).1) ?_, Finset.sum_const, nsmul_eq_mul,
      mul_right_comm]
    swap
    · intro c hc
      rw [(Finset.mem_filter.mp hc).2]
    congr 1
    rw [← hcard (yz z) (hyz_ok z).1 (hyz_ok z).2, Nat.cast_mul,
      hcardfib z _ (fun c => Finset.mem_filter.trans (hmem z c))]
  congr 1
  have hR : ∀ v, (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = ∑ l : A v, f v l.1 := by
    intro v
    rw [finsum_eq_sum_of_support_subset _ (s := (A v).toFinset) ?_,
      Finset.sum_set_coe (f := fun l => f v l)]
    · exact Finset.sum_congr rfl (fun l hl => if_pos (Set.mem_toFinset.mp hl))
    · intro l hl
      rw [Function.mem_support] at hl
      rw [Set.coe_toFinset]
      by_contra h
      exact hl (if_neg h)
  have hR1 : ∀ v, v ∈ S → v ∉ U → (∑ᶠ l : L v, if l ∈ A v then f v l else 0) = 1 := by
    intro v hvS hvU
    rw [hR, Finset.sum_set_coe (f := fun l => f v l),
      Finset.sum_congr rfl (fun l hl => hgood v hvS hvU l (Set.mem_toFinset.mp hl)), Finset.sum_ite_eq',
      if_pos (Set.mem_toFinset.mpr (ho v))]
  rw [← Fintype.prod_sum (fun (v : U) (l : A v.1) => f v.1 l.1)]
  rw [finprod_mem_eq_prod_of_subset _ (t := U) ?_ ?_]
  · rw [← Finset.prod_coe_sort U]
    exact Finset.prod_congr rfl (fun v _ => (hR v.1).symm)
  · rintro v ⟨hvS, hv1⟩
    by_contra hvU
    rw [Function.mem_mulSupport] at hv1
    exact hv1 (hR1 v hvS hvU)
  · intro v hv
    exact hUS v hv
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PTensorCompl
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.TensorComplP

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F))

theorem finite_over : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 F) = v}.Finite := by
  have := v.isMaximal
  have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine (h.preimage (f := HeightOneSpectrum.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

def phi : v.adicCompletion F ⊗[F] K →+*
    (∀ u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}, u.1.adicCompletion K) :=
  RingHom.pi fun u => GlobalTheory.LFun.toCompl u.2

theorem phi_apply (y : v.adicCompletion F ⊗[F] K) (u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}) :
    phi v y u = GlobalTheory.LFun.toCompl u.2 y := rfl

def extZ : v.adicCompletion F ⊗[F] K →ₗ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] K :=
  LinearMap.rTensor K (GlobalTheory.AdelicU.singleFin v)

theorem map_extZ_self (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) (extZ v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem map_extZ_ne {v' : HeightOneSpectrum (𝓞 F)} (h : v' ≠ v) (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F K) (extZ v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, TensorProduct.zero_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]

theorem phi_injective : Function.Injective (phi (K := K) v) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  have h0 : GlobalTheory.LFun.finAdEquiv F K (extZ v y) = 0 := by
    have hc : ∀ w : HeightOneSpectrum (𝓞 K), GlobalTheory.LFun.finAdEquiv F K (extZ v y) w = 0 := by
      intro w
      by_cases hw : w.under (𝓞 F) = v
      · rw [GlobalTheory.LFun.finAdEquiv_apply hw, map_extZ_self]
        exact (phi_apply v y ⟨w, hw⟩).symm.trans (congrFun hy ⟨w, hw⟩)
      · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, map_extZ_ne v hw, map_zero]
    exact Subtype.ext (funext hc)
  have h1 : extZ v y = 0 := (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv F K).injective).1 h0
  rw [← map_extZ_self v y, h1, map_zero]

theorem phi_surjective : Function.Surjective (phi (K := K) v) := by
  intro z
  obtain ⟨y, hy⟩ := (GlobalTheory.LFun.finAdEquiv F K).surjective
    ⟨fun w => if h : w.under (𝓞 F) = v then z ⟨w, h⟩ else 0, by
      filter_upwards [(finite_over (K := K) v).compl_mem_cofinite] with u hu
      rw [dite_eq_right (by simpa using hu)]
      exact zero_mem _⟩
  refine ⟨Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) y, funext fun u => ?_⟩
  rw [phi_apply, ← GlobalTheory.LFun.finAdEquiv_apply u.2, hy]
  show (if h : u.1.under (𝓞 F) = v then z ⟨u.1, h⟩ else 0) = z u
  rw [dite_eq_left u.2]

end PositivityTheory.Rg.BcB.G3.TensorComplP

open PositivityTheory.Rg.BcB.G3.TensorComplP in
theorem PositivityTheory.Rg.BcB.G3.tensorCompl_pf : TensorCompl := by
  intro F K _ _ _ _ _ v
  refine ⟨RingEquiv.ofBijective (phi v) ⟨phi_injective v, phi_surjective v⟩, fun a u => ?_⟩
  show GlobalTheory.LFun.toCompl u.2 (1 ⊗ₜ[F] a) = _
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PFactorField
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FactorFieldP

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cj (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

theorem emb_cj (φ : E →+* ℂ) : φ.comp (cj E) = (starRingEnd ℂ).comp φ := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E φ x

theorem conj_eq_inv {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

abbrev Good (Q : E[X]) : Prop := ∀ τ : E →+* ℂ, ∀ z ∈ (Q.map τ).roots, ‖z‖ = 1

variable (Q : E[X]) [Fact (Irreducible Q)]

instance finL : Module.Finite E (AdjoinRoot Q) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finite

instance nfL : NumberField (AdjoinRoot Q) := NumberField.of_module_finite E (AdjoinRoot Q)

theorem root_norm (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) : ‖ψ (AdjoinRoot.root Q)‖ = 1 := by
  apply h (ψ.comp (AdjoinRoot.of Q))
  rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Fact.out : Irreducible Q).ne_zero), Polynomial.IsRoot,
    Polynomial.eval_map, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

theorem csr (h : Good Q) :
    Polynomial.eval₂ ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ Q = 0 := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [Polynomial.hom_eval₂, map_zero, map_inv₀, ← conj_eq_inv (root_norm Q h ψ), ← RingHom.comp_assoc, emb_cj,
    ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero, map_zero]

def sig (h : Good Q) : AdjoinRoot Q →+* AdjoinRoot Q :=
  AdjoinRoot.lift ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ (csr Q h)

theorem sig_of (h : Good Q) (x : E) : sig Q h (AdjoinRoot.of Q x) = AdjoinRoot.of Q (IsCMField.complexConj E x) := by
  unfold sig
  erw [AdjoinRoot.lift_of]
  rfl

theorem sig_root (h : Good Q) : sig Q h (AdjoinRoot.root Q) = (AdjoinRoot.root Q)⁻¹ := by
  unfold sig
  exact AdjoinRoot.lift_root _

theorem emb_sig (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) (x : AdjoinRoot Q) :
    ψ (sig Q h x) = starRingEnd ℂ (ψ x) := by
  have e : ψ.comp (sig Q h) = (starRingEnd ℂ).comp ψ := by
    apply AdjoinRoot.ringHom_ext
    · ext y
      simp only [RingHom.coe_comp, Function.comp_apply, sig_of]
      exact IsCMField.complexEmbedding_complexConj E (ψ.comp (AdjoinRoot.of Q)) y
    · simp only [RingHom.coe_comp, Function.comp_apply, sig_root, map_inv₀]
      rw [conj_eq_inv (root_norm Q h ψ)]
  exact RingHom.congr_fun e x

theorem sig_sig (h : Good Q) (x : AdjoinRoot Q) : sig Q h (sig Q h x) = x := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [emb_sig, emb_sig, Complex.conj_conj]

theorem sig_alg (h : Good Q) (x : maximalRealSubfield E) :
    sig Q h (algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x) =
      algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x := by
  show sig Q h (AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)) =
    AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)
  rw [sig_of]
  congr 1
  exact (IsCMField.complexConj E).commutes x

def Kf (h : Good Q) : IntermediateField (maximalRealSubfield E) (AdjoinRoot Q) :=
  (RingHom.eqLocusField (sig Q h) (RingHom.id _)).toIntermediateField fun x => sig_alg Q h x

theorem mem_Kf (h : Good Q) {x : AdjoinRoot Q} : x ∈ Kf Q h ↔ sig Q h x = x := Iff.rfl

theorem totReal (h : Good Q) : IsTotallyReal (Kf Q h) := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  letI : Algebra (Kf Q h) ℂ := w.embedding.toAlgebra
  let ψ : AdjoinRoot Q →ₐ[Kf Q h] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  ext x
  have hx : w.embedding x = ψ.toRingHom (x : AdjoinRoot Q) := (ψ.commutes x).symm
  rw [ComplexEmbedding.conjugate_coe_eq, hx, ← emb_sig Q h ψ.toRingHom, (mem_Kf Q h).1 x.2]

theorem decomp (h : Good Q) {S : AdjoinRoot Q} (hS : S ≠ 0) (hσS : sig Q h S = -S) (z : AdjoinRoot Q) :
    ∃ a b : Kf Q h, z = (a : AdjoinRoot Q) + S * (b : AdjoinRoot Q) := by
  have h2 : (2 : AdjoinRoot Q) ≠ 0 := two_ne_zero
  refine ⟨⟨(z + sig Q h z) / 2, ?_⟩, ⟨(z - sig Q h z) / (2 * S), ?_⟩, ?_⟩
  · rw [mem_Kf, map_div₀, map_add (f := _), sig_sig, map_ofNat]
    ring
  · rw [mem_Kf, map_div₀, map_sub, map_mul, sig_sig, map_ofNat, hσS]
    field_simp
    ring
  · show z = (z + sig Q h z) / 2 + S * ((z - sig Q h z) / (2 * S))
    field_simp
    ring

theorem finrank_KL (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (Kf Q h) (AdjoinRoot Q) = 2 := by
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q h (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  have hle : Module.finrank (Kf Q h) (AdjoinRoot Q) ≤ 2 := by
    have hspan : Submodule.span (Kf Q h) (Set.range ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]) = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨a, b, hz⟩ := decomp Q h hS hσS z
      have e : z = a • (1 : AdjoinRoot Q) + b • AdjoinRoot.of Q s := by
        rw [hz, Algebra.smul_def, Algebra.smul_def, mul_one]
        exact congrArg (fun t => (a : AdjoinRoot Q) + t) (mul_comm _ _)
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩))
    have := finrank_range_le_card (R := Kf Q h) ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fin] at this
    exact this
  have hne1 : Module.finrank (Kf Q h) (AdjoinRoot Q) ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot Q) one_ne_zero).1 h1 (AdjoinRoot.of Q s)
    rw [Algebra.smul_def, mul_one] at hc
    have hm : AdjoinRoot.of Q s ∈ Kf Q h := hc ▸ c.2
    rw [mem_Kf, hσS] at hm
    have h2 : (2 : AdjoinRoot Q) * AdjoinRoot.of Q s = 0 := by linear_combination (-1 : AdjoinRoot Q) * hm
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact two_ne_zero h3
    · exact hS h3
  have hpos : 0 < Module.finrank (Kf Q h) (AdjoinRoot Q) := Module.finrank_pos
  omega

theorem finrank_Kf (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (maximalRealSubfield E) (Kf Q h) = Q.natDegree := by
  have h1 := Module.finrank_mul_finrank (maximalRealSubfield E) E (AdjoinRoot Q)
  haveI : IsScalarTower (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Free (maximalRealSubfield E) (Kf Q h) := Module.Free.of_divisionRing _ _
  have h2 := (letI : Module.Free (Kf Q h) (AdjoinRoot Q) := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q))
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h1
  rw [finrank_KL Q h hs hsc] at h2
  omega

end PositivityTheory.Rg.BcB.G3.FactorFieldP

open PositivityTheory.Rg.BcB.G3.FactorFieldP in
theorem PositivityTheory.Rg.BcB.G3.factorField_pf : FactorField := by
  intro E _ _ _ s d hs hsc hd Q _ hmon hQ
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q hQ (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  refine ⟨Kf Q hQ, inferInstance, inferInstance, inferInstance, (Kf Q hQ).val.toRingHom, sig Q hQ,
    totReal Q hQ, finrank_Kf Q hQ hs hsc, fun x => rfl, fun x => sig_of Q hQ x, ?_, fun a => a.2, ?_⟩
  · rw [sig_root, inv_mul_cancel₀]
    intro h0
    let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have := root_norm Q hQ ψ
    rw [h0, map_zero, norm_zero] at this
    exact zero_ne_one this
  · intro z
    obtain ⟨a, b, hz⟩ := decomp Q hQ hS hσS z
    exact ⟨a, b, hz⟩
end
end

namespace PositivityTheory.Rg.BcB.G3

theorem param : Param :=
  param_pf skewEx_pf (struct_pf factorField_pf) quadField_pf
    (locDict_pf clsNorm_pf clsOnto_pf clsEq_pf baseFrame_pf (inertBase_pf tensorCompl_pf) (splitSq_pf tensorCompl_pf)
      tensorCompl_pf) clsNorm_pf clsOnto_pf clsEq_pf locGood_pf

theorem count1 : Count1 := count1_pf param

theorem g3 : G8.G3 :=
  twisted_trace_formula_elliptic_expansion absSum_pf finCl2_pf invar2_pf (unit_pair_of_support locGood_pf genUnit_pf supp_pf) (count2_pf count1) supp_pf finPol2_pf

end PositivityTheory.Rg.BcB.G3
