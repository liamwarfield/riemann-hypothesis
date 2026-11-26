module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqAddNsmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyCoordinateCombinationsNoCommonZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem intElem_pow_mul_of_away {R S Rt St : Type} [CommRing R] [CommRing S] [CommRing Rt] [CommRing St]
    (f : R →+* S) (t : R) [Algebra R Rt] [Algebra S St] [IsLocalization.Away t Rt]
    [IsLocalization.Away (f t) St] (ft : Rt →+* St)
    (hc : ft.comp (algebraMap R Rt) = (algebraMap S St).comp f) (x : S)
    (hx : ft.IsIntegralElem (algebraMap S St x)) : ∃ n : ℕ, f.IsIntegralElem (f t ^ n * x) := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra Rt St := ft.toAlgebra
  letI : Algebra R St := ((algebraMap S St).comp f).toAlgebra
  haveI : IsScalarTower R Rt St := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : IsScalarTower R S St := IsScalarTower.of_algebraMap_eq' rfl
  have hx' : IsIntegral Rt (algebraMap S St x) := hx
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := hx'.exists_multiple_integral_of_isLocalization (Submonoid.powers t)
  have e : (⟨t ^ a, a, rfl⟩ : Submonoid.powers t) • algebraMap S St x =
      algebraMap S St (f t ^ a * x) := by
    rw [Submonoid.smul_def, Algebra.smul_def, IsScalarTower.algebraMap_apply R S St, ← map_mul]
    simp [RingHom.algebraMap_toAlgebra]
  rw [e] at ha
  have hr : IsIntegral R (f t) := f.isIntegralElem_map
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_isIntegral_mul_of_isIntegral_algebraMap (R := R) (Sₘ := St) hr ha
  exact ⟨n + a, by rw [pow_add, _root_.mul_assoc]; exact hn⟩

theorem isIntegralElem_of_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) {y : C} (h : (g.comp f).IsIntegralElem y) : g.IsIntegralElem y := by
  obtain ⟨p, hp, h⟩ := h
  exact ⟨p.map f, hp.map f, by rw [Polynomial.eval₂_map]; exact h⟩

theorem res_res_sections {Y : Scheme.{0}} {U V V' : Y.Opens} (h1 : V ≤ U) (h2 : V' ≤ V) (z : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom z) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom z := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem chartVal_isIntegral_of_intAt : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k)
    (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) →
    (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  intro X Y L α k s j W hW hWa hYa hint
  letI : Algebra Γ(X, W) Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom.toAlgebra
  set F := chartVal L α s j W hW with hF
  have loc : ∀ x ∈ W, ∃ d : Γ(X, W), x ∈ X.basicOpen d ∧
      ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F) := by
    intro x hx
    obtain ⟨j', W', hW', hxW', hW'a, hint'⟩ := hint x hx
    obtain ⟨d, hdle, hxd⟩ := hWa.exists_basicOpen_le (V := W ⊓ W') ⟨x, ⟨hx, hxW'⟩⟩ hx
    refine ⟨d, hxd, ?_⟩
    set r : Γ(Y, α ⁻¹ᵁ W) := (α.app W).hom d with hr
    have hED : Y.basicOpen r ≤ α ⁻¹ᵁ X.basicOpen d := (Scheme.preimage_basicOpen α d).ge
    haveI := hWa.isLocalization_basicOpen d
    haveI := hYa.isLocalization_basicOpen r
    have hDW : X.basicOpen d ≤ W := X.basicOpen_le d
    have hDW' : X.basicOpen d ≤ W' := hdle.trans inf_le_right
    have hEW : Y.basicOpen r ≤ α ⁻¹ᵁ W := Y.basicOpen_le r
    have hEW' : Y.basicOpen r ≤ α ⁻¹ᵁ W' := hED.trans (fun y hy => hDW' hy)
    have hDjj : X.basicOpen d ≤ L.U j ⊓ L.U j' := le_inf (hDW.trans hW) (hDW'.trans hW')
    let LC := LB.LinComb L (K := Fin 1) (fun _ => α) (fun _ => (k : ℤ))
    have hEJ : Y.basicOpen r ≤ LC.U (fun _ => j) ⊓ LC.U (fun _ => j') :=
      le_inf (hEW.trans (locInt_le_chart L α j W hW)) (hEW'.trans (locInt_le_chart L α j' W' hW'))
    refine intElem_pow_mul_of_away (α.app W).hom d (Rt := Γ(X, X.basicOpen d))
      (St := Γ(Y, Y.basicOpen r)) (α.appLE _ _ hED).hom ?_ F ?_
    · show (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW).op).hom =
        (Y.presheaf.map (homOfLE hEW).op).hom.comp (α.app W).hom
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
    · have hc0 := congrArg (Y.presheaf.map (homOfLE hEJ).op).hom (s.compat (fun _ => j) (fun _ => j'))
      rw [map_mul] at hc0
      show (α.appLE _ _ hED).hom.IsIntegralElem ((Y.presheaf.map (homOfLE hEW).op).hom F)
      have eF : (Y.presheaf.map (homOfLE hEW).op).hom F = (Y.presheaf.map (homOfLE hEJ).op).hom
          ((Y.presheaf.map (homOfLE (inf_le_left : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ LC.U (fun _ => j))).op).hom
            (s.f (fun _ => j))) :=
        (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
      rw [eF, hc0]
      refine RingHom.IsIntegralElem.mul _ ?_ ?_
      · have h'' : LC.U (fun _ => j) ⊓ LC.U (fun _ => j') ≤ α ⁻¹ᵁ (L.U j ⊓ L.U j') :=
          le_inf (inf_le_left.trans (LB.wchart_le L _ _ 0)) (inf_le_right.trans (LB.wchart_le L _ _ 0))
        have hg : ((LC.g (fun _ => j) (fun _ => j') : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) :
            Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) ^ k := by
          change ((∏ _i : Fin 1, (ReciprocityTheory.ChartRestriction.G.Semi.res h''
            (ReciprocityTheory.ChartRestriction.G.Semi.pullU α (L.U j ⊓ L.U j') (L.g j j'))) ^ (k : ℤ) :
              Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))ˣ) : Γ(Y, LC.U (fun _ => j) ⊓ LC.U (fun _ => j'))) = _
          rw [Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
          rfl
        have hz : (Y.presheaf.map (homOfLE hEJ).op).hom ((Y.presheaf.map (homOfLE h'').op).hom
              ((α.app (L.U j ⊓ L.U j')).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j')))) =
            (α.appLE _ _ hED).hom ((X.presheaf.map (homOfLE hDjj).op).hom (L.g j j' : Γ(X, L.U j ⊓ L.U j'))) := by
          refine (res_res_sections _ _ _).trans ?_
          have := congrArg (fun φ => (CommRingCat.Hom.hom φ) (L.g j j' : Γ(X, L.U j ⊓ L.U j')))
            (Scheme.Hom.map_appLE (f := α) hED (homOfLE hDjj).op)
          exact this.symm
        rw [hg, map_pow, hz, ← map_pow]
        exact RingHom.isIntegralElem_map _
      · have h1 := hint'.map (Y.presheaf.map (homOfLE hEW').op).hom
        have e1 : (Y.presheaf.map (homOfLE hEW').op).hom.comp (α.app W').hom =
            (α.appLE _ _ hED).hom.comp (X.presheaf.map (homOfLE hDW').op).hom := by
          rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]; rfl
        rw [e1] at h1
        have h2 := isIntegralElem_of_comp _ _ h1
        convert h2 using 1
        exact (res_res_sections _ _ _).trans (res_res_sections _ _ _).symm
  change F ∈ (integralClosure Γ(X, W) Γ(Y, α ⁻¹ᵁ W)).toSubmodule
  let S0 : Set Γ(X, W) := {d | ∃ n : ℕ, (α.app W).hom.IsIntegralElem ((α.app W).hom d ^ n * F)}
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ S0 ?_ F ?_
  · rw [← hWa.iSup_basicOpen_eq_self_iff]
    apply le_antisymm
    · exact iSup_le fun d => X.basicOpen_le _
    · intro x hx
      obtain ⟨d, hxd, hd⟩ := loc x hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨d, hd⟩, hxd⟩
  · rintro ⟨d, n, hn⟩
    refine ⟨n, ?_⟩
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_pow]
    exact hn

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartValue_isIntegral_of_integral_at_points : ∀ {X Y : Scheme.{0}} (L : LB X) (α : Y ⟶ X) (k : ℕ) (s : SecK L α k) (j : L.ι) (W : X.Opens) (hW : W ≤ L.U j), IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) → (∀ x ∈ W, IntAt L α s x) → (α.app W).hom.IsIntegralElem (chartVal L α s j W hW) := by
  first | exact @GlobalTheory.Mum.chartVal_isIntegral_of_intAt | exact GlobalTheory.Mum.chartVal_isIntegral_of_intAt | (intros; apply GlobalTheory.Mum.chartVal_isIntegral_of_intAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelHopfLePowCotangent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelHopfLePowCotangent
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobKerOrder

theorem finrank_le_pow_of_aeval_surjective {n d : ℕ} {K A : Type*} [Field K] [CommRing A]
    [Algebra K A] (x : Fin d → A) (hsurj : Function.Surjective (MvPolynomial.aeval (R := K) x))
    (hpow : ∀ i, x i ^ n = 0) :
    Module.finrank K A ≤ n ^ d := by
  classical
  let e : (Fin d → Fin n) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm fun i => a i
  let v : (Fin d → Fin n) → A := fun a => MvPolynomial.aeval (R := K) x (MvPolynomial.monomial (e a) 1)
  have hmono : ∀ m : Fin d →₀ ℕ,
      MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) ∈ Submodule.span K (Set.range v) := by
    intro m
    by_cases hm : ∀ i, m i < n
    · refine Submodule.subset_span ⟨fun i => ⟨m i, hm i⟩, ?_⟩
      have : e (fun i => ⟨m i, hm i⟩) = m := by
        ext i; simp [e]
      simp only [v, this]
    · push_neg at hm
      obtain ⟨i, hi⟩ := hm
      have h0 : MvPolynomial.aeval (R := K) x (MvPolynomial.monomial m 1) = 0 := by
        rw [MvPolynomial.aeval_monomial, map_one, one_mul, Finsupp.prod]
        by_cases hmi : m i = 0
        · have hn : n = 0 := by omega
          subst hn
          have h10 : (1 : A) = 0 := by simpa using hpow i
          rw [← mul_one (∏ j ∈ m.support, x j ^ m j), h10, mul_zero]
        · apply Finset.prod_eq_zero (i := i) (by simpa using hmi)
          obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hi
          rw [hr, pow_add, hpow i, zero_mul]
      rw [h0]; exact Submodule.zero_mem _
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨P, rfl⟩ := hsurj y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    have : MvPolynomial.monomial m (AddMonoidAlgebra.coeff P m) =
        AddMonoidAlgebra.coeff P m • MvPolynomial.monomial m (1 : K) := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (hmono m)
  have h1 := finrank_range_le_card (R := K) v
  rw [Set.finrank, htop, finrank_top] at h1
  simpa using h1

theorem finrank_le_pow_finrank_cot (p : ℕ) [hp : Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.finrank K (H ⧸ frobKerIdeal p K H) ≤ p ^ Module.finrank K (Cot K H) := by
  classical
  set J := frobKerIdeal p K H with hJ
  set ε := Bialgebra.counitAlgHom K H with hε
  set mk := Ideal.Quotient.mkₐ K J with hmk
  have hJI : ∀ a ∈ J, ε a = 0 := fun a ha => frobKerIdeal_le_augIdeal hp.out.ne_zero K H ha
  set εQ : (H ⧸ J) →ₐ[K] K := Ideal.Quotient.liftₐ J ε hJI with hεQ
  have hεQmk : ∀ a, εQ (mk a) = ε a := fun a => rfl
  have hmks : Function.Surjective mk := Ideal.Quotient.mkₐ_surjective K J
  haveI hfinQ : Module.Finite K (H ⧸ J) := Module.Finite.of_surjective mk.toLinearMap hmks
  haveI : IsNoetherianRing (H ⧸ J) := isNoetherian_of_tower K inferInstance

  have hkerQ : ∀ z ∈ RingHom.ker εQ, ∃ a ∈ RingHom.ker ε, mk a = z := by
    intro z hz
    obtain ⟨a, rfl⟩ := hmks z
    refine ⟨a, ?_, rfl⟩
    rw [RingHom.mem_ker] at hz ⊢
    rw [← hεQmk]; exact hz
  have hpowQ : ∀ z ∈ RingHom.ker εQ, z ^ p = 0 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (pow_mem_frobKerIdeal ha)
  have hnil : IsNilpotent (RingHom.ker εQ) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpowQ f hf⟩

  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  set d := Module.finrank K (AugCot ε) with hd
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  have hsum : ∀ l : Fin d → K, AugCot.d ε (∑ i, l i • (x i : H)) = ∑ i, l i • b i := by
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hx]
  have hmem : ∀ l : Fin d → K, (∑ i, l i • (x i : H)) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (x i).2
  have hspanH : ∀ a ∈ RingHom.ker ε, ∃ l : Fin d → K, a - ∑ i, l i • (x i : H) ∈ RingHom.ker ε ^ 2 := by
    intro a ha
    refine ⟨b.repr (AugCot.d ε a), ?_⟩
    have h1 : AugCot.d ε (a - ∑ i, b.repr (AugCot.d ε a) i • (x i : H)) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem ha (hmem _)), Ideal.toCotangent_eq_zero] at h1
  let y : Fin d → H ⧸ J := fun i => mk (x i)
  have hy : ∀ i, y i ∈ RingHom.ker εQ := fun i => by
    rw [RingHom.mem_ker, hεQmk]; exact (x i).2
  have hmapI : Ideal.map mk (RingHom.ker ε) ≤ RingHom.ker εQ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact ha
  have hspan : ∀ z ∈ RingHom.ker εQ, ∃ l : Fin d → K, z - ∑ i, l i • y i ∈ RingHom.ker εQ ^ 2 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := hkerQ z hz
    obtain ⟨l, hl⟩ := hspanH a ha
    refine ⟨l, ?_⟩
    have h1 : mk (a - ∑ i, l i • (x i : H)) ∈ Ideal.map mk (RingHom.ker ε ^ 2) :=
      Ideal.mem_map_of_mem _ hl
    rw [Ideal.map_pow] at h1
    have h2 := Ideal.pow_right_mono hmapI 2 h1
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [y, map_sub, map_sum, map_smul] using h2
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent εQ hnil y hy hspan
  have hyq : ∀ i, y i ^ p = 0 := fun i => hpowQ _ (hy i)

  exact finrank_le_pow_of_aeval_surjective y hsurj hyq

end GlobalTheory.PDiv.FrobKerOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelHopfLePowCotangentStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [Module.Finite K H], Module.finrank K (H ⧸ frobKerIdeal p K H) ≤ p ^ Module.finrank K (Cot K H) := by
  first | exact @GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot | exact GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot | (intros; apply GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulId
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

noncomputable section

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]


variable (R A) in
def restrZeroLeft : A ⊗[R] A →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ (counit (R := R) (A := A)).rTensor A

theorem restrZeroLeft_tmul (a b : A) : restrZeroLeft R A (a ⊗ₜ b) = counit (R := R) a • b := by
  simp [restrZeroLeft]

theorem restrZeroLeft_comul (a : A) : restrZeroLeft R A (comul a) = a := by
  simp [restrZeroLeft, Coalgebra.rTensor_counit_comul]


variable (R A) in
def restrZeroZero : A ⊗[R] (A ⊗[R] A) →ₗ[R] A :=
  (TensorProduct.lid R A).toLinearMap ∘ₗ TensorProduct.map (counit (R := R) (A := A))
    (restrZeroLeft R A)

theorem restrZeroZero_tmul (a : A) (t : A ⊗[R] A) :
    restrZeroZero R A (a ⊗ₜ t) = counit (R := R) a • restrZeroLeft R A t := by
  simp [restrZeroZero]

theorem restrZeroZero_assoc (u : A ⊗[R] A) (b : A) :
    restrZeroZero R A (TensorProduct.assoc R A A A (u ⊗ₜ b)) =
      counit (R := R) (restrZeroLeft R A u) • b := by
  induction u with
  | add x y hx hy => simp only [add_tmul, map_add (f := _), hx, hy, add_smul]
  | tmul x y =>
    rw [TensorProduct.assoc_tmul, restrZeroZero_tmul, restrZeroLeft_tmul, restrZeroLeft_tmul,
      map_smul, smul_eq_mul, mul_smul]

theorem restrZeroLeft_of_cobTwo_eq_zero {c : A ⊗[R] A} (hc : cobTwo R A c = 0) :
    restrZeroLeft R A c =
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) c)) := by
  have key : ∀ t : A ⊗[R] A, restrZeroZero R A (cobTwo R A t) = restrZeroLeft R A t -
      algebraMap R A (TensorProduct.lid R R (TensorProduct.map (counit (R := R) (A := A))
        (counit (R := R) (A := A)) t)) := fun t => by
    induction t with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel
    | tmul a b =>
      rw [cobTwo_apply]
      simp only [map_sub, map_add (f := _), LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.flip_apply,
        TensorProduct.mk_apply, restrZeroZero_assoc, restrZeroZero_tmul, restrZeroLeft_comul,
        restrZeroLeft_tmul, Bialgebra.counit_one, one_smul, TensorProduct.map_tmul,
        TensorProduct.lid_tmul, smul_eq_mul, Algebra.algebraMap_eq_smul_one, mul_smul]
      abel
  have := key c
  rw [hc, map_zero] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.PDiv

namespace GlobalTheory.PDiv

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B]

theorem dUnit_mul'_map (f g : A →ₐc[R] B) (t : A ⊗[R] A) :
    dUnit (R := R) (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) t)) =
      cotMap g (dUnit (R := R) (restrZeroLeft R A t)) +
        cotMap f (dUnit (R := R) (restrZeroLeft R A (TensorProduct.comm R A A t))) := by
  induction t with
  | add x y hx hy => simp only [map_add (f := _), hx, hy]; abel
  | tmul a b =>
    have e1 : dUnit (R := R) (counit (R := R) a • b) = counit (R := R) a • dUnit (R := R) b :=
      map_smul (AugCot.d _) _ _
    have e2 : dUnit (R := R) (counit (R := R) b • a) = counit (R := R) b • dUnit (R := R) a :=
      map_smul (AugCot.d _) _ _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply, TensorProduct.comm_tmul, restrZeroLeft_tmul,
      restrZeroLeft_tmul, e1, e2, map_smul, map_smul, cotMap_d, cotMap_d, dUnit, AugCot.d_mul]
    have c1 : counitAlgHom R B (f a) = counit (R := R) a := CoalgHomClass.counit_comp_apply f a
    have c2 : counitAlgHom R B (g b) = counit (R := R) b := CoalgHomClass.counit_comp_apply g b
    exact congrArg₂ (· + ·) (congrArg₂ (· • ·) c1 rfl) (congrArg₂ (· • ·) c2 rfl)

theorem dUnit_mul'_map_of_mem (f g : A →ₐc[R] B) {c : A ⊗[R] A} (hc : c ∈ symCocycles R A) :
    dUnit (R := R) (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) = 0 := by
  obtain ⟨h1, h2⟩ := mem_symCocycles.1 hc
  rw [dUnit_mul'_map, h2, restrZeroLeft_of_cobTwo_eq_zero h1, dUnit, AugCot.d_algebraMap,
    map_zero, map_zero, zero_add]

end GlobalTheory.PDiv

namespace GlobalTheory.PDivGroup

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {G H : PDivGroup p R}

theorem rigExtMap_add (f g : G ⟶ H) : rigExtMap (f + g) = rigExtMap f + rigExtMap g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨⟨c, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  let B : G.funs := ⟨fun n => LinearMap.mul' R _ (TensorProduct.map (f.app n : H.A n →ₗ[R] G.A n)
      (g.app n : H.A n →ₗ[R] G.A n) (c.1 n)), fun n => by
    dsimp only
    rw [← (c.2 n).2]
    generalize c.1 (n + 1) = t
    induction t with
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul x y => simp [res_app]⟩
  have hB : G.dFun B = 0 :=
    Subtype.ext (funext fun n => dUnit_mul'_map_of_mem (f.app n) (g.app n) (c.2 n).1)
  have hc : cocyclesMap (f + g) c = cocyclesMap f c + cocyclesMap g c + G.cob B :=
    Subtype.ext (funext fun n => T.bialgebraPullbackTwo_convMul_symmetricCocycle (f.app n) (g.app n) (c.1 n) (c.2 n).1)
  change G.rigMk (cocyclesMap (f + g) c, omegaMap G H (f + g) w) =
    G.rigMk (cocyclesMap f c, omegaMap G H f w) + G.rigMk (cocyclesMap g c, omegaMap G H g w)
  rw [← map_add (f := _), Prod.mk_add_mk, map_add (omegaMap G H) f g, LinearMap.add_apply, hc]
  refine (Submodule.Quotient.eq _).2 ⟨B, Prod.ext ?_ ?_⟩
  · show G.cob B = _
    simp
  · show G.dFun B = _
    rw [hB]
    simp


variable (G) in
theorem rigExtMap_natCast_smul_id (hp : (p : R) = 0) : rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  let φ : (G ⟶ G) →+ (G.RigExt →ₗ[R] G.RigExt) :=
    AddMonoidHom.mk' (fun f => rigExtMap f) (fun f g => rigExtMap_add f g)
  have h : φ (p • 𝟙 G) = p • φ (𝟙 G) := map_nsmul φ p (𝟙 G)
  rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul R, hp, zero_smul] at h
  exact h

theorem rigExtMap_add_and_natCast_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G H : PDivGroup p R),
    (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧
      rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 :=
  fun _ _ _ _ h G _ => ⟨rigExtMap_add, G.rigExtMap_natCast_smul_id h⟩

end GlobalTheory.PDivGroup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionPullbackAddAndPrimeSmulIdStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidifiedExtensionPullback_add_and_prime_smul_id : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G H : PDivGroup p R), (∀ f g : G ⟶ H, rigExtMap (f + g) = rigExtMap f + rigExtMap g) ∧ rigExtMap ((p : ℤ_[p]) • 𝟙 G) = 0 := by
  first | exact @GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | exact GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id | (intros; apply GlobalTheory.PDivGroup.rigExtMap_add_and_natCast_smul_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBalUniq

open TopologicalSpace

variable {X X' Y : Scheme.{0}} {M : LB X} {M' : LB X'} {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ}

theorem w_trans (w : LB.Iso M' (LB.LinComb M ψ δ)) (hw : w.IsGen) {Z : Scheme.{0}} (χ : Z ⟶ X') (z : Z)
    {jj jj' : K₀ → M.ι} {k k' : M'.ι} (h₁ : χ z ∈ LB.wchart M ψ jj) (h₁' : χ z ∈ LB.wchart M ψ jj')
    (h₂ : χ z ∈ M'.U k) (h₂' : χ z ∈ M'.U k') :
    gm χ z (LB.wchart M ψ jj ⊓ M'.U k) (w.s (jj, k)) =
      (∏ i, gm (χ ≫ ψ i) z (M.U (jj i) ⊓ M.U (jj' i)) (M.g (jj i) (jj' i)) ^ δ i) *
        (gm χ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * gm χ z (LB.wchart M ψ jj' ⊓ M'.U k') (w.s (jj', k')) := by
  have hm : χ z ∈ LB.wchart M ψ jj ⊓ M'.U k ⊓ (LB.wchart M ψ jj' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm χ z (LB.wchart M ψ jj ⊓ M'.U k ⊓ (LB.wchart M ψ jj' ⊓ M'.U k'))) (hw (jj, k) (jj', k'))
  have d := gm_div M' (LB.LinComb M ψ δ) χ z (jj, k) (jj', k') hm
  have l := gm_linComb M ψ δ χ z jj jj' h₁ h₁'
  exact (gm_res χ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res χ z _ hm _))))

theorem prod_split {G : Type} [CommGroup G] {K : Type} [Fintype K] (ε : K → ℤ) (f : K × K₀ → G) :
    ∏ p, f p ^ (ε p.1 * δ p.2) = ∏ a, (∏ i, f (a, i) ^ δ i) ^ ε a := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, mul_comm]

section Gen

variable {K : Type} [Fintype K] {φ' : K → (Y ⟶ X')} {ε : K → ℤ}

theorem chart_le (j : K × K₀ → M.ι) (q : K → M'.ι) (a : K) :
    LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q ≤
      φ' a ⁻¹ᵁ (LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a) := fun _ hy =>
  ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (a, k), Set.mem_iInter.1 hy.2 a⟩

def locU (w : LB.Iso M' (LB.LinComb M ψ δ)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (j : K × K₀ → M.ι)
    (q : K → M'.ι) : Γ(Y, LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q)ˣ :=
  (∏ a, res (chart_le j q a) (pullU (φ' a) _ (w.s (fun k => j (a, k), q a))) ^ ε a) * res inf_le_right (t'.s q)

theorem gm_locU (w : LB.Iso M' (LB.LinComb M ψ δ)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (j : K × K₀ → M.ι)
    (q : K → M'.ι) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) :
    gm r z (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) (locU w t' j q) =
      (∏ a, gm (r ≫ φ' a) z (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q a))
        (w.s (fun k => j (a, k), q a)) ^ ε a) * gm r z (LB.wchart M' φ' q) (t'.s q) := by
  refine (map_mul (gm r z _) _ _).trans (congrArg₂ (· * ·) ((map_prod (gm r z _) _ _).trans
    (Finset.prod_congr rfl fun a _ => ?_)) ?_)
  · refine (map_zpow (gm r z _) _ _).trans (congrArg (· ^ ε a) ?_)
    have hm : r z ∈ φ' a ⁻¹ᵁ (LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a) := chart_le (δ := δ) j q a hz
    have h1 := gm_res r z (chart_le (δ := δ) j q a) hz (pullU (φ' a) _ (w.s (fun k => j (a, k), q a)))
    have h2 := gm_pull r (φ' a) z ((LB.div (LB.LinComb M ψ δ) M').U (fun k => j (a, k), q a)) hm
      (w.s (fun k => j (a, k), q a))
    exact h1.trans h2
  · exact gm_res r z (inf_le_right : LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q ≤
      LB.wchart M' φ' q) hz (t'.s q)

theorem exists_gen_iso (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M ψ δ)) (hw : w.IsGen)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) :
    ∃ u : LB.Gen (LB.LinComb M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J →
        Good M' z J' → val u r z J = (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' := by
  have tr : ∀ (j : K × K₀ → M.ι) (q q' : K → M'.ι) (y : Y),
      y ∈ (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q) ⊓
        (LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q') →
      gm (𝟙 Y) y _ (locU w t' j q) = gm (𝟙 Y) y _ (locU w t' j q') := by
    intro j q q' y hy
    rw [gm_locU w t' j q (𝟙 Y) y hy.1, gm_locU w t' j q' (𝟙 Y) y hy.2, gen_trans ht' (𝟙 Y) y hy.1.2 hy.2.2]
    simp only [trF, Category.id_comp]
    have e : ∀ a, gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q a)) (w.s (fun k => j (a, k), q a)) =
        (gm (φ' a) y (M'.U (q a) ⊓ M'.U (q' a)) (M'.g (q a) (q' a)))⁻¹ *
          gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (q' a)) (w.s (fun k => j (a, k), q' a)) := by
      intro a
      have m := chart_le (δ := δ) j q a hy.1
      have m' := chart_le (δ := δ) j q' a hy.2
      rw [w_trans w hw (φ' a) y m.1 m.1 m.2 m'.2, Finset.prod_eq_one fun i _ => ?_, _root_.one_mul]
      exact (congrArg (· ^ δ i) (gm_self hM _ y (Set.mem_iInter.1 hy.1.1 (a, i)))).trans (one_zpow _)
    rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e a)]
    simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  have glue : ∀ j : K × K₀ → M.ι, ∃ s : Γ(Y, LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j)ˣ,
      ∀ q, res inf_le_left s = locU w t' j q := fun j =>
    glue_unit _ (fun q => LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q)
      (fun _ => inf_le_left) (fun y hy => by
        choose b hb using fun a => exists_chart hM' (φ' a y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨b, hy, Set.mem_iInter.2 hb⟩) (locU w t' j) (tr j)
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K × K₀ → M.ι) (q : K → M'.ι)
      (hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) j ⊓ LB.wchart M' φ' q),
      gm r z _ (s j) = gm r z _ (locU w t' j q) := fun Z r z j q hz =>
    (gm_res r z inf_le_left hz (s j)).symm.trans (congrArg (gm r z _) (hs j q))
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · choose b hb using fun a => exists_chart hM' (φ' a y)
    have hq : y ∈ LB.wchart M' φ' b := Set.mem_iInter.2 hb
    erw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_linComb M _ (fun p : K × K₀ => ε p.1 * δ p.2) (𝟙 Y) y j j' hy.1 hy.2]
    erw [hv Y (𝟙 Y) y j b ⟨hy.1, hq⟩, hv Y (𝟙 Y) y j' b ⟨hy.2, hq⟩, gm_locU w t' j b (𝟙 Y) y ⟨hy.1, hq⟩,
      gm_locU w t' j' b (𝟙 Y) y ⟨hy.2, hq⟩]
    simp only [Category.id_comp]
    have e : ∀ a, gm (φ' a) y (LB.wchart M ψ (fun k => j (a, k)) ⊓ M'.U (b a)) (w.s (fun k => j (a, k), b a)) =
        (∏ i, gm (φ' a ≫ ψ i) y (M.U (j (a, i)) ⊓ M.U (j' (a, i))) (M.g (j (a, i)) (j' (a, i))) ^ δ i) *
          gm (φ' a) y (LB.wchart M ψ (fun k => j' (a, k)) ⊓ M'.U (b a)) (w.s (fun k => j' (a, k), b a)) := by
      intro a
      have m := chart_le (δ := δ) j b a ⟨hy.1, hq⟩
      have m' := chart_le (δ := δ) j' b a ⟨hy.2, hq⟩
      rw [w_trans w hw (φ' a) y m.1 m'.1 m.2 m.2, gm_self hM' _ y m.2, inv_one, _root_.mul_one]
    rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e a), prod_split ε]
    simp only [mul_zpow, Finset.prod_mul_distrib]
    rw [_root_.mul_assoc]
  · have hz : r z ∈ LB.wchart M (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => J (r ≫ φ' p.1 ≫ ψ p.2)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) := ⟨hJ.mem _ r, hJ'.mem φ' r⟩
    refine (hv Z r z _ _ hz).trans ((gm_locU w t' _ _ r z hz).trans ?_)
    refine congrArg (· * _) (Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) ?_)
    unfold GlobalTheory.TensBal.isoV
    have : (fun k => J ((r ≫ φ' a) ≫ ψ k)) = fun k => J (r ≫ φ' a ≫ ψ k) := funext fun k => by rw [Category.assoc]
    rw [this]
    rfl

end Gen

theorem iso_unique : ∀ {X X' Y S₀ : Scheme.{0}} {M : LB X} {M' : LB X'}, M.IsLB → M'.IsLB → ∀ {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ} (w : LB.Iso M' (LB.LinComb M ψ δ)), w.IsGen → ∀ {K K₁ : Type} [Fintype K] [Fintype K₁] {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}, FormEq (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2) φ ε₁ → ∀ {t' : LB.Gen (LB.LinComb M' φ' ε)}, t'.IsGen → ∀ {t : LB.Gen (LB.LinComb M φ ε₁)}, t.IsGen → ∀ (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 _ → Function.Surjective p.appTop.hom → (∀ (y : S₀) (J : (S₀ ⟶ X) → M.ι) (J' : (S₀ ⟶ X') → M'.ι), Good M y J → Good M' y J' → (∏ a, GlobalTheory.TensBal.isoV w y J J' (e ≫ φ' a) ^ ε a) * val t' e y J' = val t e y J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J → Good M' z J' → (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' = val t r z J := by
  intro X X' Y S₀ M M' hM hM' K₀ _ ψ δ w hw K K₁ _ _ φ' ε φ ε₁ hF t' ht' t ht p e he hp h Z r z J J' hJ hJ'
  obtain ⟨u, hu, hv⟩ := exists_gen_iso hM hM' w hw ht'
  have key := gen_unique' hM hF p e he hp ht hu (fun y I hI => by
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    exact (h y I I' hI hI').symm.trans (hv _ e y I I' hI hI').symm) Z r z J hJ
  exact (hv Z r z J J' hJ hJ').symm.trans key.symm

end GlobalTheory.TensBalUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedGeneratorUniqueGlobalFunctionsBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_generator_unique_globalFunctions_base : ∀ {X X' Y S₀ : Scheme.{0}} {M : LB X} {M' : LB X'}, M.IsLB → M'.IsLB → ∀ {K₀ : Type} [Fintype K₀] {ψ : K₀ → (X' ⟶ X)} {δ : K₀ → ℤ} (w : LB.Iso M' (LB.LinComb M ψ δ)), w.IsGen → ∀ {K K₁ : Type} [Fintype K] [Fintype K₁] {φ' : K → (Y ⟶ X')} {ε : K → ℤ} {φ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}, FormEq (fun p : K × K₀ => φ' p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2) φ ε₁ → ∀ {t' : LB.Gen (LB.LinComb M' φ' ε)}, t'.IsGen → ∀ {t : LB.Gen (LB.LinComb M φ ε₁)}, t.IsGen → ∀ (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 _ → Function.Surjective p.appTop.hom → (∀ (y : S₀) (J : (S₀ ⟶ X) → M.ι) (J' : (S₀ ⟶ X') → M'.ι), Good M y J → Good M' y J' → (∏ a, GlobalTheory.TensBal.isoV w y J J' (e ≫ φ' a) ^ ε a) * val t' e y J' = val t e y J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (J' : (Z ⟶ X') → M'.ι), Good M z J → Good M' z J' → (∏ a, GlobalTheory.TensBal.isoV w z J J' (r ≫ φ' a) ^ ε a) * val t' r z J' = val t r z J := by
  first | exact @GlobalTheory.TensBalUniq.iso_unique | exact GlobalTheory.TensBalUniq.iso_unique | (intros; apply GlobalTheory.TensBalUniq.iso_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasValOfUnitMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm.DvrScale

open GlobalTheory.TorusExt GlobalTheory.ZH.TestVal GlobalTheory.ThetaDvr.Scale
open Classical

theorem hasVal_of_unit_mul {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (u : Vˣ) {r : V} {n : ℤ}
    (h : HasVal ϖ (algebraMap V (FractionRing V) ((u : V) * r)) n) :
    HasVal ϖ (algebraMap V (FractionRing V) r) n := by
  obtain ⟨u', hu'⟩ := h
  refine ⟨u' * u⁻¹, ?_⟩
  have e1 : algebraMap V (FractionRing V) r =
      algebraMap V (FractionRing V) ((u⁻¹ : Vˣ) : V) * algebraMap V (FractionRing V) ((u : V) * r) := by
    rw [← map_mul, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
  rw [e1, hu', Units.val_mul, map_mul]
  ring


attribute [local instance] gtGroup in
theorem exists_dvd_pow : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ b, ∀ a, ∃ (w : Fin 8 → X) (r : V), 𝔪.YY a w ∧ 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) = algebraMap V (FractionRing V) r * 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) * algebraMap V (FractionRing V) (mono W t δ w) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ _ ev X _ m t δ 𝔪
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hc : IsAdicComplete (maximalIdeal V) V := 𝔪.cn.2.2.1
  obtain ⟨hL, hL₂⟩ := abelianSchemeLaws_all
  obtain ⟨H, h₁, h₂, h₃, h₄⟩ := hyps hL hL₂
  have hm := odd_level' X₁.ρ
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, hc⟩
  have hB := 𝔪.D.tau_bimult
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using QForm.exists_QVal hϖ 𝔪.D
  obtain ⟨v, hv, -⟩ := GlobalTheory.ValClosure.exists_valuation_closure V ϖ hϖ
  have hu : IsUnit ((X₁.S.r * X₁.S.N : ℕ) : V) := by
    have := X₁.S.unit.map (ev.comp ((X₁.M.stalkEquiv z₁).symm.toRingHom.comp (algebraMap X₁.o₁ (X₁.M.O z₁))))
    rwa [map_natCast] at this
  obtain ⟨x, hx, xadd, xinj, xonto⟩ := GlobalTheory.ThetaDvr.torsion_points 𝔪.yK 𝔪.cart
  obtain ⟨rig, e, hrig, he, hsec⟩ := GlobalTheory.ThetaDvr.frames 𝔪.yK 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩ x hx
  obtain ⟨t', ht⟩ := hsec 1 X₁.ρ.th₁
  obtain ⟨w₀, hw₀⟩ := EvalZero.exists_normW 𝔪.U.toUnifPre rig hrig
  obtain ⟨th, ϑ, hE, hP, hgen⟩ := exists_prim_generator H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G
    𝔪.semi 𝔪.U w₀ hw₀.1
  have key := val_theta H h₁ h₂ h₃ h₄ V hc ϖ hϖ 𝔪.D Q hQ _ v hv 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ rig hw₀ th ϑ hE hP
    _ hm hu
  obtain ⟨f, f₁, f₂, f₃, -⟩ := GlobalTheory.TorsionIso.torsion_eq H V _ hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hm.pos
  obtain ⟨r, hr⟩ := hgen t'
  obtain ⟨sc, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (AlgebraicClosure (FractionRing V)))).inv).2 r
  set Fc := AlgebraicClosure (FractionRing V) with hF
  set y₀ : X₁.S.R →+* Fc := (algebraMap (FractionRing V) Fc).comp 𝔪.yK with hy₀
  have tv : ∀ a z J, Good 𝔪.A.L z J → cst (R := V) Fc z sc *
      @id ((TF (R := V) Fc).left.presheaf.stalk z) (sA th (ptSecT 𝔪.A.A (x a)).left z J) =
      cst (R := V) Fc z (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) * @id ((TF (R := V) Fc).left.presheaf.stalk z)
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ =>
    (ThetaCompare.sval_smul hr (x a) hJ).symm.trans (ht a _ (by
      have b := X₁.ρ.th_val a
      rw [← powFrame_one' (X₁.ρ.pt a) (X₁.ρ.fr a)] at b
      exact b) z J hJ)
  have ex : ∀ a, ∃ q, QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) := fun a => by
    obtain ⟨q, hq⟩ := f₂ (x a) (he a).1
    exact ⟨q, (f₁ _ _).2 hq.symm⟩
  have yyOf : ∀ a q (χ : 𝔪.D.toPre.X), QkToAkU 𝔪.U.toUnifPre Fc (X₁.S.r * X₁.S.N) q (x a) →
      𝔪.YY a (𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y)) := fun a q χ hq =>
    ⟨qkShift hB q χ, x a, by
      rw [AddEquiv.apply_symm_apply]
      show q.y + (X₁.S.r * X₁.S.N) • χ = _
      rw [add_comm],
      (f₁ _ _).2 (((f₁ _ _).1 hq).trans ((f₃ _ _).2 (equiv_qkShift hB q _))), hx a⟩
  have hM2 : (X₁.S.r * X₁.S.N) ^ 2 ≠ 0 := pow_ne_zero _ hm.pos.ne'
  by_cases h0 : sc = 0
  · have z0 : ∀ a, y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a => by
      obtain ⟨z⟩ := CoefBasic.exists_pt (R := V) (F := Fc)
      obtain ⟨J, hJ⟩ := CoefBasic.exists_good' (Z := (TFK (R := V) Fc).left) 𝔪.A.isLB z
      have := tv a z J hJ
      rw [h0, CoefBasic.cst_eq, CoefBasic.cst_eq, map_zero, zero_mul] at this
      exact CoefBasic.cstH_inj (R := V) z (((Units.mul_left_eq_zero _).1 this.symm).trans (map_zero _).symm)
    have z1 : ∀ a, 𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ = 0 := fun a =>
      (map_eq_zero_iff _ (algebraMap (FractionRing V) Fc).injective).1 (z0 a)
    refine ⟨0, fun a => ?_⟩
    obtain ⟨q, hq⟩ := ex a
    refine ⟨_, 0, yyOf a q 0 hq, ?_⟩
    rw [z1 a, zero_pow hM2, map_zero, zero_mul, zero_mul]

  have tv' : ∀ a z J, Good 𝔪.A.L z J → sA th (ptSecT 𝔪.A.A (x a)).left z J =
      @id ((TFK (R := V) Fc).left.presheaf.stalk z)
        (cst (R := V) Fc z (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)) *
        (val (powFrame 𝔪.A.A 𝔪.A.L (x a) (e a) ((1 : ℕ) : ℤ)) (𝟙 _) z J).val := fun a z J hJ => by
    have b := congrArg (CoefBasic.cstH (R := V) z sc⁻¹ * ·) (tv a z J hJ)
    simp only [CoefBasic.cst_eq, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, _root_.one_mul] at b
    rw [CoefBasic.cst_eq]
    exact b
  have hvs : v sc ≠ ⊤ := v.ne_top_iff.2 h0
  have split : ∀ a, v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc + v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) := fun a => by
    rw [← v.map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ h0, _root_.one_mul]
  have nz : ∀ a, v (sc⁻¹ * y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = 0 → v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩) = v sc :=
    fun a h => by rw [split a, h, add_zero]
  have h2 : 2 ≤ X₁.S.r * X₁.S.N := X₁.S.N_ge.trans (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  obtain ⟨b, hb⟩ : ∃ b, v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) = v sc := by
    obtain ⟨p₀, hp₀⟩ := exists_qkPt (F := Fc) H.1.mulN (Or.inr H.1.polBaseChange) hB
      (n := X₁.S.r * X₁.S.N) hm.pos.ne' 0
    obtain ⟨q', x', -, hx', -, hval⟩ := (key p₀ (f p₀) ((f₁ _ _).2 rfl)).2 (X₁.S.r * X₁.S.N) h2 dvd_rfl hp₀
    obtain ⟨a', rfl⟩ := xonto x' (hx' w₀ hw₀.1).1
    exact ⟨a', nz a' (hval _ _ (he a') (tv' a'))⟩
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 hvs
  refine ⟨b, fun a => ?_⟩
  obtain ⟨q, hq₁⟩ := ex a
  obtain ⟨_, ⟨χ, rfl⟩, hχ⟩ := Int.exists_least_of_bdd (P := fun k => ∃ χ, Q ((X₁.S.r * X₁.S.N) • χ + q.y) = k)
    ⟨0, by
      rintro _ ⟨χ, rfl⟩
      by_cases c : (X₁.S.r * X₁.S.N) • χ + q.y = 0
      · rw [c, QForm.Q_zero hϖ 𝔪.D hQ]
      · exact zero_le_one.trans (QForm.Q_pos hϖ 𝔪.D hQ c)⟩ ⟨_, 0, rfl⟩
  have hk := ((key q _ hq₁).1 _ _ (he a) (tv' a)).1
    ((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) fun χ' =>
      div_le_div_of_nonneg_right (Int.cast_le.2 (hχ _ ⟨χ', rfl⟩)) (Nat.cast_nonneg _)
  set w := 𝔪.e₈.symm ((X₁.S.r * X₁.S.N) • χ + q.y) with hw
  have hew : 𝔪.e₈ w = (X₁.S.r * X₁.S.N) • χ + q.y := AddEquiv.apply_symm_apply _ _
  have hmono : v (algebraMap (FractionRing V) Fc (algebraMap V (FractionRing V) (mono W t δ w))) =
      (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ) := by
    obtain ⟨u, hpc⟩ := 𝔪.psi w
    rw [hew] at hpc
    exact hv _ _ (hasVal_of_unit_mul u (GlobalTheory.ValForm.hasVal_coord (hQ _) hpc))
  have hb0 : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ≠ 0 := fun h => hvs (by
    rw [← hb]; show v (algebraMap (FractionRing V) Fc (𝔪.yK _)) = ⊤; rw [h, map_zero, AddValuation.map_zero])
  have hne : 𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (mono W t δ w) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hb0)
      ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 (𝔪.mono_ne_zero w))
  have hle : v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th b, X₁.S.th_mem b⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2) *
      algebraMap V (FractionRing V) (mono W t δ w))) ≤
      v (algebraMap (FractionRing V) Fc (𝔪.yK ⟨X₁.S.th a, X₁.S.th_mem a⟩ ^ ((X₁.S.r * X₁.S.N) ^ 2))) := by
    rw [map_mul, map_pow, map_pow, v.map_mul, v.map_pow, v.map_pow, hmono]
    change (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th b, X₁.S.th_mem b⟩) + _ ≤
      (X₁.S.r * X₁.S.N) ^ 2 • v (y₀ ⟨X₁.S.th a, X₁.S.th_mem a⟩)
    rw [hb, split a, ← hs]

    have hN : (((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM2
    have e : (((X₁.S.r * X₁.S.N) ^ 2 • (s : WithTop ℚ)) + (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℤ) : ℚ) : WithTop ℚ)) =
        (X₁.S.r * X₁.S.N) ^ 2 • ((s : WithTop ℚ) +
          (((Q ((X₁.S.r * X₁.S.N) • χ + q.y) : ℚ) / ((X₁.S.r * X₁.S.N) ^ 2 : ℕ) : ℚ) : WithTop ℚ)) := by
      rw [← WithTop.coe_add, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.coe_add, WithTop.coe_eq_coe,
        nsmul_eq_mul, nsmul_eq_mul, mul_add, mul_div_cancel₀ _ hN]
    rw [e]
    exact nsmul_le_nsmul_right (add_le_add le_rfl hk) _
  obtain ⟨r', hr', -⟩ := GlobalTheory.ThetaDvr.exists_mul_of_val_le hϖ hv hne hle
  refine ⟨w, r', yyOf a q χ hq₁, ?_⟩
  rw [hr', _root_.mul_assoc]

end GlobalTheory.Poinc.IntTerm.DvrScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionAddComponentwise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionAddComponentwise
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

theorem GlobalTheory.Mum.TensTor.qkAdd_of_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (p' q' s' : QkPt D'.toPre F k) (ps qs ss : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → PtRel T ν ν' s' ss → (∀ i, QkAdd (ps i) (qs i) (ss i)) → QkAdd p' q' s' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k p' q' s' ps qs ss hp hq hs hadd
  have gt : GlobalTheory.Ex.BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  obtain ⟨-, -, gAdd, -, gQ⟩ := gt R D.toPre D.psi_even D.tau_bimult F N ν
  obtain ⟨-, -, gAdd', -, gQ'⟩ := gt R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  obtain ⟨-, -, he, hebij, -, -, -, -⟩ := hF
  obtain ⟨P', Ps, hP', hPs, hPy, hPg⟩ := hp
  obtain ⟨Q', Qs, hQ', hQs, hQy, hQg⟩ := hq
  obtain ⟨S', Ss, hS', hSs, hSy, hSg⟩ := hs
  have hz : ∀ i, N.QEq (Ps i * Qs i) (Ss i) := by
    intro i
    obtain ⟨x, hxy, hxg, hxe⟩ := hadd i
    obtain ⟨X, hX⟩ := ((gQ k).1 x).exists
    have hXeq : X = Ps i * Qs i := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · apply Multiplicative.toAdd.injective
        apply ν.eX.injective
        rw [hX.1, hxy, ← (hPs i).1, ← (hQs i).1, ← map_add (f := _)]
        rfl
      · exact (gAdd _ _ _ _ _ _ (hPs i).2 (hQs i).2 hX.2).1 hxg
    rw [← hXeq]
    exact ((gQ k).2.2 x (ss i) X (Ss i) hX (hSs i)).1 hxe
  choose z hz1 hz2 using hz
  obtain ⟨z', hz'⟩ := hebij.2 z
  have he0 : ∀ i, chi T ν ν' 0 i = 0 := fun i => by
    have := he 0 0 i
    rw [add_zero] at this
    exact (add_eq_left.1 this.symm)
  have hensmul : ∀ (n : ℕ) χ i, chi T ν ν' (n • χ) i = n • chi T ν ν' χ i := by
    intro n χ i
    induction n with
    | zero => rw [zero_smul, zero_smul, he0]
    | succ n ih => rw [succ_nsmul, he, ih, succ_nsmul]
  obtain ⟨x', hx'⟩ := (gQ' k).2.1 (P' * Q')
  refine ⟨x', ?_, ?_, ?_⟩
  · rw [← hx'.1, ← hP'.1, ← hQ'.1, ← map_add (f := _)]
    rfl
  · exact (gAdd' _ _ _ _ _ _ hP'.2 hQ'.2 hx'.2).2 rfl
  · refine ((gQ' k).2.2 x' s' (P' * Q') S' hx' hS').2 ⟨z', ?_, ?_⟩
    · apply hebij.1
      funext i
      have e1 : (P' * Q').1.1.toAdd = P'.1.1.toAdd + Q'.1.1.toAdd := rfl
      have e2 : (Ps i * Qs i).1.1.toAdd = (Ps i).1.1.toAdd + (Qs i).1.1.toAdd := rfl
      rw [hSy i, hz1 i, he, hensmul, hz', e1, he, hPy i, hQy i, e2]
    · have m1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        P'.1.2 Q'.1.2 _ _ hPg hQg
      have m2 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν') z'
      have m3 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        _ _ _ _ m1 m2
      have e3 : ((fun j => (Ps j).1.2) * (fun j => (Qs j).1.2)) * (fun j => N.io (chi T ν ν' z' j)) =
          fun j => (Ss j).1.2 := by
        funext j
        rw [hz2 j, hz']
        rfl
      rw [e3] at m3
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') (GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν')
        _ _ _ hSg m3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionAddComponentwiseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_torsion_add_componentwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (p' q' s' : QkPt D'.toPre F k) (ps qs ss : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → PtRel T ν ν' s' ss → (∀ i, QkAdd (ps i) (qs i) (ss i)) → QkAdd p' q' s' := by
  first | exact @GlobalTheory.Mum.TensTor.qkAdd_of_components | exact GlobalTheory.Mum.TensTor.qkAdd_of_components | (intros; apply GlobalTheory.Mum.TensTor.qkAdd_of_components <;> assumption)
end
end
