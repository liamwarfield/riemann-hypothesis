module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryGroupAdelicClassesViaFiniteAdelicPart
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidue
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidue
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TameSplitChar

open GlobalTheory.CharLocProd

theorem locK_eq_of_congr {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L)
    (P : HeightOneSpectrum (𝓞 L)) (ht : χ.TameAt P) (k b : Lˣ) (hb : P.valuation L (b : L) = 1)
    (h : Valued.v (algebraMap L (P.adicCompletion L) (k : L) - algebraMap L (P.adicCompletion L) (b : L)) ≤
      WithZero.exp (-1 : ℤ)) : χ.locK P k = χ.locK P b := by
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have e : ((Formalism.L2.Host.atFin P (k * b⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) - 1 =
      (algebraMap L (P.adicCompletion L) (k : L) - algebraMap L (P.adicCompletion L) (b : L)) *
        algebraMap L (P.adicCompletion L) ((b : L)⁻¹) := by
    show algebraMap L (P.adicCompletion L) ((k * b⁻¹ : Lˣ) : L) - 1 = _
    rw [sub_mul, ← map_mul, ← map_mul, mul_inv_cancel₀ b.ne_zero, map_one, Units.val_mul, Units.val_inv_eq_inv_val]
  have h1 : Valued.v (((Formalism.L2.Host.atFin P (k * b⁻¹) : (P.adicCompletion L)ˣ) : P.adicCompletion L) - 1) ≤
      WithZero.exp (-1 : ℤ) := by
    rw [e, map_mul, val_algebraMap, map_inv₀, hb, inv_one, mul_one]
    exact h
  have h2 : χ.locK P (k * b⁻¹) = 1 := by
    refine ht _ ?_ h1
    show Valued.v _ = 1
    rw [← map_one (Valued.v : Valuation (P.adicCompletion L) _)]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [map_one]
    exact h1.trans_lt hlt
  rwa [map_mul, map_inv, mul_inv_eq_one] at h2

theorem idem_apply {L : Type} [Field L] [NumberField L] (ε : FiniteAdeleRing (𝓞 L) L) (hε : ε * ε = ε)
    (Q : HeightOneSpectrum (𝓞 L))
    (h : ∀ x : 𝓞 L, x ≠ 0 → (x ∈ Q.asIdeal ↔
      ¬ ∀ R, Valued.v (CharLocProd.evalAt R (ε * algebraMap L (FiniteAdeleRing (𝓞 L) L) ((x : L)⁻¹))) ≤ 1)) :
    CharLocProd.evalAt Q ε = 1 ∧ ∀ R, R ≠ Q → CharLocProd.evalAt R ε = 0 := by
  have h01 : ∀ R, CharLocProd.evalAt R ε ≠ 0 → CharLocProd.evalAt R ε = 1 := fun R hR =>
    mul_left_cancel₀ hR (by rw [← map_mul, hε, mul_one])
  have h0 : ∀ R, R ≠ Q → CharLocProd.evalAt R ε = 0 := by
    intro R hR
    by_contra hne
    have hnle : ¬ R.asIdeal ≤ Q.asIdeal := fun hle =>
      hR (HeightOneSpectrum.ext (R.isMaximal.eq_of_le Q.isPrime.ne_top hle))
    obtain ⟨y, hyR, hyQ⟩ := Set.not_subset.1 hnle
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hyQ Q.asIdeal.zero_mem
    have h2 := not_not.1 (mt (h y hy0).2 hyQ) R
    rw [map_mul, h01 R hne, one_mul] at h2
    exact (GlobalTheory.PlaceIdem.val_inv_le_one R hy0).1 h2 hyR
  refine ⟨h01 Q fun hQ => ?_, h0⟩
  obtain ⟨y, hyQ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
  refine (h y hy0).1 hyQ fun R => ?_
  have : CharLocProd.evalAt R ε = 0 := by
    by_cases hR : R = Q
    · rw [hR, hQ]
    · exact h0 R hR
  rw [map_mul, this, zero_mul, map_zero]
  exact zero_le

theorem val_sub_le_of_resS {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : Pl E) (φ : Formalism.L2.Herm.intAf F E →+* P.adicCompletion E) (h1 : ∀ z, Valued.v (φ z) ≤ 1)
    (h2 : ∀ t : 𝓞 E, φ (oToS F E t) = algebraMap E _ (t : E)) (a : Formalism.L2.Herm.intAf F E) (b : 𝓞 E)
    (hab : resS F P a = Ideal.Quotient.mk P.asIdeal b) :
    Valued.v (φ a - algebraMap E _ (b : E)) ≤ WithZero.exp (-1 : ℤ) := by
  have h0 : resS F P (a - oToS F E b) = 0 := by rw [map_sub, resS_oToS, hab, sub_self]
  have hm : a - oToS F E b ∈ idS F P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact (map_eq_zero_iff _ (RingEquiv.ofBijective (cmpS F P.asIdeal)
      (cmpS_bij (F := F) P.asIdeal P.ne_bot)).symm.injective).1 h0
  rw [← h2, ← map_sub]
  generalize a - oToS F E b = z at hm
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨t, ht, rfl⟩ := hy
    rw [h2, val_algebraMap]
    have := (P.intValuation_le_pow_iff_mem t 1).2 (by simpa using ht)
    rw [show P.valuation E (t : E) = P.intValuation t from HeightOneSpectrum.valuation_of_algebraMap P t]
    simpa using this
  | zero => rw [map_zero, map_zero]; exact zero_le
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Valuation.map_add_le _ hx hy
  | smul r x _ hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_mul' (h1 r) hx).trans (one_mul _).le

theorem map_mix {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (e a : A) :
    f (e * a + (1 - e)) = f e * f a + (1 - f e) := by
  rw [map_add (f := _), map_mul, map_sub, map_one]

theorem map_finset_sum {A B ι : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : Finset ι) (g : ι → A) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s


set_option maxHeartbeats 800000 in
theorem char_eq_prod_res : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D) (ρ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → IsIdemSum e P → (∀ PP ∈ P, χ.TameAt PP ∧ IsRes χ PP (ρ PP)) → ∀ (x : (AE D)ˣ) (a : AE D) (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ), (x : AE D) = e * a + (1 - e) → (a' : Lev.EAf D) = toEAf D a → (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') → ((c x : Circle) : ℂ) = ∏ PP ∈ P, ((ρ PP (u PP) : ℂˣ) : ℂ) := by
  classical
  intro D c χ P e ρ hc he ht x a a' u hx ha hu
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_mix, GlobalTheory.PlaceVec.idemSum_infPart he, zero_mul, zero_add, sub_zero]
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  obtain ⟨ev, hev⟩ : ∃ ev : ∀ R : Pl D.host.E, AE D →+* R.adicCompletion D.host.E,
      ∀ R z, ev R z = CharLocProd.evalAt R (ι (finPart D z)) :=
    ⟨fun R => (CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (finPart D)), fun _ _ => rfl⟩
  have hidem : ∀ Q ∈ P, ev Q (es Q) = 1 ∧ ∀ R, R ≠ Q → ev R (es Q) = 0 := by
    intro Q hQ
    simp only [hev]
    refine idem_apply _ (by rw [← RingEquiv.map_mul, ← RingHom.map_mul, (hes Q hQ).1.1]) Q fun y hy => ?_
    refine ((hes Q hQ).2 y hy).trans (not_congr ((h2 _).trans ?_))
    rw [RingHom.map_mul, RingEquiv.map_mul, show finPart D (incA D ((y : D.host.E)⁻¹)) =
      (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] ((y : D.host.E)⁻¹) from rfl, h1]
    rfl
  have hxP : ∀ R ∈ P, ev R x = ev R a := by
    intro R hR
    have : ev R e = 1 := by
      rw [hsum, map_finset_sum, Finset.sum_eq_single R, (hidem R hR).1]
      · intro Q hQ hne; exact (hidem Q hQ).2 R hne.symm
      · intro h; exact absurd hR h
    rw [hx, map_mix, this, one_mul, sub_self, add_zero]
  have hxP' : ∀ R, R ∉ P → ev R x = 1 := by
    intro R hR
    have : ev R e = 0 := by
      rw [hsum, map_finset_sum]
      exact Finset.sum_eq_zero fun Q hQ => (hidem Q hQ).2 R fun h => hR (h ▸ hQ)
    rw [hx, map_mix, this, zero_mul, zero_add, sub_zero]
  have hx0 : ∀ R, ev R x ≠ 0 := fun R => (RingHom.isUnit_map (ev R) x.isUnit).ne_zero
  choose k hk using fun R => GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN R _ (hx0 R)
  have hfin : {R : Pl D.host.E | R.asIdeal ∣ Ideal.span {(N : 𝓞 D.host.E)}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hN.ne')
  have key := hprod x hinf (P ∪ hfin.toFinset) (fun R => if R ∈ P then k R else 1) ?_ ?_
  rotate_left
  · intro R _
    change Valued.v (CharLocProd.evalAt R (ι (finPart D x))) = _ ∧
      Valued.v (CharLocProd.evalAt R (ι (finPart D x)) - _) ≤ _
    rw [← hev]
    by_cases hR : R ∈ P
    · simp only [if_pos hR]
      exact ⟨(hk R).1, (hk R).2.1⟩
    · simp only [if_neg hR]
      rw [hxP' R hR, Units.val_one, map_one, map_one, map_one, sub_self, map_zero]
      exact ⟨rfl, zero_le⟩
  · intro R hR
    rw [Finset.mem_union, not_or] at hR
    change Valued.v (CharLocProd.evalAt R (ι (finPart D x))) = _ ∧ _
    rw [← hev, hxP' R hR.1, map_one]
    exact ⟨rfl, fun h => hR.2 (hfin.mem_toFinset.2 (Ideal.dvd_span_singleton.2 h))⟩
  rw [key, ← Finset.prod_subset Finset.subset_union_left
    (fun R _ hR => by rw [if_neg hR, map_one, Units.val_one])]
  refine Finset.prod_congr rfl fun R hR => ?_
  rw [if_pos hR]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (u R : kP R)
  have := R.isPrime
  have hbR : b ∉ R.asIdeal := fun h => (u R).ne_zero (hb ▸ Ideal.Quotient.eq_zero_iff_mem.2 h)
  have hb0 : (b : D.host.E) ≠ 0 := fun h => hbR (RingOfIntegers.coe_eq_zero_iff.1 h ▸ R.asIdeal.zero_mem)
  have hbv : R.valuation D.host.E (b : D.host.E) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := D.host.E) R (r := b)).2 hbR
  let cm := (Algebra.TensorProduct.comm D.host.F (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)
  let φ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* R.adicCompletion D.host.E :=
    (CharLocProd.evalAt R).comp ((ι : _ →+* _).comp (cm.symm.toRingEquiv.toRingHom.comp
      (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype))
  have hφ : ∀ z, φ z = CharLocProd.evalAt R (ι (cm.symm (z : Lev.EAf D))) := fun _ => rfl
  have hv := val_sub_le_of_resS R φ (fun z => (h2 _).1 ((GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D _).2
      (by change cm (cm.symm (z : Lev.EAf D)) ∈ _; rw [AlgEquiv.apply_symm_apply]; exact z.2)) R)
    (fun t => by
      rw [hφ, show cm.symm ((oToS D.host.F D.host.E t : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) =
        (1 : GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (t : D.host.E) from rfl, h1]
      rfl) a' b ((hu R hR).symm.trans hb.symm)
  have hφa : φ a' = ev R x := by
    rw [hxP R hR, hev, hφ, ha]
    exact congrArg (fun z => CharLocProd.evalAt R (ι z)) (cm.symm_apply_apply (finPart D a))
  rw [hφa] at hv
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hxv : Valued.v (ev R x) = 1 := by
    rw [← hbv, ← val_algebraMap]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [val_algebraMap, hbv]
    exact hv.trans_lt hlt
  have hk3 := (hk R).2.2
  rw [← (hk R).1, hxv, mul_one] at hk3
  rw [(ht R hR).2 b (Units.mk0 _ hb0) (u R) rfl hb.symm,
    locK_eq_of_congr χ R (ht R hR).1 (k R) (Units.mk0 _ hb0) hbv ?_]
  have e4 : algebraMap D.host.E (R.adicCompletion D.host.E) (k R : D.host.E) -
      algebraMap D.host.E (R.adicCompletion D.host.E) (b : D.host.E) =
      (ev R x - algebraMap D.host.E _ (b : D.host.E)) - (ev R x - algebraMap D.host.E _ (k R : D.host.E)) := by
    ring
  rw [Units.val_mk0, e4]
  exact Valuation.map_sub_le _ hv hk3

end GlobalTheory.TameSplitChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameHeckeCharSplitSupportedEqProdResidueStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.VecInv
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameHeckeChar_splitSupported_eq_prod_residue : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (P : Finset (Pl D.host.E)) (e : AE D) (ρ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), ChrEq c χ → IsIdemSum e P → (∀ PP ∈ P, χ.TameAt PP ∧ IsRes χ PP (ρ PP)) → ∀ (x : (AE D)ˣ) (a : AE D) (a' : Formalism.L2.Herm.intAf D.host.F D.host.E) (u : ∀ PP : Pl D.host.E, (kP PP)ˣ), (x : AE D) = e * a + (1 - e) → (a' : Lev.EAf D) = toEAf D a → (∀ PP ∈ P, (u PP : kP PP) = resS D.host.F PP a') → ((c x : Circle) : ℂ) = ∏ PP ∈ P, ((ρ PP (u PP) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.TameSplitChar.char_eq_prod_res | exact GlobalTheory.TameSplitChar.char_eq_prod_res | (intros; apply GlobalTheory.TameSplitChar.char_eq_prod_res <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.TensorGlob

theorem der_span {E : Type*} [AddCommGroup E] [Module ℂ E] {s : Set E} (hs : Submodule.span ℂ s = ⊤)
    (f : ℝ → E →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] ℂ) (h : ∀ e ∈ s, HasDerivAt (fun t => f t e) (g e) 0) (e : E) :
    HasDerivAt (fun t => f t e) (g e) 0 := by
  have he : e ∈ Submodule.span ℂ s := hs ▸ Submodule.mem_top
  induction he using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero =>
    have h0 : (fun t => f t 0) = fun _ => (0 : ℂ) := funext fun t => map_zero (f t)
    rw [h0, map_zero]
    exact hasDerivAt_const _ _
  | add x y _ _ hx hy =>
    have h0 : (fun t => f t (x + y)) = fun t => f t x + f t y := funext fun t => map_add (f t) x y
    rw [h0, map_add (f := _)]
    exact hx.add hy
  | smul a x _ hx =>
    have h0 : (fun t => f t (a • x)) = fun t => a * f t x := funext fun t => map_smul (f t) a x
    rw [h0, map_smul, smul_eq_mul]
    exact hx.const_mul a

theorem der_span₂ {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    {s : Set E} (hs : Submodule.span ℂ s = ⊤) {s' : Set F} (hs' : Submodule.span ℂ s' = ⊤)
    (f : ℝ → E →ₗ[ℂ] F →ₗ[ℂ] ℂ) (g : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)
    (h : ∀ e ∈ s, ∀ x ∈ s', HasDerivAt (fun t => f t e x) (g e x) 0) (e : E) (x : F) :
    HasDerivAt (fun t => f t e x) (g e x) 0 := by
  have h1 : ∀ x ∈ s', ∀ e', HasDerivAt (fun t => f t e' x) (g e' x) 0 := fun x hx e' =>
    der_span hs (fun t => (f t).flip x) (g.flip x) (fun e'' he'' => h e'' he'' x hx) e'
  exact der_span hs' (fun t => f t e) (g e) (fun x hx => h1 x hx e) x

variable {D : D7}

open Classical in
theorem glue_update {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) :
    glue (Function.update P τ p) = MvPolynomial.rename (fun s => (τ, s)) p *
      ∏ ρ ∈ Finset.univ.erase τ, MvPolynomial.rename (fun s => (ρ, s)) (P ρ) := by
  unfold glue
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem glue_update_add_smul {a b : ℕ} (P : D.what₂.Tau → LPol b a) (τ : D.what₂.Tau) (p : LPol b a) (c : ℂ) :
    glue (Function.update P τ p) + c • glue P = glue (Function.update P τ (p + c • P τ)) := by
  have h0 : glue P = glue (Function.update P τ (P τ)) := by rw [Function.update_eq_self]
  rw [h0, glue_update, glue_update, glue_update, map_add (f := _), map_smul, add_mul, smul_mul_assoc]

variable {V : HSp D} {S : D.what₂.Tau → SPar}

theorem ellT_tprod' (M : DSModel V S) (w v : ∀ τ, M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ v) = ∏ τ, ⟪w τ, v τ⟫_ℂ := by
  unfold ellT
  rw [PiTensorProduct.lift.tprod]
  simp

open Classical in
theorem ellT_update (M : DSModel V S) (w v : ∀ τ, M.H τ) (τ : D.what₂.Tau) (u : M.H τ) :
    ellT M w (PiTensorProduct.tprod ℂ (Function.update v τ u)) =
      ⟪w τ, u⟫_ℂ * ∏ ρ ∈ Finset.univ.erase τ, ⟪w ρ, v ρ⟫_ℂ := by
  rw [ellT_tprod', ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  congr 1
  · simp
  · exact Finset.prod_congr rfl fun ρ hρ => by simp [Finset.ne_of_mem_erase hρ]

open Classical in
theorem actT_tprod (M : DSModel V S) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (v : ∀ τ, M.H τ) :
    actT M τ g (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ (Function.update v τ (M.rep τ g (v τ))) := by
  unfold actT
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext ρ
  by_cases hρ : ρ = τ
  · subst hρ; simp
  · simp [Function.update_of_ne hρ]

theorem der_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {c : ℝ → H} {y : H}
    (h : HasDerivAt c y 0) (w : H) (k : ℂ) : HasDerivAt (fun t => ⟪w, c t⟫_ℂ * k) (⟪w, y⟫_ℂ * k) 0 := by
  have h1 : HasDerivAt (fun t => ⟪w, c t⟫_ℂ) ⟪w, y⟫_ℂ 0 := by
    simpa [Function.comp_def] using ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  exact h1.mul_const k


open Classical in
theorem exists_globIt : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (A : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.ContrTensor → GlueLaw D V.rank W.rank → (∀ τ, LocIt M M' τ (aS τ) (aT τ) (A τ)) → ∃ It I, GlobIt M M' aS aT It I := by
  intro D V W S S' M M' aS aT A hC hG hL
  have hs := hG.1
  have hs' : Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ : (∀ τ, M'.H τ) → ⨂[ℂ] τ, M'.H τ)) = ⊤ :=
    PiTensorProduct.span_tprod_eq_top
  obtain ⟨I, hI, -⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => M'.H τ) (fun τ => M.H τ) A
  have hIg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.H τ),
      I (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (v ρ) :=
    fun P v => hI P v
  let Itl : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ := fun τ =>
    LinearMap.mk₂ ℂ (fun P y => (⟨A τ P (y : M'.H τ), (hL τ).sm P (y : M'.H τ)⟩ : M.sm τ))
      (fun P Q y => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
      (fun P y z => Subtype.ext (by simp)) (fun c P y => Subtype.ext (by simp))
  have hItl : ∀ τ P y, ((Itl τ P y : M.sm τ) : M.H τ) = A τ P (y : M'.H τ) := fun _ _ _ => rfl
  obtain ⟨It, hIt, hItne⟩ := hC D.what₂.Tau (fun _ => Fin W.rank × Fin V.rank) (FVar D W.rank V.rank)
    (Equiv.sigmaEquivProd D.what₂.Tau (Fin W.rank × Fin V.rank) :
      (Σ _ : D.what₂.Tau, Fin W.rank × Fin V.rank) ≃ FVar D W.rank V.rank)
    (fun τ => ↥(M'.sm τ)) (fun τ => ↥(M.sm τ)) Itl
  have hItg : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (v : ∀ τ, M'.sm τ),
      It (glue P) (PiTensorProduct.tprod ℂ v) = PiTensorProduct.tprod ℂ fun ρ => Itl ρ (P ρ) (v ρ) :=
    fun P v => hIt P v
  have hupdP : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (Q : LPol W.rank V.rank)
      (v : ∀ τ, M'.H τ), (PiTensorProduct.tprod ℂ fun ρ => A ρ (Function.update P τ Q ρ) (v ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ Q (v τ))) := by
    intro P τ Q v
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  have hupdV : ∀ (P : D.what₂.Tau → LPol W.rank V.rank) (τ : D.what₂.Tau) (v : ∀ τ, M'.H τ) (y : M'.H τ),
      (PiTensorProduct.tprod ℂ fun ρ => A ρ (P ρ) (Function.update v τ y ρ)) =
        PiTensorProduct.tprod ℂ (Function.update (fun ρ => A ρ (P ρ) (v ρ)) τ (A τ (P τ) y)) := by
    intro P τ v y
    congr 1
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  refine ⟨It, I, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro φ v
    have h1 : It.compr₂ (inclT M) = I.compl₂ (inclT M') := by
      refine LinearMap.ext_on hs ?_
      rintro _ ⟨P, rfl⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply, hItg]
      unfold inclT
      simp only [PiTensorProduct.map_tprod, Submodule.subtype_apply, hItl, hIg]
    exact DFunLike.congr_fun (DFunLike.congr_fun h1 φ) v
  · apply hItne
    intro τ h0
    obtain ⟨P, y, hy, hne⟩ := (hL τ).ne
    apply hne
    have h2 := congrArg (fun B : LPol W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.sm τ =>
      ((B P ⟨y, hy⟩ : M.sm τ) : M.H τ)) h0
    simpa [hItl] using h2
  · intro φ w
    have hφ : φ ∈ Submodule.span ℂ (Set.range (glue : (D.what₂.Tau → LPol W.rank V.rank) → PolF D W.rank V.rank)) :=
      hs ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨P, rfl⟩ := hx
      choose w' hw' using fun τ => (hL τ).adj (P τ) (w τ)
      refine Submodule.subset_span ⟨w', ?_⟩
      refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, hIg, ellT_tprod', hw']
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), LinearMap.comp_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul, LinearMap.comp_smul]
      exact Submodule.smul_mem _ a hx
  · intro τ X hX φ x w
    have key := der_span₂ hs hs' (fun t => I.compr₂ (ellT M w ∘ₗ actT M τ (NormedSpace.exp (t • X))))
      ((I ∘ₗ srcOp M M' τ (aT τ) X).compr₂ (ellT M w)) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.comp_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, srcOp, LinearMap.add_apply,
        LinearMap.smul_apply, Module.End.one_apply, (hG.2 τ (M.ε τ) (M'.ε τ) P).1, glue_update_add_smul,
        hIg, hupdP, actT_tprod, ellT_update]
      rw [neg_smul, ← sub_eq_add_neg]
      exact der_inner ((hL τ).src X hX (P τ) (v τ)) (w τ) _
  · intro τ Y hY φ x w
    have key := der_span₂ hs hs'
      (fun t => (I.compl₂ (actT M' τ (NormedSpace.exp (t • Y)))).compr₂ (ellT M w))
      (-((I ∘ₗ tgtOp M M' τ (aS τ) Y).compr₂ (ellT M w))) ?hyp φ x
    · simpa only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        LinearMap.neg_apply] using key
    case hyp =>
      rintro _ ⟨P, rfl⟩ _ ⟨v, rfl⟩
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply, LinearMap.neg_apply,
        tgtOp, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        (hG.2 τ (M.ε τ) (M'.ε τ) P).2, glue_update_add_smul, hIg, hupdP, hupdV, actT_tprod, ellT_update]
      rw [← neg_mul, ← inner_neg_right]
      exact der_inner ((hL τ).tgt Y hY (P τ) (v τ)) (w τ) _

end GlobalTheory.Chain.RealIt.TensorGlob

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGlobalFockIntertwinerTensorRealPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (A : ∀ τ, LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), GlobalTheory.IndefiniteRowSideFullHecke.ContractionTensorModels.ContrTensor → GlueLaw D V.rank W.rank → (∀ τ, LocIt M M' τ (aS τ) (aT τ) (A τ)) → ∃ It I, GlobIt M M' aS aT It I := by
  first | exact @GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt | exact GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt | (intros; apply GlobalTheory.Chain.RealIt.TensorGlob.exists_globIt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergMatrixCoeffRealLineSkew
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergMatrixCoeffRealLineSkew
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatrixCoeffDeriv

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

private theorem measure_fundamentalDomain_ratL_lt_top {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ) : μ 𝓕 < ⊤ := by
  have := hμ
  obtain ⟨-, -, hsc, -, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have := hsc
  have := hdisc
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : MeasurableConstVAdd (ratL W V) (WO V W) :=
    ⟨fun γ => (continuous_const_add (γ : WO V W)).measurable⟩
  have : VAddInvariantMeasure (ratL W V) (WO V W) μ :=
    ⟨fun γ _ hs => Measure.measure_preimage_of_map_eq_self
      (Measure.IsAddLeftInvariant.map_add_left_eq_self (γ : WO V W))
      (continuous_const_add (γ : WO V W)).measurable.aemeasurable hs.nullMeasurableSet⟩
  have : Countable (ratL W V) :=
    (TopologicalSpace.separableSpace_iff_countable (α := ratL W V)).1 inferInstance
  have hsub : 𝓕 ⊆ ⋃ γ : ratL W V, ((γ +ᵥ ·) '' K ∩ 𝓕) := by
    intro x hx
    obtain ⟨γ, hγ, hγK⟩ := hcov x
    refine Set.mem_iUnion.2 ⟨⟨-γ, neg_mem hγ⟩, ⟨γ + x, hγK, ?_⟩, hx⟩
    show -γ + (γ + x) = x
    abel
  calc μ 𝓕 ≤ μ (⋃ γ : ratL W V, ((γ +ᵥ ·) '' K ∩ 𝓕)) := measure_mono hsub
    _ ≤ ∑' γ : ratL W V, μ ((γ +ᵥ ·) '' K ∩ 𝓕) := measure_iUnion_le _
    _ = μ K := (h𝓕.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top

theorem hasDerivAt_integral_line (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {L : ℝ →+ WO V W}
    (hL : IsRealDir W V L) {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 μ)
    {f g : WO V W → ℂ} (h : IsThetaFunO ψ V W f) (h' : IsThetaFunO ψ V W g) :
    HasDerivAt (fun t : ℝ => ∫ x in 𝓕, heisO ψ V W (L t) f x * (starRingEnd ℂ) (g x) ∂μ)
      (∫ x in 𝓕, dLine ψ V W L f x * (starRingEnd ℂ) (g x) ∂μ) 0 := by
  have := hμ
  have : BorelSpace (WO V W) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (measure_fundamentalDomain_ratL_lt_top hμ h𝓕).ne
  have hd : IsThetaFunO ψ V W (dLine ψ V W L f) := theta_dLine hθ hψ hL h
  obtain ⟨C, hC⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := V) (W := W) hψ _ hd).2.1
  obtain ⟨C₀, hC₀⟩ := (GlobalTheory.ThetaSquare.squareIntegrable (V := V) (W := W) hψ _ h).2.1
  have hgi : Integrable g (μ.restrict 𝓕) :=
    ((GlobalTheory.ThetaSquare.squareIntegrable (V := V) (W := W) hψ _ h').2.2 μ 𝓕 hμ h𝓕).integrable one_le_two
  have hcg : Continuous fun x => (starRingEnd ℂ) (g x) := Complex.continuous_conj.comp h'.cont
  have hc : ∀ k : WO V W → ℂ, IsThetaFunO ψ V W k → ∀ t : ℝ,
      Continuous fun x => heisO ψ V W (L t) k x * (starRingEnd ℂ) (g x) :=
    fun k hk t => (theta_heisO_real hθ hψ (hL.2 t) hk).cont.mul hcg
  have hb : ∀ (k : WO V W → ℂ) (B : ℝ), (∀ y, ‖k y‖ ≤ B) → ∀ (t : ℝ) (x : WO V W),
      ‖heisO ψ V W (L t) k x * (starRingEnd ℂ) (g x)‖ ≤ B * ‖g x‖ := by
    intro k B hk t x
    rw [norm_mul, GlobalTheory.ThetaSquare.norm_heisO hψ, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hk _) (norm_nonneg _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
    (F := fun t x => heisO ψ V W (L t) f x * (starRingEnd ℂ) (g x))
    (F' := fun t x => heisO ψ V W (L t) (dLine ψ V W L f) x * (starRingEnd ℂ) (g x))
    (bound := fun x => C * ‖g x‖) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t => (hc f h t).aestronglyMeasurable)
    ((hgi.norm.const_mul C₀).mono' (hc f h 0).aestronglyMeasurable (ae_of_all _ (hb f C₀ hC₀ 0)))
    (hc _ hd 0).aestronglyMeasurable
    (ae_of_all _ fun x t _ => hb _ C hC t x) (hgi.norm.const_mul C)
    (ae_of_all _ fun x t _ => (hasDerivAt_heisO hθ hψ hL h x t).mul_const _)
  have h0 : ∀ (k : WO V W → ℂ) (x : WO V W), heisO ψ V W (L 0) k x = k x := by
    intro k x
    simp only [map_zero, heisO, GlobalTheory.ThetaSquare.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]
  simpa only [h0] using key.2

theorem hasDerivAt_ipO_and_skew : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) g) (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g) 0 ∧ ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g = -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  intro D ψ θ S T μ 𝓕 hψ hθ hcov f g hf hg τ z
  obtain ⟨hμ, h𝓕, -⟩ := hcov
  refine ⟨?_, ((GlobalTheory.ThetaSquare.derSkew hψ hθ) τ z).2.2 μ 𝓕 hμ h𝓕 f g hf hg⟩
  rw [dRho_eq_dLine]
  exact hasDerivAt_integral_line hψ hθ (isRealDir_lineAt hθ τ z) hμ h𝓕 hf hg

end GlobalTheory.MatrixCoeffDeriv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergMatrixCoeffRealLineSkewStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsInfFam θ → IsCovolOne (ratL T S) μ 𝓕 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) g) (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g) 0 ∧ ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) g = -ipO μ 𝓕 f (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g) := by
  first | exact @GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew | exact GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew | (intros; apply GlobalTheory.MatrixCoeffDeriv.hasDerivAt_ipO_and_skew <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
open scoped TensorProduct

namespace GlobalTheory.SegmentClass

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def rangeEquiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) : ρ.Equiv f.range.toRepresentation :=
  .mk (LinearEquiv.ofInjective f.toLinearMap hf) fun g =>
    LinearMap.ext fun v => Subtype.ext (by change f (ρ g v) = σ g (f v); rw [f.isIntertwining])

def subIncl {ρ : Representation ℂ G V} (S : Subrepresentation ρ) : S.toRepresentation.IntertwiningMap ρ :=
  ⟨S.toSubmodule.subtype, fun _ => rfl⟩

theorem subIncl_injective {ρ : Representation ℂ G V} (S : Subrepresentation ρ) :
    Function.Injective (subIncl S) := Subtype.val_injective

theorem nonempty_equiv_of_eq {ρ : Representation ℂ G V} {S T : Subrepresentation ρ} (h : S = T) :
    Nonempty (S.toRepresentation.Equiv T.toRepresentation) := by
  subst h; exact ⟨.refl _⟩

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def cuspRep (Δ : Segment k) : IrrRep (GL (Fin Δ.d) k) := Δ.cusp.choose

theorem cuspRep_cl (Δ : Segment k) : (cuspRep Δ).cl = Δ.start := Δ.cusp.choose_spec.1

theorem cuspRep_isCuspidal (Δ : Segment k) : IsCuspidal (cuspRep Δ).ρ := Δ.cusp.choose_spec.2

theorem nonempty_prod_equiv (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) :
    Nonempty ((multiProd e (segTerm σ.ρ Δ.len)).Equiv
      (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len))) := by
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 (hσ.trans (cuspRep_cl Δ).symm)
  obtain ⟨ψ⟩ := (Placing.parInd_jac_placing k (Fin Δ.len) (Fin (Δ.len * Δ.d)) (fun _ => Fin Δ.d) e
    (GlobalTheory.Published.consecBlocks Δ.len Δ.d) _).1 (piTensor (segTerm (cuspRep Δ).ρ Δ.len))
  exact ⟨(GlobalTheory.LocGL.multiProdEquiv e (π := segTerm σ.ρ Δ.len) (σ := segTerm (cuspRep Δ).ρ Δ.len)
    fun a => GlobalTheory.LocGL.twistEquiv φ _).trans ψ⟩

theorem nonempty_piTensor_equiv (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start) :
    Nonempty ((piTensor (segTerm (cuspRep Δ).ρ Δ.len)).Equiv (piTensor (segTerm σ.ρ Δ.len))) := by
  obtain ⟨φ⟩ := IrrRep.cl_eq_iff.1 ((cuspRep_cl Δ).trans hσ.symm)
  exact ⟨GlobalTheory.LocGL.piTensorEquiv (ρ := segTerm (cuspRep Δ).ρ Δ.len) (σ := segTerm σ.ρ Δ.len)
    fun a => GlobalTheory.LocGL.twistEquiv φ _⟩

section Published

variable (h : GlobalTheory.Published.SegmentRepresentation)
include h

def segSub (Δ : Segment k) :
    Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len)) :=
  (h k Δ.d Δ.len Δ.d_pos Δ.len_pos (cuspRep Δ) (cuspRep_isCuspidal Δ)).choose

theorem segSub_spec (Δ : Segment k) :
    (segSub h Δ).toRepresentation.IsIrreducible ∧
      (∀ S' : Subrepresentation (multiProd (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segTerm (cuspRep Δ).ρ Δ.len)),
        S'.toRepresentation.IsIrreducible → S' = segSub h Δ) ∧
      Nonempty ((GlobalTheory.SmGL.jac (GlobalTheory.Published.consecBlocks Δ.len Δ.d) (segSub h Δ).toRepresentation).Equiv
        (piTensor (segTerm (cuspRep Δ).ρ Δ.len))) :=
  (h k Δ.d Δ.len Δ.d_pos Δ.len_pos (cuspRep Δ) (cuspRep_isCuspidal Δ)).choose_spec

def segIrr (Δ : Segment k) : IrrRep (GL (Fin (Δ.len * Δ.d)) k) where
  V := (segSub h Δ).toSubmodule
  ρ := (segSub h Δ).toRepresentation
  smooth := IsSubquotient.isSmooth ⟨segSub h Δ, .id _, Function.surjective_id⟩ (isSmooth_parInd _ _)
  irr := (segSub_spec h Δ).1

theorem embeds_iff (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)) :
    (∃ φ : π.ρ.IntertwiningMap (multiProd e (segTerm σ.ρ Δ.len)), Function.Injective φ) ↔
      Nonempty (π.ρ.Equiv (segIrr h Δ).ρ) := by
  obtain ⟨Φ⟩ := nonempty_prod_equiv Δ σ hσ e
  constructor
  · rintro ⟨φ, hφ⟩
    let f := Φ.toIntertwiningMap.comp φ
    have hf : Function.Injective f := Φ.toLinearEquiv.injective.comp hφ
    have hR : f.range.toRepresentation.IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (rangeEquiv f hf) π.irr
    obtain ⟨ψ⟩ := nonempty_equiv_of_eq ((segSub_spec h Δ).2.1 _ hR)
    exact ⟨(rangeEquiv f hf).trans ψ⟩
  · rintro ⟨ψ⟩
    exact ⟨Φ.symm.toIntertwiningMap.comp ((subIncl (segSub h Δ)).comp ψ.toIntertwiningMap),
      Φ.symm.toLinearEquiv.injective.comp ((subIncl_injective _).comp ψ.toLinearEquiv.injective)⟩

theorem jac_iff (Δ : Segment k) (σ : IrrRep (GL (Fin Δ.d) k)) (hσ : σ.cl = Δ.start)
    (e : (Σ _ : Fin Δ.len, Fin Δ.d) ≃ Fin (Δ.len * Δ.d)) (π : IrrRep (GL (Fin (Δ.len * Δ.d)) k)) :
    Nonempty ((GlobalTheory.SmGL.jac e π.ρ).Equiv (piTensor (segTerm σ.ρ Δ.len))) ↔ Nonempty (π.ρ.Equiv (segIrr h Δ).ρ) := by
  constructor
  · rintro ⟨ψ⟩
    obtain ⟨f, hf⟩ := (Model.evalOne_bijective e π.smooth (piTensor (segTerm σ.ρ Δ.len))).2
      ψ.toIntertwiningMap
    refine (embeds_iff h Δ σ hσ e π).1 ⟨f, ?_⟩
    haveI := π.irr
    refine (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right fun h0 => ?_
    haveI : Nontrivial (⨂[ℂ] _ : Fin Δ.len, σ.V) :=
      GlobalTheory.ProdSupport.nontrivial_piTensor _ fun _ => Model.nontrivial_of_isIrreducible σ.irr
    obtain ⟨y, hy⟩ := exists_ne (0 : ⨂[ℂ] _ : Fin Δ.len, σ.V)
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (ψ.symm y)
    have h1 : ψ (Submodule.Quotient.mk v) = (f v).1.1 1 :=
      (congrArg (fun F => F (Submodule.Quotient.mk v)) hf).symm
    rw [h0, hv] at h1
    exact hy ((ψ.apply_symm_apply y).symm.trans h1)
  · rintro ⟨ψ⟩
    obtain ⟨A⟩ := (Placing.parInd_jac_placing k (Fin Δ.len) (Fin (Δ.len * Δ.d)) (fun _ => Fin Δ.d) e
      (GlobalTheory.Published.consecBlocks Δ.len Δ.d) _).2 (segSub h Δ).toRepresentation
    obtain ⟨B⟩ := (segSub_spec h Δ).2.2
    obtain ⟨C⟩ := nonempty_piTensor_equiv Δ σ hσ
    exact ⟨(Exponents.jacEquiv e ψ).trans (A.trans (B.trans C))⟩

theorem exists_isSegmentClass : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z := by
  intro k _ _ _ _
  refine ⟨fun Δ => (segIrr h Δ).cl, fun Δ σ hσ e π => ⟨?_, ?_⟩⟩
  · rw [IrrRep.cl_eq_iff]; exact (embeds_iff h Δ σ hσ e π).symm
  · rw [IrrRep.cl_eq_iff]; exact (jac_iff h Δ σ hσ e π).symm

end Published

end GlobalTheory.SegmentClass

theorem GlobalTheory.segmentClass_exists : GlobalTheory.Published.SegmentRepresentation → ∀ (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z :=
  fun h => GlobalTheory.SegmentClass.exists_isSegmentClass h

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacingStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zelevinskySegmentClass_exists_for_every_placing : GlobalTheory.Published.SegmentRepresentation → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z := by
  first | exact @GlobalTheory.segmentClass_exists | exact GlobalTheory.segmentClass_exists | (intros; apply GlobalTheory.segmentClass_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfTypePlaceReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfTypePlaceReductions
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MemLevRed

theorem mem_lev_of_reductions : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (y : GL (Fin T.rank) (EAf D)), LT.Q = ∅ → y ∈ UA D.sp.cm T.gram → y ∈ St βT → ∀ (a b : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1)), (∀ PP, a PP ∈ blockTri (blkOf LT.r LT.t)) → (∀ PP, b PP ∈ blockTri (blkOf LT.r LT.t)) → (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H → (fun PP => upperLeftBlock LT.hr (b PP)) ∈ LT.P.H → (∀ PP : ↥LT.Pg, b PP * redFn βT PP.1 y = a PP) → y ∈ lev D.sp.cm T.gram βT LT := by
  intro D T βT LT y hQ hU hS a b ha hb hHa hHb hab
  have hred : ∀ PP : ↥LT.Pg, redFn βT PP.1 y = (b PP)⁻¹ * a PP := fun PP => by
    rw [← hab PP, inv_mul_cancel_left]
  refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hS, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rw [hred ⟨PP, hP⟩]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hb ⟨PP, hP⟩)) (ha ⟨PP, hP⟩)
  · rw [hQ] at hP
    exact absurd hP (Finset.notMem_empty PP)
  · have h1 : rTup βT LT y = (fun PP => upperLeftBlock LT.hr (b PP)) ⁻¹ * (fun PP => upperLeftBlock LT.hr (a PP)) := by
      funext PP
      have hb2 := blockTri_blkOf_le LT.r LT.t (hb PP)
      have ha2 := blockTri_blkOf_le LT.r LT.t (ha PP)
      show upperLeftBlock LT.hr (redFn βT PP.1 y) = (upperLeftBlock LT.hr (b PP))⁻¹ * upperLeftBlock LT.hr (a PP)
      rw [hred PP]
      unfold upperLeftBlock
      rw [extendMatrixByIdentityAlongIndices_mul _ (Subgroup.inv_mem _ hb2) ha2, extendOne_inv _ hb2]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hHb) hHa

end GlobalTheory.MemLevRed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemLevelOfTypePlaceReductionsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_level_of_type_place_reductions : ∀ {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (LT : LevDat D.host.E ℂ T.rank) (y : GL (Fin T.rank) (EAf D)), LT.Q = ∅ → y ∈ UA D.sp.cm T.gram → y ∈ St βT → ∀ (a b : ∀ PP : ↥LT.Pg, GL (Fin T.rank) (kP PP.1)), (∀ PP, a PP ∈ blockTri (blkOf LT.r LT.t)) → (∀ PP, b PP ∈ blockTri (blkOf LT.r LT.t)) → (fun PP => upperLeftBlock LT.hr (a PP)) ∈ LT.P.H → (fun PP => upperLeftBlock LT.hr (b PP)) ∈ LT.P.H → (∀ PP : ↥LT.Pg, b PP * redFn βT PP.1 y = a PP) → y ∈ lev D.sp.cm T.gram βT LT := by
  first | exact @GlobalTheory.MemLevRed.mem_lev_of_reductions | exact GlobalTheory.MemLevRed.mem_lev_of_reductions | (intros; apply GlobalTheory.MemLevRed.mem_lev_of_reductions <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftsRationalOfRatAt
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open Formalism.IndefR.Arith

namespace GlobalTheory.LiftRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

end Abstract

section Forms

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
  {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL]
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {G : Type} [Group G] [Fintype G] (A : FormsL LL Ks WL W G)

end Forms

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Package

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

theorem j_eq_sum (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (y : Fin (R.nW i) → D.what₂.LL) :
    (R.FW i).j σ y = ∑ k, σ (y k) • (R.FW i).j σ (Pi.basisFun D.what₂.LL (Fin (R.nW i)) k) := by
  conv_lhs => rw [← (Pi.basisFun D.what₂.LL (Fin (R.nW i))).sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smulₛₗ, Pi.basisFun_repr]

theorem span_basis (hU : R.LUnif) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) :
    Submodule.span ℂ (Set.range fun k => (R.FW i).j σ (Pi.basisFun D.what₂.LL (Fin (R.nW i)) k)) = ⊤ := by
  refine top_le_iff.1 ((hU i σ).2.1.ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨y, rfl⟩
  rw [j_eq_sum]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Package

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
  (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
  (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (ph : Fin D.R.m → ℂ)

end GlobalTheory.LiftRat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpOfTranslates
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.HeckeClassSums

section Linear

variable {L : Type} [Field L] {σ : L →+* ℂ} {H : Type} [AddCommGroup H] [Module ℂ H]

end Linear

section Group

open Formalism.IndefR.Bridge

variable {G : Type} [Group G]

end Group

section Row

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev
  Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Local

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

variable {R}


set_option maxHeartbeats 1000000 in
theorem span_jV (hV : R.models_HV) (hj : R.models_jV) (i : Fin D.R.m) (t : T0) : Submodule.span ℂ (Set.range (R.jV i t)) = ⊤ := by
  apply Submodule.map_injective_of_injective (hV i t).1
  rw [Submodule.map_span, Submodule.map_top, (hV i t).2.1, ← Set.range_comp]
  have h1 : (⇑(R.HV i t).e ∘ ⇑(R.jV i t)) = ⇑((R.B.L i t).pres.extL) := funext fun x => hj i t x
  rw [h1]
  exact GlobalTheory.PresBasic.ext_span (R.B.L i t).pres

end Local

section Comparison₂

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

end Comparison₂

end Row

end GlobalTheory.HeckeClassSums
end
end
