module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkedEndEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.ResOpen

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.AwayTriv
open NumberField IsDedekindDomain Neutral.B1

theorem UpperTheory.V.Af.Tw.awayTriv :
    UpperTheory.V.Af.Tw.AwayTriv := by
  intro F B _ _ _ _ _ _ N S hN hinf hS b hbS hbin
  classical
  have k1 : (b : AdeleRing (𝓞 F) F).1 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.mul_inv b)
  have k2 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1 * (b : AdeleRing (𝓞 F) F).1 = 1 :=
    congrArg Prod.fst (Units.inv_mul b)
  have k3 : (b : AdeleRing (𝓞 F) F).2 * ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.mul_inv b)
  have k4 : ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2 * (b : AdeleRing (𝓞 F) F).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul b)
  let binf : Ideles F := ⟨((b : AdeleRing (𝓞 F) F).1, 1), (((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).1, 1),
    Prod.ext k1 (mul_one 1), Prod.ext k2 (mul_one 1)⟩
  let bfin : Ideles F := ⟨(1, (b : AdeleRing (𝓞 F) F).2), (1, ((b⁻¹ : Ideles F) : AdeleRing (𝓞 F) F).2),
    Prod.ext (mul_one 1) k3, Prod.ext (mul_one 1) k4⟩
  have hb : b = binf * bfin := by
    apply Units.ext
    exact Prod.ext (mul_one _).symm (one_mul _).symm
  have hfin2 : (↑bfin : AdeleRing (𝓞 F) F).2 = (↑b : AdeleRing (𝓞 F) F).2 := rfl
  have h1 : N binf = 1 := hinf binf rfl
  have h2 : N bfin = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_local N hN bfin rfl ?_
    intro v
    by_cases hv : v ∈ S
    · have hone : Units.map (GlobalTheory.Mem.LocTriv.ev v) bfin = 1 := by
        apply Units.ext
        rw [Units.coe_map, Units.val_one]
        change (↑bfin : AdeleRing (𝓞 F) F).2 v = 1
        rw [hfin2]
        exact hbin v hv
      rw [hone, map_one, map_one]
    · apply hS v hv
      change Valued.v ((↑bfin : AdeleRing (𝓞 F) F).2 v) = 1
      rw [hfin2]
      exact hbS v hv
  rw [hb, map_mul, h1, h2, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.Kron
open NumberField IsDedekindDomain in
theorem UpperTheory.V.Af.Tw.kron :
    UpperTheory.V.Af.Tw.Kron := by
  intro K _ _
  refine ⟨NumberField.Units.torsionOrder K, ?_, ?_⟩
  · intro l hl hno
    haveI : Fact (Nat.Prime l) := ⟨hl⟩
    rw [Nat.coprime_comm, hl.coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := NumberField.Units.torsion K) l hdvd
    have h1 : IsPrimitiveRoot (g : (𝓞 K)ˣ) l := by
      rw [← hg, ← Subgroup.orderOf_coe]
      exact IsPrimitiveRoot.orderOf _
    have h2 : IsPrimitiveRoot (((g : (𝓞 K)ˣ) : 𝓞 K)) l := IsPrimitiveRoot.coe_units_iff.mpr h1
    have h3 := h2.map_of_injective (f := algebraMap (𝓞 K) K) (FaithfulSMul.algebraMap_injective _ _)
    exact hno ⟨_, h3⟩
  · intro y hy hnorm
    have hy' : ∀ v : HeightOneSpectrum (𝓞 K),
        Valued.v (((Neutral.B1.diagUnits K y : Neutral.B1.Ideles K) : AdeleRing (𝓞 K) K).2 v) = 1 := hy
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K (y : K) (fun v => by
      rw [← GlobalTheory.UpIdeleMod.valued_algebraMap (R := 𝓞 K) v]
      exact le_of_eq (hy' v))
    have hI : IsIntegral ℤ (y : K) := by
      have := NumberField.RingOfIntegers.isIntegral_coe r
      rwa [hr] at this
    obtain ⟨m, hm, hym⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hI hnorm
    have hrm : r ^ m = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_pow, hr, hym, map_one]
    let u : (𝓞 K)ˣ := Units.ofPowEqOne r m hrm hm.ne'
    have hu : u ∈ NumberField.Units.torsion K := by
      rw [NumberField.Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
      exact ⟨m, hm, Units.ext (by simp [u, hrm])⟩
    rw [← NumberField.Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hu
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, ← hr, ← map_pow]
    have hu' := congrArg (fun z : (𝓞 K)ˣ => ((z : 𝓞 K))) hu
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at hu'
    change (u : 𝓞 K) ^ NumberField.Units.torsionOrder K = 1 at hu'
    have hur : (u : 𝓞 K) = r := Units.val_ofPowEqOne r m hrm hm.ne'
    rw [hur] at hu'
    rw [hu', map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.PhiPart
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.SplitIso
open NumberField IsDedekindDomain GroundTheory.Global.SemiLocal

theorem UpperTheory.V.Af.Tw.splitIso :
    UpperTheory.V.Af.Tw.SplitIso := by
  intro F L _ _ _ _ _ h2 w w' hne hunder
  classical
  set v := HeightOneSpectrum.under (𝓞 F) w with hv
  haveI hw : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  haveI hw' : w'.asIdeal.LiesOver v.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hunder).symm⟩
  have hsum := sum_ramificationIdx_mul_inertiaDeg L v
  rw [h2] at hsum
  have hpos : ∀ u : PlacesOver L v, 1 ≤ (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) *
      (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F) := fun u =>
    Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)
  let a : PlacesOver L v := ⟨w, hw⟩
  let b : PlacesOver L v := ⟨w', hw'⟩
  have hab : a ≠ b := fun h => hne (congrArg Subtype.val h).symm
  have hle := Finset.add_le_sum (s := Finset.univ)
    (f := fun u : PlacesOver L v => (u : HeightOneSpectrum (𝓞 L)).asIdeal.ramificationIdx (𝓞 F) *
      (u : HeightOneSpectrum (𝓞 L)).asIdeal.inertiaDeg (𝓞 F))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ a) (Finset.mem_univ b) hab
  have hle2 := hle.trans_eq hsum
  have ha1 := hpos a
  have hb1 := hpos b
  have h1 : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    change _ + _ ≤ 2 at hle2
    change 1 ≤ w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) at ha1
    change 1 ≤ w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) at hb1
    change w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) +
      w'.asIdeal.ramificationIdx (𝓞 F) * w'.asIdeal.inertiaDeg (𝓞 F) ≤ 2 at hle2
    omega
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_right h1
  have hfin : Module.finrank (v.adicCompletion F) (w.adicCompletion L) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg L v w, h1]
  have hbij : Function.Bijective (completionMap v w) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin
  let e := RingEquiv.ofBijective (completionMap v w) hbij
  refine ⟨(e.symm : w.adicCompletion L →+* v.adicCompletion F), ?_, ?_⟩
  · refine GlobalTheory.DenseCompl.continuous_of_valued_eq (HeightOneSpectrum.valuedAdicCompletion_surjective L w) _ ?_
    intro y
    obtain ⟨x, rfl⟩ := hbij.2 y
    have hx : (e.symm : w.adicCompletion L →+* v.adicCompletion F) (completionMap v w x) = x :=
      e.symm_apply_apply x
    rw [hx, valued_completionMap, he, pow_one]
  · intro x
    exact e.symm_apply_apply x
end

open NumberField IsDedekindDomain Neutral.B1 GlobalTheory.Mem.Chr.Model
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap)

private def evAt (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    AdeleRing (𝓞 L) L →* w.adicCompletion L where
  toFun a := a.2 w
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem evAt_continuous (L : Type) [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) :
    Continuous (evAt L w) :=
  (RestrictedProduct.continuous_eval w).comp continuous_snd

private theorem exists_local (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    (h2 : Module.finrank F L = 2) (l : ℕ) (Φ : Set (HeightOneSpectrum (𝓞 L))) (hΦ : UpperTheory.V.Af.Tw.IsType F l Φ)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ q : Ideles L →* (v.adicCompletion F)ˣ, Continuous q ∧ (((l : ℕ) : 𝓞 F) ∈ v.asIdeal →
      (∀ a : Ideles F, (q (ideleMap F L a)).val = a.val.2 v) ∧
      ∀ x : Ideles L, (∀ w : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → w ∈ Φ → x.val.2 w = 1) → q x = 1) := by
  by_cases hv : ((l : ℕ) : 𝓞 F) ∈ v.asIdeal
  swap
  · exact ⟨1, continuous_const, fun h => absurd h hv⟩
  have hl : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v → ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := fun w hw => by
    rw [← hw] at hv
    have : algebraMap (𝓞 F) (𝓞 L) ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := hv
    rwa [map_natCast] at this
  obtain ⟨w, w', hw, hne, hw', hin⟩ : ∃ w w' : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v ∧ w' ≠ w ∧
      w'.under (𝓞 F) = w.under (𝓞 F) ∧ w ∈ Φ := by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L)))
    let u : HeightOneSpectrum (𝓞 L) := ⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
    have hu : u.under (𝓞 F) = v := HeightOneSpectrum.ext hP'.over.symm
    obtain ⟨u', h1, h3, h4⟩ := hΦ u (hl u hu)
    by_cases hin : u ∈ Φ
    · exact ⟨u, u', hu, h1, h3, hin⟩
    · exact ⟨u', u, h3.trans hu, h1.symm, h3.symm, by_contra fun h => hin (h4.2 h)⟩
  have hlw := hl w hw
  subst hw
  obtain ⟨r, hr, hr'⟩ := UpperTheory.V.Af.Tw.splitIso F L h2 w w' hne hw'
  refine ⟨Units.map (r.toMonoidHom.comp (evAt L w)), Continuous.units_map _ (hr.comp (evAt_continuous L w)),
    fun _ => ⟨fun a => hr' _, fun x hx => Units.ext ?_⟩⟩
  show r (x.val.2 w) = 1
  rw [hx w hlw hin, map_one]

theorem UpperTheory.V.Af.Tw.phiPart :
    UpperTheory.V.Af.Tw.PhiPart := by
  intro F L _ _ _ _ _ h2 l hl Φ hΦ
  classical
  choose q hq hq' using exists_local F L h2 l Φ hΦ
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h0 : Ideal.span {((l : ℕ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 hl
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let p : Ideles L →* Ideles F := ∏ v ∈ hfin.toFinset, (GlobalTheory.Mem.Chr.localIdele F v).comp (q v)
  have hp : ∀ x, p x = ∏ v ∈ hfin.toFinset, GlobalTheory.Mem.Chr.localIdele F v (q v x) := by
    intro x
    change (∏ v ∈ hfin.toFinset, (GlobalTheory.Mem.Chr.localIdele F v).comp (q v)) x = _
    generalize hfin.toFinset = s
    induction s using Finset.induction_on with
    | empty => simp
    | insert v s hv ih => simp [hv, ih]
  have hc : ∀ x u, (p x).val.2 u = ∏ v ∈ hfin.toFinset, (GlobalTheory.Mem.Chr.localIdele F v (q v x)).val.2 u := fun x u => by
    rw [hp]
    exact map_prod ((evAt F u).comp (Units.coeHom _)) _ _
  refine ⟨p, ?_, fun a v hv => ?_, fun x v hv => ?_, fun x hx => ?_⟩
  · rw [show (p : Ideles L → Ideles F) = _ from funext hp]
    exact continuous_finsetProd _ fun v _ => (localIdele_continuous F v).comp (hq v)
  · rw [hc, Finset.prod_eq_single_of_mem v (hfin.mem_toFinset.2 hv)
      fun u _ hu => localIdele_snd_ne F u v hu.symm _, GlobalTheory.Mem.Chr.Model.localIdele_snd_self, (hq' v hv).1]
  · rw [hc]
    refine Finset.prod_eq_one fun u hu => localIdele_snd_ne F u v ?_ _
    rintro rfl
    exact hv (hfin.mem_toFinset.1 hu)
  · rw [hp]
    exact Finset.prod_eq_one fun u hu => by rw [(hq' u (hfin.mem_toFinset.1 hu)).2 x hx, map_one]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.GlueExt
namespace UpperTheory.V.Af.Tw

private theorem glue_ext {G H B : Type*} [CommGroup G] [CommGroup H] [CommGroup B] (hB : KStar.Choice.IsDiv B)
    (p : G →* H) (f : G →* B) (h : ∀ x, p x = 1 → f x = 1) : ∃ F : H →* B, ∀ x, F (p x) = f x := by
  classical
  obtain ⟨F, hF⟩ := hB.exists_extension p.range
    ((QuotientGroup.lift p.ker f (fun x hx => (MonoidHom.mem_ker).2 (h x ((MonoidHom.mem_ker).1 hx)))).comp
      (QuotientGroup.quotientKerEquivRange p).symm.toMonoidHom)
  refine ⟨F, fun x => (hF ⟨p x, x, rfl⟩).trans ?_⟩
  have hx : (QuotientGroup.quotientKerEquivRange p).symm ⟨p x, x, rfl⟩ = (x : G ⧸ p.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx]
  rfl

private theorem glue_exp (n M l : ℕ) (hM : 0 < M) (hl : l.Prime) :
    ∃ e k : ℕ, e ≡ 1 [MOD n] ∧ 0 < k ∧ (n.Coprime l → k.Coprime l) ∧ M ∣ e * k := by
  by_cases hc : n.Coprime l
  · have hM0 : M ≠ 0 := hM.ne'
    have hco : n.Coprime (l ^ M.factorization l) := Nat.Coprime.pow_right _ hc
    obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hco 1 0
    refine ⟨e, M / l ^ M.factorization l, he1, Nat.ordCompl_pos l hM0,
      fun _ => (Nat.coprime_ordCompl hl hM0).symm, ?_⟩
    have hd : l ^ M.factorization l ∣ e := (Nat.modEq_zero_iff_dvd).1 he0
    calc M = l ^ M.factorization l * (M / l ^ M.factorization l) :=
          (Nat.ordProj_mul_ordCompl_eq_self M l).symm
      _ ∣ e * (M / l ^ M.factorization l) := mul_dvd_mul_right hd _
  · exact ⟨1, M, Nat.ModEq.refl 1, hM, fun h' => absurd h' hc, by simp⟩

theorem glue : Glue := by
  unfold Glue
  intro I J K B _ _ _ _ hB i d c σ U V N g n M l hM hl h1 h2 h3 h4 h5 h6 h7 h8
  obtain ⟨e, k, he, hk0, hkc, hMk⟩ := glue_exp n M l hM hl
  obtain ⟨p₀, hp₀⟩ : ∃ p₀ : J × K × U →* I, ∀ z, p₀ z = i z.1 * d z.2.1 * (z.2.2 : I) :=
    ⟨i.comp (MonoidHom.fst _ _) * d.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _)) *
      U.subtype.comp ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)), fun z => rfl⟩
  have hq : ∀ z, p₀ z = 1 → (z.2.2 : I) / c z.2.2 = d (σ z.2.1 / z.2.1) := by
    intro z hz
    rw [hp₀] at hz
    have hu : (z.2.2 : I) = (i z.1 * d z.2.1)⁻¹ := eq_inv_of_mul_eq_one_right hz
    rw [hu, map_inv, map_mul, h1, h2, map_div]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  obtain ⟨pθ, hpθ⟩ : ∃ pθ : p₀.ker × V →* I,
      ∀ w, pθ w = d (σ (w.1 : J × K × U).2.1 / (w.1 : J × K × U).2.1) * (w.2 : I) :=
    ⟨d.comp ((σ / MonoidHom.id K).comp ((MonoidHom.fst _ _).comp ((MonoidHom.snd _ _).comp
      (p₀.ker.subtype.comp (MonoidHom.fst _ _))))) * V.subtype.comp (MonoidHom.snd _ _), fun w => rfl⟩
  obtain ⟨fθ, hfθ⟩ : ∃ fθ : p₀.ker × V →* B,
      ∀ w, fθ w = (N (w.1 : J × K × U).1 * g ((w.1 : J × K × U).2.2 : I))⁻¹ :=
    ⟨((N.comp (MonoidHom.fst _ _) * g.comp (U.subtype.comp ((MonoidHom.snd _ _).comp
      (MonoidHom.snd _ _)))).comp (p₀.ker.subtype.comp (MonoidHom.fst _ _)))⁻¹, fun w => rfl⟩
  obtain ⟨θ₁, hθ₁⟩ := glue_ext hB pθ fθ (by
    rintro ⟨⟨⟨a, x, u⟩, hz⟩, v⟩ hw
    rw [hpθ] at hw
    rw [hfθ]
    dsimp only at hw ⊢
    have hz' : p₀ (a, x, u) = 1 := MonoidHom.mem_ker.1 hz
    rw [hp₀] at hz'
    dsimp only at hz'
    have hv : d (σ x / x) = (v : I)⁻¹ := eq_inv_of_mul_eq_one_left hw
    have hσ : σ x = x := h7 x (by rw [hv]; exact inv_mem v.2)
    obtain ⟨a', ha', hN⟩ := h5 x hσ
    have hiu : i (a * a') = (u : I)⁻¹ := by
      rw [map_mul, ha']
      exact eq_inv_of_mul_eq_one_left hz'
    have h4' := h4 (a * a') (by rw [hiu]; exact inv_mem u.2)
    rw [hiu, map_inv, map_mul, hN, mul_one] at h4'
    rw [← h4', inv_mul_cancel, inv_one])
  obtain ⟨θ, hθ⟩ : ∃ θ : I →* B, ∀ y, θ y = θ₁ y ^ e := ⟨(powMonoidHom e).comp θ₁, fun y => rfl⟩
  have hV : ∀ v ∈ V, θ₁ v = 1 := by
    intro v hv
    have h := hθ₁ (1, ⟨v, hv⟩)
    rw [hpθ, hfθ] at h
    simpa using h
  have hZ : ∀ z, p₀ z = 1 → θ (z.2.2 / c z.2.2) = (N z.1 * g z.2.2)⁻¹ := by
    intro z hz
    have h := hθ₁ (⟨z, MonoidHom.mem_ker.2 hz⟩, 1)
    rw [hpθ, hfθ] at h
    dsimp only at h
    simp only [OneMemClass.coe_one, mul_one] at h
    rw [hθ, hq z hz, h]
    have hw : ((N z.1 * g z.2.2)⁻¹) ^ n = 1 := by
      have hmem : d (σ z.2.1 / z.2.1) ∈ U := by
        rw [← hq z hz]
        exact div_mem z.2.2.2 (h3 _ z.2.2.2)
      rw [← h, ← map_pow, ← map_pow, h6 _ hmem, map_one, map_one]
    rw [pow_eq_pow_mod e hw, show e % n = 1 % n from he, ← pow_eq_pow_mod 1 hw, pow_one]
  obtain ⟨f, hf⟩ : ∃ f : J × K × U →* B, ∀ z, f z = N z.1 * (g z.2.2 * θ (z.2.2 / c z.2.2)) :=
    ⟨N.comp (MonoidHom.fst _ _) * (g.comp (U.subtype.comp ((MonoidHom.snd _ _).comp
      (MonoidHom.snd _ _))) * θ.comp ((U.subtype / c.comp U.subtype).comp
      ((MonoidHom.snd _ _).comp (MonoidHom.snd _ _)))), fun z => rfl⟩
  obtain ⟨ψ, hψ⟩ := glue_ext hB p₀ f (by
    intro z hz
    rw [hf, hZ z hz, ← mul_assoc, mul_inv_cancel])
  refine ⟨ψ, θ, fun a => ?_, fun x => ?_, fun u hu => ?_, fun v hv => ?_, k, hk0, hkc, fun u hu => ?_⟩
  · have h := hψ (a, 1, 1)
    rw [hp₀, hf] at h
    simpa using h
  · have h := hψ (1, x, 1)
    rw [hp₀, hf] at h
    simpa using h
  · have h := hψ (1, 1, ⟨u, hu⟩)
    rw [hp₀, hf] at h
    simpa using h
  · rw [hθ, hV v hv, one_pow]
  · obtain ⟨j, hj⟩ := hMk
    rw [hθ, ← pow_mul, ← map_pow, hj, pow_mul]
    exact hV _ (pow_mem (h8 u hu) j)

end UpperTheory.V.Af.Tw
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.LocProd
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap finiteCompletionMap infiniteAdeleMap)

private noncomputable def UpperTheory.V.Af.Tw.compAt (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 K) K →* v.adicCompletion K where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def UpperTheory.V.Af.Tw.infPart (K : Type) [Field K] [NumberField K] :
    AdeleRing (𝓞 K) K →* InfiniteAdeleRing K where
  toFun a := a.1
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem UpperTheory.V.Af.Tw.loc_same {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 v = x := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_same _ _ _

private theorem UpperTheory.V.Af.Tw.loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)}
    (h : w ≠ v) (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 w = 1 := by
  classical
  simp only [localIdele, finiteSingle, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  exact RestrictedProduct.mulSingle_eq_of_ne _ _ h

theorem UpperTheory.V.Af.Tw.locProd :
    UpperTheory.V.Af.Tw.LocProd := by
  unfold UpperTheory.V.Af.Tw.LocProd
  intro F L _ _ _ _ _ v x
  classical
  let y : ∀ w : HeightOneSpectrum (𝓞 L), (w.adicCompletion L)ˣ := fun w =>
    Units.map (finiteCompletionMap F L w).toMonoidHom
      (Units.map (UpperTheory.V.Af.Tw.compAt F (HeightOneSpectrum.under (𝓞 F) w)) (localIdele F v x))
  have hy : ∀ w, ((y w : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      finiteCompletionMap F L w ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w)) :=
    fun w => rfl
  have hmem : ∀ w : HeightOneSpectrum (𝓞 L),
      w ∈ aboveF F v ↔ HeightOneSpectrum.under (𝓞 F) w = v :=
    fun w => by
      unfold aboveF
      simp
  have key : ∀ a b : AdeleRing (𝓞 L) L, UpperTheory.V.Af.Tw.infPart L a = UpperTheory.V.Af.Tw.infPart L b →
      (∀ w, UpperTheory.V.Af.Tw.compAt L w a = UpperTheory.V.Af.Tw.compAt L w b) → a = b :=
    fun a b h1 h2 => Prod.ext h1 (RestrictedProduct.ext _ _ h2)
  refine ⟨y, ?_, ?_⟩
  · apply Units.ext
    rw [Units.coe_prod]
    apply key
    · rw [map_prod]
      have h1 : ∀ w, UpperTheory.V.Af.Tw.infPart L ((localIdele L w (y w)).val) = 1 := fun w => rfl
      simp only [h1, Finset.prod_const_one]
      show infiniteAdeleMap F L 1 = 1
      exact map_one _
    · intro w'
      rw [map_prod]
      show finiteCompletionMap F L w' ((localIdele F v x).val.2 (HeightOneSpectrum.under (𝓞 F) w')) =
        ∏ w ∈ aboveF F v, (localIdele L w (y w)).val.2 w'
      by_cases hw' : HeightOneSpectrum.under (𝓞 F) w' = v
      · rw [Finset.prod_eq_single w']
        · rw [UpperTheory.V.Af.Tw.loc_same, hy]
        · intro b _ hb
          exact UpperTheory.V.Af.Tw.loc_ne (Ne.symm hb) _
        · intro h
          exact absurd ((hmem w').mpr hw') h
      · rw [UpperTheory.V.Af.Tw.loc_ne hw', map_one, Finset.prod_eq_one]
        intro b hb
        exact UpperTheory.V.Af.Tw.loc_ne (fun h => hw' (by rw [h]; exact (hmem b).mp hb)) _
  · intro hunr hx w hw
    subst hw
    unfold IsUnifAt at hx ⊢
    rw [hy, UpperTheory.V.Af.Tw.loc_same, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, hunr w rfl, pow_one]
    exact hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.LevPow
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (unitIdl)

namespace UpperTheory.V.Af.Tw

private theorem loc (K : Type) [Field K] [NumberField K] {N : ℕ} (hN : N ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ M : ℕ, 0 < M ∧ ∀ x : v.adicCompletion K, Valued.v x = 1 → ∀ k : ℕ, M ∣ k →
      Valued.v (x ^ k - 1) ≤ Valued.v (N : v.adicCompletion K) := by
  classical
  let I : Ideal (v.adicCompletionIntegers K) := Ideal.span {(N : v.adicCompletionIntegers K)}
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    intro h
    apply hN
    have := congrArg (fun r : v.adicCompletionIntegers K => (r : v.adicCompletion K)) h
    simpa using this
  haveI := Formalism.UG.P.glint_finite_quotient_of_dvr inferInstance I hI
  haveI : Finite (v.adicCompletionIntegers K ⧸ I)ˣ :=
    Finite.of_injective (fun u : (v.adicCompletionIntegers K ⧸ I)ˣ => (u : v.adicCompletionIntegers K ⧸ I))
      (fun a b h => Units.ext h)
  refine ⟨Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ, Nat.card_pos, ?_⟩
  intro x hx k hk
  have hxR : x ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hx.le
  have hyR : x⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hx, inv_one]
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx
    exact zero_ne_one hx
  let u : (v.adicCompletionIntegers K)ˣ :=
    ⟨⟨x, hxR⟩, ⟨x⁻¹, hyR⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩
  obtain ⟨j, rfl⟩ := hk
  have h1 : (Units.map (Ideal.Quotient.mk I).toMonoidHom u) ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) = 1 := by
    rw [pow_mul, pow_card_eq_one', one_pow]
  have h2 : ((⟨x, hxR⟩ : v.adicCompletionIntegers K) ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) - 1) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
    have := congrArg Units.val h1
    simpa [u] using this
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
  have hy' : x ^ (Nat.card (v.adicCompletionIntegers K ⧸ I)ˣ * j) - 1 =
      (y : v.adicCompletion K) * (N : v.adicCompletion K) := by
    have := congrArg (fun r : v.adicCompletionIntegers K => (r : v.adicCompletion K)) hy
    simpa using this.symm
  rw [hy', map_mul]
  have hyle : Valued.v (y : v.adicCompletion K) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 y.2
  simpa using mul_le_mul' hyle (le_refl (Valued.v (N : v.adicCompletion K)))

theorem levPow : LevPow := by
  unfold LevPow
  intro K _ _ N hN
  choose M hMpos hM using fun v : HeightOneSpectrum (𝓞 K) => loc K hN v
  have hN0 : Ideal.span {(N : 𝓞 K)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  have hfin := Ideal.finite_factors hN0
  refine ⟨∏ v ∈ hfin.toFinset, M v, Finset.prod_pos (fun v _ => hMpos v), ?_⟩
  intro u hu
  refine ⟨pow_mem hu _, fun v => ?_⟩
  have hpow : ∀ P : ℕ, (u ^ P).val.2 v = (u.val.2 v) ^ P := by
    intro P
    induction P with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Units.val_mul, pow_succ, ← ih]
      rfl
  have hu1 : Valued.v (u.val.2 v) = 1 := hu v
  show Valued.v ((u ^ (∏ v ∈ hfin.toFinset, M v)).val.2 v - 1) ≤ Valued.v (N : v.adicCompletion K)
  rw [hpow]
  by_cases hv : v ∈ hfin.toFinset
  · exact hM v _ hu1 _ (Finset.dvd_prod_of_mem M hv)
  · rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton] at hv
    have hlt := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) v (N : 𝓞 K)).not.2 hv
    have hle := HeightOneSpectrum.valuation_le_one (K := K) v (N : 𝓞 K)
    have h2 := PI.IntAdCpctOpenWork.valued_algebraMap v (N : K)
    simp at h2 hlt hle
    have hN1 : Valued.v (N : v.adicCompletion K) = 1 := by
      rw [h2]
      exact le_antisymm hle hlt
    rw [hN1]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [map_pow, hu1, one_pow]
    · rw [map_one]

end UpperTheory.V.Af.Tw
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.UnrAE
open NumberField IsDedekindDomain

theorem UpperTheory.V.Af.Tw.unrAE :
    UpperTheory.V.Af.Tw.UnrAE := by
  unfold UpperTheory.V.Af.Tw.UnrAE
  intro F L _ _ _ _ _
  letI := FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 L))
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) := inferInstance
  have hD0 : differentIdeal (𝓞 F) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 L)
  have hfin := Ideal.finite_factors (R := 𝓞 L) (I := differentIdeal (𝓞 F) (𝓞 L)) hD0
  rw [Filter.eventually_cofinite]
  refine (hfin.image (HeightOneSpectrum.under (𝓞 F))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  unfold UpperTheory.V.Af.Tw.Unr at hv
  push_neg at hv
  obtain ⟨w, rfl, he⟩ := hv
  refine ⟨w, ?_, rfl⟩
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤
      w.asIdeal := Ideal.map_comap_le
  have h2 : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤
      w.asIdeal ^ 2 := by
    by_contra h
    exact he (Ideal.ramificationIdx'_spec (by rwa [pow_one]) h)
  haveI := (HeightOneSpectrum.under (𝓞 F) w).isMaximal
  have hdvd := pow_sub_one_dvd_differentIdeal (A := 𝓞 F) (P := w.asIdeal) (e := 2)
    (hp := (HeightOneSpectrum.under (𝓞 F) w).ne_bot) (hP := Ideal.dvd_iff_le.mpr h2)
  simpa using hdvd
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.FrobSplit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial UpperTheory.V.Af UpperTheory.V.Af.Tw

private theorem int_mem {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    (A : ValuationSubring Ω) (x : 𝓞 L) : algebraMap L Ω x ∈ A := by
  have hi : IsIntegral ℤ (algebraMap L Ω x) := x.isIntegral_coe.algebraMap
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 (hi.tower_top (A := A))
  rw [← hy]
  exact y.2

private theorem exists_above {F L Ω : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω]
    [Algebra F L] [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {v : HeightOneSpectrum (𝓞 F)}
    {A : ValuationSubring Ω} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v ∧ IsPlaceOver A w := by
  let φ : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A.toSubring (int_mem A)
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap φ :=
    fun x => (A.valuation_lt_one_iff (φ x)).symm
  have hu : ((IsLocalRing.maximalIdeal A).comap φ).under (𝓞 F) = v.asIdeal := by
    ext x
    rw [← hA x, IsScalarTower.algebraMap_apply F L Ω]
    exact (hP (algebraMap (𝓞 F) (𝓞 L) x)).symm
  haveI : ((IsLocalRing.maximalIdeal A).comap φ).LiesOver v.asIdeal := ⟨hu.symm⟩
  exact ⟨⟨(IsLocalRing.maximalIdeal A).comap φ, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot _⟩,
    HeightOneSpectrum.ext hu, hP⟩

private theorem normV_under' {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  rw [show normV w = Ideal.absNorm w.asIdeal by
        rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply],
      show normV (w.under (𝓞 K)) = Ideal.absNorm (w.under (𝓞 K)).asIdeal by
        rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem normV_le {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : 1 < q)
    (h : ∀ x : 𝓞 K, x - x ^ q ∈ w.asIdeal) : normV w ≤ q := by
  have := w.isMaximal
  letI : Field (𝓞 K ⧸ w.asIdeal) := Ideal.Quotient.field _
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Fintype.ofFinite (𝓞 K ⧸ w.asIdeal)
  have e : normV w = Fintype.card (𝓞 K ⧸ w.asIdeal) := Nat.card_eq_fintype_card
  rw [e]
  by_contra hlt
  refine Polynomial.X_pow_sub_X_ne_zero (R := 𝓞 K ⧸ w.asIdeal) hq
    (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun y _ => ?_) ?_)
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have := Ideal.Quotient.eq.2 (h x)
    rw [map_pow] at this
    rw [eval_sub, eval_pow, eval_X, ← this, sub_self]
  · rw [Polynomial.natDegree_X_pow_sub_X hq, Finset.card_univ]
    exact not_le.1 hlt

private theorem two_of_sum {ι : Type} [Fintype ι] (f : ι → ℕ) (hf : ∀ i, 0 < f i) (hs : ∑ i, f i = 2) (a : ι)
    (ha : f a = 1) : ∃ b, b ≠ a ∧ f b = 1 ∧ ∀ c, c = a ∨ c = b := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ha] at hs
  have h1 : ∑ i ∈ Finset.univ.erase a, f i = 1 := by omega
  obtain ⟨b, hb⟩ : (Finset.univ.erase a).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at h1
    simp at h1
  rw [← Finset.add_sum_erase _ _ hb] at h1
  have := hf b
  refine ⟨b, Finset.ne_of_mem_erase hb, by omega, fun c => ?_⟩
  by_contra hc
  rw [not_or] at hc
  have h2 : f c ≤ ∑ i ∈ (Finset.univ.erase a).erase b, f i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (by simp [hc.1, hc.2])
  have := hf c
  omega

theorem UpperTheory.V.Af.Tw.frobSplit :
    UpperTheory.V.Af.Tw.FrobSplit := by
  intro F L Ω _ _ _ _ _ _ _ _ _ _ _ h2 v A hur hA s hs
  classical
  obtain ⟨w, hwv, hw⟩ := exists_above (L := L) hA
  have hq : 1 < normV v := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hle : normV w ≤ normV v := by
    refine normV_le w hq fun x => ?_
    rw [← hw]
    have h3 := hs.2 _ ((A.valuation_le_one_iff _).2 (int_mem A x))
    have h4 : resG F L Ω s (algebraMap L Ω x) = algebraMap L Ω x := s.commutes x
    rw [h4] at h3
    simpa using h3
  haveI := v.isMaximal
  haveI := w.isPrime
  have hf : w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
    rw [normV_under' (K := F) w, hwv] at hle
    have h5 : 0 < w.asIdeal.inertiaDeg (𝓞 F) := Ideal.inertiaDeg_pos _ _
    have h6 : w.asIdeal.inertiaDeg (𝓞 F) ≤ 1 :=
      (Nat.pow_le_pow_iff_right hq).1 (by rwa [pow_one])
    omega
  have hl : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 F) = v → u.asIdeal ∈ v.asIdeal.primesOver (𝓞 L) :=
    fun u hu => ⟨u.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩⟩
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := by
    haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ (w.under (𝓞 F)).ne_bot]
    exact hur w hwv
  haveI := (IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).fintype
  have hsum := Ideal.sum_ramification_inertia_eq_finrank v.asIdeal (𝓞 L)
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 L) L, h2] at hsum
  obtain ⟨⟨Q, hQ, hQv⟩, hne, h1, hall⟩ := two_of_sum _
    (fun P => Nat.mul_pos (Ideal.ramificationIdx_pos _ _) (Ideal.inertiaDeg_pos _ _)) hsum
    ⟨w.asIdeal, hl w hwv⟩ (by simp only [he, hf])
  let w' : HeightOneSpectrum (𝓞 L) := ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
  have hw' : w'.under (𝓞 F) = v := HeightOneSpectrum.ext hQv.over.symm
  have hf' : w'.asIdeal.inertiaDeg (𝓞 F) = 1 := Nat.eq_one_of_mul_eq_one_left h1
  refine ⟨w, w', fun h => hne (Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)), fun u => ⟨fun hu => ?_, ?_⟩,
    hw, ?_, ?_⟩
  · rcases hall ⟨u.asIdeal, hl u hu⟩ with h | h
    · exact Or.inl (HeightOneSpectrum.ext (congrArg Subtype.val h))
    · exact Or.inr (HeightOneSpectrum.ext (congrArg Subtype.val h))
  · rintro (rfl | rfl)
    exacts [hwv, hw']
  · rw [normV_under' (K := F) w, hwv, hf, pow_one]
  · rw [normV_under' (K := F) w', hw', hf', pow_one]
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Af.Tw
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap adeleMap finiteCompletionMap ideleConj IsCMExtension)
open GlobalTheory.Mem.Chr (unitIdl)

private theorem loc_self {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    (localIdele K v x).val.2 v = x := by
  classical
  exact Function.update_self v (x : v.adicCompletion K) (fun w : HeightOneSpectrum (𝓞 K) => (1 : w.adicCompletion K))

private theorem loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : (localIdele K v x).val.2 w = 1 := by
  classical
  exact Function.update_of_ne h (x : v.adicCompletion K) (fun w : HeightOneSpectrum (𝓞 K) => (1 : w.adicCompletion K))

private theorem loc_unit {K : Type} [Field K] [NumberField K] {v : HeightOneSpectrum (𝓞 K)}
    {x : (v.adicCompletion K)ˣ} (hx : IsUnitAt v x) : localIdele K v x ∈ unitIdl K := fun w => by
  by_cases h : w = v
  · subst h
    rw [loc_self]
    exact hx
  · rw [_root_.loc_ne h, map_one]

private theorem lev_one {K : Type} [Field K] [NumberField K] {a : Ideles K} : a ∈ lev K 1 ↔ a ∈ unitIdl K :=
  ⟨fun h => h.1, fun h => ⟨h, fun v => by
    rw [Nat.cast_one, map_one]
    exact Valuation.map_sub_le _ (h v).le (map_one _).le⟩⟩

private theorem loc_lev {K : Type} [Field K] [NumberField K] {l : ℕ} {v : HeightOneSpectrum (𝓞 K)}
    (hv : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal) {x : (v.adicCompletion K)ˣ} (hx : IsUnitAt v x) : localIdele K v x ∈ lev K l :=
  ⟨loc_unit hx, fun w => by
    by_cases h : w = v
    · subst h
      have e : Valued.v (l : w.adicCompletion K) = 1 := by
        rw [← map_natCast (algebraMap K (w.adicCompletion K)), GlobalTheory.UpIdeleMod.valued_algebraMap,
          ← map_natCast (algebraMap (𝓞 K) K)]
        exact (HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hv
      rw [e]
      exact Valuation.map_sub_le _ (loc_unit hx w).le (map_one _).le
    · rw [_root_.loc_ne h, sub_self, map_zero]
      exact zero_le⟩

private theorem isDiv_qbar (l : ℕ) [Fact l.Prime] : KStar.Choice.IsDiv (Qbar l)ˣ := fun n hn a => by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (a : Qbar l) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact a.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩

private theorem ideleExt_of (hG : Glue) (hP : LevPow) (hK : Kron) (hΦ : PhiPart) (hA : AwayTriv)
    (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [IsCMField L] [Algebra F L] (hF : IsTotallyReal F)
    (h2 : Module.finrank F L = 2) (q : ℕ) [hl : Fact q.Prime] (l : ℕ) (hl3 : 3 ≤ l) (Φ : Set (HeightOneSpectrum (𝓞 L))) (hT : IsType F l Φ)
    (N : Ideles F →* (Qbar q)ˣ) (hN : Continuous N) (hd : ∀ k, N (diagUnits F k) = 1) (hi : ∀ z : Ideles F, z.val.2 = 1 → N z = 1)
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ x, IsUnitAt v x → N (localIdele F v x) = 1) :
      ∃ ψ : Ideles L →* (Qbar q)ˣ, Continuous ψ ∧ (∀ a, ψ (ideleMap F L a) = N a) ∧ (∀ k, ψ (diagUnits L k) = 1) ∧
        (∀ z : Ideles L, z.val.2 = 1 → ψ z = 1) ∧
        ∃ k : ℕ, 0 < k ∧
          ∀ (w : HeightOneSpectrum (𝓞 L)) (x : (w.adicCompletion L)ˣ), IsUnitAt w x →
            (((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ψ (localIdele L w x) = 1) ∧ (w ∉ Φ → ψ (localIdele L w x) ^ k = 1) := by
  have hl0 : l ≠ 0 := by omega
  haveI : IsCMExtension F L := ⟨hF, inferInstance, { finrank_eq_two' := h2 }⟩
  obtain ⟨p, hp, p1, p2, p3⟩ := hΦ F L h2 l hl0 Φ hT
  obtain ⟨M, hM, hMu⟩ := hP L l hl0
  obtain ⟨n, -, hnu⟩ := hK L
  let c := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj F L
  let σ : Lˣ →* Lˣ := Units.map c.toRingEquiv.toRingHom.toMonoidHom
  have c3 : ∀ (m : ℕ), ∀ u ∈ lev L m, ideleConj F L u ∈ lev L m := fun m u hu =>
    (@ideleMap_mem_lev L L _ _ _ _ c.toRingEquiv.toRingHom.toAlgebra _ u).2 hu
  have hnorm : ∀ (x : Lˣ) (φ : L →+* ℂ), ‖φ (σ x / x : Lˣ)‖ = 1 := fun x φ => by
    rw [Units.val_div_eq_div_val, map_div₀, norm_div]
    have : φ (σ x : Lˣ) = starRingEnd ℂ (φ x) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj F L φ x
    rw [this, Complex.norm_conj, div_self (by simp)]
  obtain ⟨ψ, θ, h1, h3, h4, h5, k, hk, -, h6⟩ := hG (Ideles L) (Ideles F) Lˣ (Qbar q)ˣ (isDiv_qbar q) (ideleMap F L)
    (diagUnits L) (ideleConj F L) σ (unitIdl L) (lev L l) N (N.comp p) n M q hM hl.out
    (fun a => Units.ext (GlobalTheory.UnitaryHeckeBaseChange.adeleConj_adeleMap _))
    (fun x => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele F L x)
    (fun u hu => lev_one.1 (c3 1 u (lev_one.2 hu)))
    (fun a ha => by
      have ha' : a ∈ unitIdl F := lev_one.1 ((ideleMap_mem_lev F L 1 a).1 (lev_one.2 ha))
      have e : ∀ v, (a / p (ideleMap F L a)).val.2 v * (p (ideleMap F L a)).val.2 v = a.val.2 v := fun v =>
        congrArg (fun z : Ideles F => z.val.2 v) (div_mul_cancel a (p (ideleMap F L a)))
      have := hA F _ N {v | ((l : ℕ) : 𝓞 F) ∈ v.asIdeal} hN hi hu (a / p (ideleMap F L a))
        (fun v hv => by
          have := e v
          rw [p2 _ v hv, mul_one] at this
          rw [this]
          exact ha' v)
        (fun v hv => by
          have := e v
          rw [p1 _ v hv] at this
          refine mul_right_cancel₀ (b := a.val.2 v) (fun h0 => ?_) (this.trans (one_mul _).symm)
          have h := ha' v
          rw [h0, map_zero] at h
          exact zero_ne_one h)
      rw [map_div, div_eq_one] at this
      exact this.symm)
    (fun x hx => by
      obtain ⟨t, ht⟩ := GlobalTheory.UnitaryHeckeBaseChange.exists_of_fixed
        ((GlobalTheory.UnitaryHeckeBaseChange.isCMExt_iff (c : L →ₐ[F] L)).2 ⟨inferInstance, rfl⟩) (x := x) (congrArg Units.val hx)
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact x.ne_zero (by rw [← ht, map_zero])
      exact ⟨diagUnits F (Units.mk0 t ht0),
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele F L _).trans (congrArg (diagUnits L) (Units.ext ht)), hd _⟩)
    (fun x hx => hnu _ hx (hnorm x))
    (fun x hx => div_eq_one.1 (eq_one_of_mem_lev L hl3 _ hx (hnorm x))) hMu
  have hV : ∀ u ∈ lev L l, ψ u = N (p u) := fun u hu => by
    rw [h4 u hu.1, h5 _ (div_mem hu (c3 l u hu)), mul_one]
    rfl
  refine ⟨ψ, ?_, h1, h3, fun z hz => ?_, k, hk, fun w x hx => ⟨fun hw => ?_, fun hw => ?_⟩⟩
  · refine continuous_of_continuousAt_one ψ ((hN.comp hp).continuousAt.congr ?_)
    filter_upwards [lev_mem_nhds L hl0] with x hx
    exact (hV x hx).symm
  · have e : ∀ w, z.val.2 w = 1 := fun w => by rw [hz]; rfl
    rw [hV z ⟨fun w => by rw [e, map_one], fun w => by rw [e, sub_self, map_zero]; exact zero_le⟩,
      p3 z fun w _ _ => e w, map_one]
  · rw [hV _ (loc_lev hw hx), p3 _ fun u hu _ => _root_.loc_ne (by rintro rfl; exact hw hu) x, map_one]
  · have hu := loc_unit hx
    rw [h4 _ hu, MonoidHom.comp_apply, p3 _ fun u _ hu' => _root_.loc_ne (by rintro rfl; exact hw hu') x, map_one, one_mul]
    exact h6 _ (div_mem hu (lev_one.1 (c3 1 _ (lev_one.2 hu))))

private theorem frob_val {L Ω B : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [CommGroup B] [TopologicalSpace B]
    [T1Space B] {art : Ideles L →* Gab L Ω} (ha : IsGlobalArtin art) {κ : G L Ω →* B} (hκ : Continuous κ)
    {w : HeightOneSpectrum (𝓞 L)} {A : ValuationSubring Ω} (hA : IsPlaceOver A w) (hu : ∀ s ∈ Ine (F := L) A, κ s = 1)
    {s : G L Ω} (hs : IsFrob A (normV w) s) {y : (w.adicCompletion L)ˣ} (hy : IsUnifAt w y) :
    liftAb κ hκ (art (localIdele L w y)) = (κ s)⁻¹ := by
  obtain ⟨x, hx, e⟩ := (ha.frob w A hA _).2 ⟨s, hs, rfl⟩
  have h1 : IsUnitAt w (y * x⁻¹) := by
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hy]
    exact mul_inv_cancel₀ (by simp)
  obtain ⟨t, ht, e'⟩ := (ha.ine w A hA _).1 ⟨_, h1, rfl⟩
  have : y = y * x⁻¹ * x := by simp
  rw [this, map_mul (localIdele L w), map_mul art, ← e', e, map_mul, liftAb_toAb, liftAb_toAb, hu t ht, one_mul, map_inv]

private theorem exists_conj {F L Ω : Type} [Field F] [Field L] [Field Ω] [Algebra F L] [Algebra F Ω] [Algebra L Ω]
    [IsScalarTower F L Ω] (h : (resG F L Ω).range.index = 2) :
    (∃ g, g ∉ (resG F L Ω).range) ∧ ∀ (g : G F Ω) (s : G L Ω), ∃ s', resG F L Ω s' = g * resG F L Ω s * g⁻¹ := by
  refine ⟨?_, fun g s => (Subgroup.normal_of_index_eq_two h).conj_mem _ ⟨s, rfl⟩ g⟩
  by_contra hc
  push Not at hc
  rw [(Subgroup.eq_top_iff' _).2 hc, Subgroup.index_top] at h
  omega

private theorem verArt_of (hR : ResOpen) (hV : VerGroup) (hC : ConjPlace) (hU : UnrAE) (hL : LocProd) (hS : FrobSplit)
    (hI : FrobInert) : VerArt := by
  intro F L Ω B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h2 art artL ha haL κ ν hκ hν hun hc
  classical
  obtain ⟨ho, hi⟩ := hR F L Ω
  rw [h2] at hi
  obtain ⟨ν', hν', hv⟩ := hV _ _ B (resG F L Ω) ho hi κ hκ
  suffices e : ν' = ν from e ▸ hv
  refine GlobalTheory.GalChar.eq_of_frob ha hν' hν ?_
  filter_upwards [hU F L, hun] with v hv1 hv2 A hA σ hσ
  obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).2 ⟨σ, hσ, rfl⟩
  obtain ⟨y, hy, hy'⟩ := hL F L v x
  obtain ⟨τ, hτ⟩ := toAb_surjective (artL (ideleMap F L (localIdele F v x)))
  have e1 := hc _ _ τ e hτ.symm
  rw [← liftAb_toAb κ hκ, hτ, hy, map_prod, map_prod, map_inv] at e1
  have hab : ∀ u : HeightOneSpectrum (𝓞 L), u ∈ aboveF (L := L) F v ↔ u.under (𝓞 F) = v := fun u =>
    Set.Finite.mem_toFinset _
  apply inv_injective
  rw [← e1]
  by_cases hm : σ ∈ (resG F L Ω).range
  · obtain ⟨s, rfl⟩ := hm
    obtain ⟨w, w', hne, hw, hAw, n1, n2⟩ := hS F L Ω h2 v A hv1 hA s hσ
    obtain ⟨⟨g, hg⟩, hcj⟩ := exists_conj hi
    obtain ⟨s', hs'⟩ := hcj g s
    have u1 := (hw w).2 (Or.inl rfl)
    have u2 := (hw w').2 (Or.inr rfl)
    obtain ⟨A', hA', hcA⟩ := hC F L Ω h2 g hg w w' A hAw hne (u2.trans u1.symm)
    have f1 : IsFrob A (normV v) s := ⟨hσ.1, hσ.2⟩
    have : aboveF (L := L) F v = {w, w'} := by
      ext u
      rw [hab, hw, Finset.mem_insert, Finset.mem_singleton]
    rw [this, Finset.prod_pair hne.symm, frob_val haL hκ hAw (hv2 w A u1 hAw) (n1 ▸ f1) (hy' hv1 hx w u1),
      frob_val haL hκ hA' (hv2 w' A' u2 hA') (n2 ▸ (hcA s s' hs').2 _ f1) (hy' hv1 hx w' u2), ← mul_inv,
      (hv g hg).1 s s' hs']
  · obtain ⟨w, hw, hAw, hf⟩ := hI F L Ω h2 v A hv1 hA σ hσ hm
    obtain ⟨t, ht⟩ : σ * σ ∈ (resG F L Ω).range := Subgroup.mul_self_mem_of_index_two hi σ
    have u1 := (hw w).2 rfl
    have : aboveF (L := L) F v = {w} := by
      ext u
      rw [hab, hw, Finset.mem_singleton]
    rw [this, Finset.prod_singleton, frob_val haL hκ hAw (hv2 w A u1 hAw) (hf t ht) (hy' hv1 hx w u1),
      (hv σ hm).2 t ht]

private theorem nat_mem_under {F L : Type} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (l : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : ((l : ℕ) : 𝓞 F) ∈ (w.under (𝓞 F)).asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  change algebraMap (𝓞 F) (𝓞 L) _ ∈ w.asIdeal ↔ _
  rw [map_natCast]

theorem UpperTheory.V.Z.Sym.Pl.lemTWM : GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.Z.Sym.Pl.LemTWM := by
  intro H F L Ω _ _ _ _ _ _ _ _ _ _ _ _ hF h2 l hl M hM Φ hT ν hν hc hr
  have hl0 : M ≠ 0 := by omega
  obtain ⟨art, ha⟩ := H F Ω
  obtain ⟨artL, haL⟩ := H L Ω
  let N : Ideles F →* (Qbar l)ˣ := (liftAb ν hν).comp art
  have hNv : ∀ a σ, art a = toAb F Ω σ → N a = ν σ := fun a σ h => by
    rw [MonoidHom.comp_apply, h, liftAb_toAb]
  obtain ⟨ψ, hψ, h1, h3, h4, k, hk, h5⟩ := ideleExt_of glue levPow kron phiPart awayTriv F L hF h2 l M hM Φ hT N
    ((continuous_liftAb ν hν).comp ha.quot.continuous)
    (fun k => by rw [MonoidHom.comp_apply, GlobalTheory.HilbertFromArtin.art_diag ha, map_one])
    (fun z hz => by
      obtain ⟨σ, hσ⟩ := toAb_surjective (art z)
      rw [hNv z σ hσ.symm]
      exact infTriv F Ω _ art ha ν hν hc z σ hz hσ.symm)
    (fun v hv x hx => by
      obtain ⟨A, hA⟩ := (exists_isPlaceOver Ω v : ∃ A : ValuationSubring Ω, IsPlaceOver A v)
      obtain ⟨σ, hσ, e⟩ := GlobalTheory.GalChar.exists_ine ha hA hx
      rw [hNv _ σ e]
      exact hr v A hA hv σ hσ)
  obtain ⟨κ, hκ, h6⟩ := descend L Ω _ artL haL ψ hψ h3 h4
  have h7 : ∀ (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω), IsPlaceOver A w → ∀ s ∈ Ine (F := L) A,
      (((M : ℕ) : 𝓞 L) ∉ w.asIdeal → κ s = 1) ∧ (w ∉ Φ → κ s ^ k = 1) := fun w A hA s hs => by
    obtain ⟨x, hx, e⟩ := GlobalTheory.GalChar.exists_unit haL hA hs
    rw [h6 _ s e]
    exact h5 w x hx
  exact ⟨κ, hκ, verArt_of resOpen verGroup conjPlace unrAE locProd frobSplit frobInert F L Ω _ h2 art artL ha haL κ ν hκ hν (by
    filter_upwards [GlobalTheory.GalChar.away_ae (E := F) M hl0] with v hv w A hw hA s hs
    exact (h7 w A hA s hs).1 fun h => hv (hw ▸ (nat_mem_under M w).2 h))
    (fun a σ τ e e' => by rw [h6 _ τ e', h1, hNv a σ e]), k, hk, h7⟩
