module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PFrameEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PDatEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.NsmulIntegIff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PThLoc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCuspTh
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSeenActs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PExtP
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTfAdm

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PTyFact
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem UpperTheory.Gal.W2.Seed.mem_cj_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (n : ℕ) (hG : UpperTheory.Gal.CertificateRingHomMap.LocComm)
    {q : ℕ} [Fact q.Prime] {w : Plc E} (hw : IsSplitAt w) (h : (q : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∈ (CertificateRingHomMap.cj w).asIdeal := by
  by_contra hn
  have hap : GlobalTheory.Cong.Apart w (CertificateRingHomMap.cj w) := UpperTheory.Gal.W2.Seed.apart_of_not_mem hn h
  obtain ⟨-, -, -, hs, hcc, -⟩ := hG E n w hw
  exact ((hG E n (CertificateRingHomMap.cj w) hs).2.1 w).1 hap |>.2 hcc.symm

theorem UpperTheory.Gal.W2.Seed.pTyFact :
    FacEq → LevSec → LevFact → AtApart → CongGrpEx → Denom → UpperTheory.Gal.W2.Seed.LocComm → UpperTheory.Gal.CertificateRingHomMap.LocComm → TyFact := by
  intro hF hS hLF hA hC hD hc hG E _ _ _ A n p _ S F x U w₀ Up V _ _ _ hOff _ r W hAux N _ _ L hw Ty hTy
  have hj : F.j = F.tr.j := F.j_tr
  have hL : ∀ w, L w = fac F.tr hc w := fun w => (hF E A n p S F hc w).2 _ (hTy.fac w)
  haveI : Fact r.Prime := ⟨hAux.prime⟩
  have hK1 : ∀ k, (∃ k', F.j k' = k ∧ F.th k' ∈ lev V.S V.Kw) ↔ k ∈ F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw)) := by
    intro k
    constructor
    · rintro ⟨k', rfl, h⟩
      rw [th_eq, CertificateRingHomMap.th_mem_lev] at h
      rw [hj]
      exact (hS E A n p S F.tr V.S _ hOff.1).1 k' h
    · intro h
      refine ⟨F.tr.sec k, by rw [hj]; exact F.tr.j_sec k, ?_⟩
      rw [th_eq, CertificateRingHomMap.th_mem_lev]
      exact h
  have hKiff : ∀ k, k ∈ Ty.K ↔ k ∈ F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw)) ∧ ∀ w ∈ W, (L w).pr k ∈ Iw n w.1 :=
    fun k => (hTy.K_iff k).trans (and_congr_left' (hK1 k))
  have hIK : ∀ w : Plc E, Iw n w ≤ GlobalTheory.LFun.KGL w (n := n) := fun w => by
    obtain ⟨K, -, -, -, -, -, -, h⟩ := hC E n 1 one_pos w
    exact h
  have hnS : ∀ w ∈ W, w.1 ∉ V.S ∧ CertificateRingHomMap.cj w.1 ∉ V.S := fun w hw' =>
    ⟨fun h => hAux.off _ h (hAux.half.above w hw'),
      fun h => hAux.off _ h (mem_cj_of_mem n hG w.2.1 (hAux.half.above w hw'))⟩
  have hAw₀ : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S → GlobalTheory.Cong.Apart w₀ w.1 := fun w h1 h2 =>
    ((hG E n w.1 w.2.1).2.1 w₀).2 ⟨fun e => h1 (e ▸ V.shape.mem), fun e => h2 (e ▸ V.shape.mem)⟩
  have hAp : ∀ w w' : Spl E p, GlobalTheory.Cong.Apart w.1 w'.1 → (L w).Apart (L w') := fun w w' h => by
    rw [hL, hL]
    exact (hA E A n p S F.tr hc w.1 w.2.1 w.2.2).2 w'.1 w'.2.1 w'.2.2 h
  have hLF' : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S →
      (L w).Fact (F.tr.lv (lev V.S (CertificateRingHomMap.levT V.Kw))) (GlobalTheory.LFun.KGL w.1 (n := n)) := fun w h1 h2 => by
    rw [hL]
    exact (hLF E A n p S F.tr hc V.S (CertificateRingHomMap.levT V.Kw) w.1 w.2.1 w.2.2 h2).2 h1
  have hTyAp : ∀ w : Spl E p, w.1 ∉ V.S → CertificateRingHomMap.cj w.1 ∉ V.S → Ty.L.Apart (L w) := fun w h1 h2 => by
    rw [hTy.L_eq]
    exact hAp ⟨w₀, hw⟩ w (hAw₀ w h1 h2)
  refine ⟨fun w hw' => ⟨⟨fun y hy => ?_, fun g hg => ((hKiff g).1 hg).2 w hw'⟩, hTyAp w (hnS w hw').1 (hnS w hw').2,
      fun w' hw'' e => hAp w w' (hAux.half.apart w hw' w' hw'' e)⟩,
    fun w h1 h2 h3 => ⟨⟨fun y hy => (hKiff _).2 ⟨(hLF' w h1 h2).1 y hy, fun u hu => ?_⟩,
      fun g hg => (hLF' w h1 h2).2 g ((hKiff g).1 hg).1⟩, hTyAp w h1 h2⟩, ?_⟩
  · refine (hKiff _).2 ⟨(hLF' w (hnS w hw').1 (hnS w hw').2).1 y (hIK w.1 hy), fun w' hw'' => ?_⟩
    by_cases e : w = w'
    · subst e
      rw [(L w).pr_loc]
      exact hy
    · rw [(hAp w' w (hAux.half.apart w' hw'' w hw' (Ne.symm e))).1 y]
      exact one_mem _
  · rw [(hAp w u (h3 u hu)).2 y]
    exact one_mem _
  · haveI : (Ty.K₀.subgroupOf Ty.K).FiniteIndex := ⟨Ty.idx⟩
    haveI : Fintype (Ty.K ⧸ Ty.K₀.subgroupOf Ty.K) := Fintype.ofFinite _
    choose c hc0 hcp hcv using fun q : Ty.K ⧸ Ty.K₀.subgroupOf Ty.K => hD p S.D S.G S.L (q.out : S.G.GAf)
    refine ⟨∏ q, c q, Finset.prod_pos fun q _ => hc0 q, Nat.Coprime.prod_left fun q _ => hcp q, fun k hk v hv => ?_⟩
    obtain ⟨q, hq⟩ : ∃ q : Ty.K ⧸ Ty.K₀.subgroupOf Ty.K, q = QuotientGroup.mk ⟨k, hk⟩ := ⟨_, rfl⟩
    have hu : (q.out : S.G.GAf)⁻¹ * k ∈ Ty.K₀ := by
      have : q.out⁻¹ * ⟨k, hk⟩ ∈ Ty.K₀.subgroupOf Ty.K := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', hq]
      simpa [Subgroup.mem_subgroupOf] using this
    have hint : Integ S.L ((q.out : S.G.GAf)⁻¹ * k) := integ_of_mem (KN_anti (one_dvd N.1) (hTy.K₀_eq ▸ hu))
    have hk' : k = (q.out : S.G.GAf) * ((q.out : S.G.GAf)⁻¹ * k) := by group
    have h1 := hcv q _ (hint v hv)
    rw [hk', map_mul, Module.End.mul_apply, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ q), mul_comm, mul_smul]
    exact nsmul_mem h1 _
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPhiEx
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pPhiEx :
    PhiTy → SeenShape → SeenActs → TyFact → TfAct → TfCen → TEig → AtApart → FacEq → JEq → UpperTheory.Gal.W2.Seed.LocComm → PhiEx := by
  intro hTy hShape hActs hFact hTfAct hTfCen hTEig hAt hFac hJ hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  obtain ⟨h0, h1, h2, -⟩ := hTy E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok
  refine ⟨fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h)), h0, h1, ?_, ?_⟩
  · intro g hg
    have := h2 g hg
    rw [th_eq F]
    exact this
  · intro g θ hs
    obtain ⟨-, hcase⟩ := hShape E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    have hA := hActs E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok g θ hs
    rcases hcase with ⟨hd, hk, rfl⟩ | ⟨w, t, z, i, B, hfree, hap, hi, hT, hz, hB, hzp, hh, hcen, -, hLf, rfl⟩
    · have h3 := (hA.2.1 hd hk).2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      rw [h3]
      funext a
      have h4 := hTfCen _ _ Ty 1 ⟨fun _ => by simp, map_one _⟩ _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      simp only [Pi.smul_apply, one_smul]
      rw [h4, mul_one]
    · obtain ⟨hLK, hLA⟩ := (hFact E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst L hw Ty hok).2.1 w
        hfree.2.1 hfree.2.2.1 hap
      have hAc := hA.2.2 _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hLK hLf hLA hcen hh
      have h3 := hAc.2.2 _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1
      have hsz : F.tr.sec (F.j (z ^ i)⁻¹) = (z ^ i)⁻¹ := by
        apply (hJ E A n p S F.tr.toAdT F.tr.μ F.tr.mu F.tr.a F.tr.j F.tr.j_mx).1
        intro u
        by_cases hu : (p : 𝓞 E) ∈ u.asIdeal
        · rw [F.tr.sec_p _ u hu]
          simp [hzp u hu]
        · exact (F.tr.j_eq _ _).1 (by rw [F.tr.j_sec, F.j_tr]) u hu
      have hsl : ∀ y, F.tr.sec ((L w).loc y) = CertificateRingHomMap.loc w.2.1 y := by
        intro y
        have hL : L w = fac F.tr hc w := (hFac E A n p S F hc w).2 _ (hok.fac w)
        rw [hL]
        exact (hAt E A n p S F.tr hc w.1 w.2.1 w.2.2).1 y
      rw [h3, hh]
      funext a
      have h4 := hTfAct _ _ _ Ty (L w) _ hLK hLA t⁻¹ (F.j (z ^ i)⁻¹) hcen _ (fun h => V.Φ (CertificateRingHomMap.th (F.tr.sec h))) h1 a
      have h5 := hTEig E n hodd.pos x U w₀ Up V w.1 w.2.1 hfree i hi t hT z hz B hB (F.tr.sec a)
      simp only [Pi.smul_apply]
      rw [h4, mul_smul, ← h5]
      congr 1
      refine finsum_congr fun y => ?_
      simp only [map_mul, hsz, hsl]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSeenShape
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem seenShape_not_both {E : Type} [Field E] [NumberField E] {u : Plc E} {a b : ℕ} (ha : a.Prime) (hb : b.Prime)
    (hne : a ≠ b) (h1 : (a : 𝓞 E) ∈ u.asIdeal) (h2 : (b : 𝓞 E) ∈ u.asIdeal) : False := by
  obtain ⟨c, d, e⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes ha hb).2 hne)
  have e' := congrArg (Int.cast : ℤ → 𝓞 E) e
  push_cast at e'
  refine u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

private theorem seenShape_nat_mem_cj {E : Type} [Field E] [NumberField E] [IsCMField E] {u : Plc E} {m : ℕ}
    (h : (m : 𝓞 E) ∈ u.asIdeal) : (m : 𝓞 E) ∈ (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal := by
  have e := (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
  rw [e, Ideal.mem_comap, map_natCast]
  exact h

theorem UpperTheory.Gal.W2.Seed.pSeenShape :
    StabKer → SiteFact → CenFacts → LevBasic → UpperTheory.Gal.CertificateRingHomMap.LocComm → SeenShape := by
  intro hSK hSF hCF hLB hc E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq₀ r W haux N hrN hstab L hw Ty hty g θ hs
  have key : ∀ k, Stab F V k → k ∈ S.L.KN r → k ∈ Ty.kerK :=
    hSK E A n p S F x U w₀ Up V hodd hsc hgen hoff hq₀ r W haux N hrN hstab L hw Ty hty
  rcases hs with ⟨hd, hst, hr, hθ⟩ | ⟨w, σ, i, B, hfree, hqr, hK, ⟨hi, hgK, ⟨hws, t, z, ht, hz, hh⟩, -⟩, hB, hθ⟩
  · refine ⟨?_, Or.inl ⟨hd, key _ hst hr, hθ⟩⟩
    rw [hd.1]
    exact fun k hk => key k (hstab k hk) (KN_anti hrN hk)
  · have hqw : ((σ.q : ℕ) : 𝓞 E) ∈ w.asIdeal := σ.atp.le (Ideal.subset_span (Set.mem_insert _ _))
    have hpp : p.Prime := Fact.out
    have hpw : (p : 𝓞 E) ∉ w.asIdeal := fun h => seenShape_not_both σ.atp.prime hpp σ.atp.ne hqw h
    let w' : Spl E p := ⟨w, hws, hpw⟩
    have hrU : ∀ u ∈ W, (r : 𝓞 E) ∈ u.1.asIdeal := haux.half.above
    have hqU : ∀ u ∈ W, ((σ.q : ℕ) : 𝓞 E) ∉ u.1.asIdeal := fun u hu h =>
      seenShape_not_both σ.atp.prime haux.prime hqr h (hrU u hu)
    have hcen := hCF E A n hodd.pos x hgen σ.q σ.atp.prime σ.good.1 w hqw z hz
    have hap1 : ∀ u ∈ W, GlobalTheory.Cong.Apart w u.1 := fun u hu => ((hc E n u.1 u.2.1).2.1 w).2
      ⟨fun e => hqU u hu (e ▸ hqw), fun e => seenShape_not_both (u := w) σ.atp.prime haux.prime hqr hqw
        (e ▸ seenShape_nat_mem_cj (hrU u hu))⟩
    have hap2 : ∀ u ∈ W, GlobalTheory.Cong.Apart u.1 w := fun u hu => ((hc E n w hws).2.1 u.1).2
      ⟨fun e => hqU u hu (e ▸ hqw), fun e => hqU u hu (e ▸ seenShape_nat_mem_cj hqw)⟩
    have hσK : σ.K₀ ≤ S.L.KN r := by
      obtain ⟨-, h2, h3, -⟩ := hLB p S.D S.G S.L
      refine h2 _ _ _ _ σ.isLev (h3 r) (Ideal.mul_le_left.trans (Ideal.span_singleton_le_span_singleton.2 ?_))
      have hd : r ∣ ordCompl[σ.q] N.1 := Nat.dvd_ordCompl_of_dvd_not_dvd hrN fun h =>
        hqr ((Nat.prime_dvd_prime_iff_eq σ.atp.prime haux.prime).1 h)
      exact Nat.cast_dvd_cast hd
    have hzi : ∀ a, (z ^ i)⁻¹ * a = a * (z ^ i)⁻¹ := fun a =>
      ((Commute.pow_left (show Commute z a from hcen.1 a) i).inv_left).eq
    have hw0 : comp w₀ z = 1 := (hz w₀).2 (hfree.2.2.2.1 w₀ V.shape.mem)
    refine ⟨?_, Or.inr ⟨w', t, z, i, B, hfree, hap1, hi, ht, hz, hB, ?_, ?_, ?_, ?_, ?_, hθ⟩⟩
    · rw [hgK]
      exact fun k hk => key k (hK k hk) (hσK hk)
    · exact fun u hu => hcen.2 u fun h => seenShape_not_both σ.atp.prime hpp σ.atp.ne h hu
    · have e : (UpperTheory.Gal.CertificateRingHomMap.loc hws t * z ^ i)⁻¹ = UpperTheory.Gal.CertificateRingHomMap.loc hws t⁻¹ * (z ^ i)⁻¹ := by
        rw [_root_.mul_inv_rev, map_inv]
        exact hzi _
      rw [hh, (hty.fac w').2 t⁻¹, ← map_inv F.j, e, map_mul]
    · refine ⟨fun a => ?_, ?_⟩
      · obtain ⟨a', rfl⟩ := F.surj a
        rw [← map_mul, ← map_mul, hzi]
      · rw [hty.L_eq]
        refine ((hty.fac ⟨w₀, hw⟩).1 (z ^ i)⁻¹).trans ?_
        show comp w₀ (z ^ i)⁻¹ = 1
        rw [map_inv, map_pow, hw0, one_pow, inv_one]
    · intro u hu
      rw [hh, (hty.fac u).1, map_mul, map_pow, UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hws (hap2 u hu),
        hcen.2 _ (hqU u hu), one_pow, one_mul]
    · rw [hgK]
      exact hSF E A n p S F x hgen N w' σ (L w') (hty.fac w')
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PCenFacts
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pCenFacts :
    Sides → CenFacts := by
  intro hS E _ _ _ A n _ x hx q hq hsp w hw z hz
  obtain ⟨-, -, -, h4, -⟩ := hS E A x hx q hq hsp w hw
  have hscal : ∀ (u : Plc E) (a : GL (Fin n) (u.adicCompletion E)), comp u z * a = a * comp u z := by
    intro u a
    by_cases h : UpperTheory.Gal.CertificateRingHomMap.SameK x (UpperTheory.Gal.CertificateRingHomMap.cj u) w
    · apply Units.ext
      rw [Units.val_mul, Units.val_mul, (hz u).1 h, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    · rw [(hz u).2 h, one_mul, mul_one]
  refine ⟨fun g => UpperTheory.Gal.CertificateRingHomMap.guf_ext ?_ fun u => ?_, fun u hu => ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_mul, map_mul, hscal]
  · refine (hz u).2 fun h => hu ?_
    have h' := h4 _ h
    have e : (UpperTheory.Gal.CertificateRingHomMap.cj u).asIdeal = _ :=
      (GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (GlobalTheory.SplitPts.conjE E) u)
    rw [e, Ideal.mem_comap, map_natCast] at h'
    exact h'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemFn
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pMemFn :
    SeenShape → SeenActs → ActsConv → TyFact → MemFn := by
  intro hSh hAc hAC hTF E _ _ _ A n p _ S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨-, hcase⟩ := hSh E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨hsupp, hdeck, hgen⟩ := hAc E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy g θ hs
  obtain ⟨tf1, tf2, -⟩ := hTF E A n p S F x U w₀ Up V h1 h2 h3 h4 h5 r W hAux N hrN hSt L hw Ty hTy
  rcases hcase with ⟨hD, hh, hθ⟩ | ⟨w, t, z, i, B, hFree, hAp, -, -, -, -, -, hinv, hCen, hWpr, hFg, -⟩
  · have hA := hdeck hD hh
    have hhK : g.h ∈ Ty.K := ((Ty.mem_kerK _).1 hh).1
    refine ⟨hA.1, ?_, Or.inl ⟨hD, hθ, ?_⟩⟩
    · intro a ha u hu
      obtain ⟨k, hk, hka⟩ := hsupp a ha
      have haK : a ∈ Ty.K := by
        have e : a = (g.h * k)⁻¹ * (g.h * k * a) := by group
        rw [e]
        exact Ty.K.mul_mem (Ty.K.inv_mem (Ty.K.mul_mem hhK hk)) hka
      exact (tf1 u hu).1.2 a haK
    · have e := (hAC _ _ Ty _ _ _ hA).1
      rwa [one_smul] at e
  · obtain ⟨hfac, hap⟩ := tf2 w hFree.2.1 hFree.2.2.1 hAp
    have hA := hgen _ (L w) _ t⁻¹ (F.j (z ^ i)⁻¹) hfac hFg hap hCen hinv
    have hpr : Ty.L.pr g.h = 1 := by
      have e := hA.2.1
      rwa [map_inv, inv_eq_one] at e
    refine ⟨hA.1, ?_, Or.inr ⟨hpr, hWpr, (hAC _ _ Ty _ _ _ hA).1⟩⟩
    intro a ha u hu
    obtain ⟨k, hk, hka⟩ := hsupp a ha
    have f := (tf1 u hu).1.2
    have e : (L u).pr (g.h * k * a) = (L u).pr k * (L u).pr a := by
      rw [map_mul, map_mul, hWpr u hu, one_mul]
    have h6 := f _ hka
    rw [e] at h6
    exact (Subgroup.mul_mem_cancel_left _ (f k hk)).1 h6
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.FinsumInvT
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.LFun (KGL satEig heckeVec IsSatVecGL)

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Plc E}

private theorem tj_eq {ϖ : w.adicCompletion E} {i : ℕ} (t : GLw n w)
    (ht : t.val = Matrix.diagonal fun k : Fin n => if (k : ℕ) < i then ϖ else 1) :
    Tj ℂ n (Ov E w) ϖ i = dosetInd ℂ (KGL w (n := n)) t := by
  unfold Tj dosetInd
  congr 1
  ext y
  rw [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
  constructor
  · rintro ⟨a, ha, b, hb, e⟩
    refine ⟨a, ha, b, hb, Units.ext ?_⟩
    rw [e, Units.val_mul, Units.val_mul, ht]
    rfl
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨a, ha, b, hb, ?_⟩
    rw [Units.val_mul, Units.val_mul, ht]
    rfl

private theorem dos_invT (t : GLw n w) (h : invT n _ t⁻¹ = t) (a : GLw n w) :
    dosetInd ℂ (KGL w (n := n)) t (invT n _ a) = dosetInd ℂ (KGL w (n := n)) t⁻¹ a := by
  have h' : invT n _ t = t⁻¹ := by
    have := congrArg (invT n _) h
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_invT'] at this
    exact this.symm
  have key : invT n _ a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) ↔
      a ∈ DoubleCoset.doubleCoset t⁻¹ (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) := by
    rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨k, hk, l, hl, e⟩
      refine ⟨_, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hk, _, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hl, ?_⟩
      have := congrArg (invT n _) e
      rwa [UpperTheory.Gal.CertificateRingHomMap.invT_invT', map_mul, map_mul, h'] at this
    · rintro ⟨k, hk, l, hl, rfl⟩
      exact ⟨_, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hk, _, UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL hl, by rw [map_mul, map_mul, h]⟩
  unfold dosetInd
  by_cases hm : a ∈ DoubleCoset.doubleCoset t⁻¹ (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n))
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (key.2 hm)]; rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (key.1 h))]

private theorem dos_mul (t a k : GLw n w) (hk : k ∈ KGL w (n := n)) :
    dosetInd ℂ (KGL w (n := n)) t (a * k) = dosetInd ℂ (KGL w (n := n)) t a := by
  have key : a * k ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) ↔
      a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n)) := by
    rw [DoubleCoset.mem_doubleCoset, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨u, hu, l, hl, e⟩
      exact ⟨u, hu, l * k⁻¹, (KGL w (n := n)).mul_mem hl ((KGL w (n := n)).inv_mem hk), by
        rw [← mul_assoc, ← e, mul_inv_cancel_right]⟩
    · rintro ⟨u, hu, l, hl, rfl⟩
      exact ⟨u, hu, l * k, (KGL w (n := n)).mul_mem hl hk, by simp only [mul_assoc]⟩
  unfold dosetInd
  by_cases hm : a ∈ DoubleCoset.doubleCoset t (KGL w (n := n) : Set (GLw n w)) (KGL w (n := n))
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (key.2 hm)]; rfl
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (key.1 h))]

private theorem finsum_invT {M : Type} [AddCommMonoid M] (F : GLw n w → M)
    (hF : ∀ a, ∀ k ∈ KGL w (n := n), F (a * k) = F a) :
    ∑ᶠ c : GLw n w ⧸ KGL w (n := n), F (invT n _ c.out) = ∑ᶠ c : GLw n w ⧸ KGL w (n := n), F c.out := by
  let f : GLw n w ⧸ KGL w (n := n) → GLw n w ⧸ KGL w (n := n) := fun c => QuotientGroup.mk (invT n _ c.out)
  have hf : Function.Involutive f := fun c => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (invT n _ c.out)
    simp only [f]
    rw [hk, map_mul, UpperTheory.Gal.CertificateRingHomMap.invT_invT', QuotientGroup.mk_mul_of_mem _ (UpperTheory.Gal.CertificateRingHomMap.invT_mem_KGL k.2),
      QuotientGroup.out_eq']
  have hshift : ∀ c, F (invT n _ c.out) = F ((Function.Involutive.toPerm f hf c).out) := fun c => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (invT n _ c.out)
    rw [Function.Involutive.coe_toPerm]
    simp only [f]
    rw [hk, hF _ _ k.2]
  rw [finsum_congr hshift]
  exact finsum_comp_equiv (Function.Involutive.toPerm f hf) (f := fun c => F c.out)

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.tEig_of_thLoc :
    UpperTheory.Gal.CertificateRingHomMap.ThLoc → TEig := by
  intro hT E _ _ _ n hn x U w₀ Up V w hw hF i hi t ht z hz B hB g
  obtain ⟨-, s2, -, s4⟩ := V.form.sat w hw hF.2.1 hF.2.2.1 B hB
  obtain ⟨ϖ, hϖ, htd⟩ := ht
  obtain ⟨hT1, hT2⟩ := hT E n
  have hcen := V.kap.cen w hF.2.2.2.1 hF.2.2.2.2 z hz
  have hpow : ∀ (j : ℕ) (G : GUf E n), V.Φ (G * z ^ j) = (((V.κ.val w : ℂˣ) : ℂ)⁻¹ ^ j) • V.Φ G := by
    intro j
    induction j with
    | zero => intro G; simp
    | succ j ih =>
      intro G
      rw [pow_succ, ← mul_assoc, hcen, ih, smul_smul, pow_succ, mul_comm]
  have hinv : invT n _ t⁻¹ = t := by
    apply Units.ext
    rw [UpperTheory.Gal.CertificateRingHomMap.invT_val, inv_inv, htd, Matrix.diagonal_transpose]
  set G' : GUf E n := UpperTheory.Gal.CertificateRingHomMap.th g * z ^ i with hG'
  let Fn : GLw n w → Module.Dual ℂ V.W.Sp := fun a => dosetInd ℂ (KGL w (n := n)) t a • V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a)
  have hFn : ∀ a, ∀ k ∈ KGL w (n := n), Fn (a * k) = Fn a := fun a k hk => by
    have h1 : V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a * UpperTheory.Gal.CertificateRingHomMap.loc hw k) = V.Φ (G' * UpperTheory.Gal.CertificateRingHomMap.loc hw a) :=
      congrFun (GlobalTheory.LGrp.mem_fixed.1 s2 k hk) _
    simp only [Fn]
    rw [UpperTheory.Gal.W2.Seed.dos_mul _ _ _ hk, map_mul, ← mul_assoc, h1]
  have hterm : ∀ c : GLw n w ⧸ KGL w (n := n), dosetInd ℂ (KGL w (n := n)) t⁻¹ c.out •
      V.Φ (UpperTheory.Gal.CertificateRingHomMap.th (g * (z ^ i)⁻¹ * UpperTheory.Gal.CertificateRingHomMap.loc hw c.out)) = Fn (invT n _ c.out) := fun c => by
    simp only [Fn]
    rw [UpperTheory.Gal.W2.Seed.dos_invT t hinv, map_mul, map_mul, hT1, map_inv, map_pow, hT2 hn x w z hz, inv_pow, inv_inv]
  have hev := congrFun (s4 ϖ hϖ i hi) G'
  unfold heckeVec at hev
  rw [finsum_apply (GlobalTheory.LFun.finite_heckeVec (Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke hϖ i) _ V.Φ),
    UpperTheory.Gal.W2.Seed.tj_eq t htd] at hev
  rw [finsum_congr hterm, UpperTheory.Gal.W2.Seed.finsum_invT Fn hFn]
  refine Eq.trans hev ?_
  rw [Pi.smul_apply, hG', hpow, smul_smul]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStabKer
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.W2.Seed.pStabKer :
    FacEq → KNFact → CongGrpEx → StabKer := by
  intro _ hKN hCG E _ _ _ A n p _ S F x U w₀ Up V _ _ _ _ _ r W haux N _ _ L hw Ty hTy k hk hkr
  obtain ⟨k', hk', hlev, hJ, hχ⟩ := hk
  have hK : k ∈ Ty.K := by
    refine (hTy.K_iff k).2 ⟨⟨k', hk', hlev⟩, fun w hwW => ?_⟩
    have hr : (r : 𝓞 E) ∈ w.1.asIdeal := haux.half.above w hwW
    obtain ⟨K, hK, -, -, -, -, hIw, -⟩ := hCG E n r haux.prime.pos w.1
    have hf := hKN E A n p S F w (L w) (hTy.fac w) r haux.prime haux.good hr r haux.prime.pos K hK
    exact hIw hr (hf.2 k hkr)
  refine (Ty.mem_kerK k).2 ⟨hK, ?_⟩
  have hpr : Ty.L.pr k = comp w₀ k' := by
    rw [hTy.L_eq, ← hk']
    exact (hTy.fac ⟨w₀, hw⟩).1 k'
  refine (hTy.ψ_eq _ ⟨comp w₀ (F.th k'), hJ⟩ ?_).trans hχ
  simp only [hpr, th_eq F, CertificateRingHomMap.comp_th, CertificateRingHomMap.invT_val]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PActsConv
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp lev GLw IsCen mat sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Spc
open scoped TensorProduct Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem conv_eq_hAct {X : Type} [Group X] (K : Subgroup X) (f f' : X → ℂ) (g : X) :
    conv K f f' g = hAct K f (fun x => f' (x⁻¹ * g)) 1 := by
  simp only [conv, hAct, one_mul, smul_eq_mul]

private theorem conv_tf {X M : Type} [Group X] [Group M] (hA : TfAdm) (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h h' : X)
    (hψ : T.Acts ψ c h) (hh' : T.L.pr h' = 1) :
    conv T.K₀ ψ (T.tf h') = c • conv T.K₀ (T.tf h) (T.tf h') := by
  funext g
  have hΦ : T.IsTy (fun x => T.tf h' (x⁻¹ * g)) := by
    intro k hk x
    have hk' : k⁻¹ ∈ T.K := T.K.inv_mem hk
    simp only [_root_.mul_inv_rev, mul_assoc]
    rw [((hA X M T h' hh').2 k⁻¹ hk' (x⁻¹ * g)).1, smul_eq_mul]
    congr 1
    have e : ∀ (p1 : T.L.pr k⁻¹ ∈ T.J) (p2 : T.L.pr k ∈ T.J),
        (⟨T.L.pr k⁻¹, p1⟩ : T.J) = (⟨T.L.pr k, p2⟩ : T.J)⁻¹ := fun p1 p2 =>
      Subtype.ext (map_inv _ _)
    rw [e _ (T.fact.2 k hk)]
    simp
  have key := congrFun (hψ.2.2 ℂ _ hΦ) 1
  rw [Pi.smul_apply, conv_eq_hAct, conv_eq_hAct, key, Pi.smul_apply]

theorem UpperTheory.Gal.W2.Seed.pActsConv :
    TfAdm → TfIdem → ActsConv := by
  intro hA hI X M _ _ T ψ c h hψ
  constructor
  · rw [conv_tf hA T ψ c h 1 hψ (map_one _), (hI X M T h hψ.2.1).2.1]
  · intro c' h' hh'
    have hlin : ∀ f : X → ℂ, conv T.K₀ ψ (c' • f) = c' • conv T.K₀ ψ f := by
      intro f
      funext g
      rw [Pi.smul_apply]
      unfold conv
      rw [smul_finsum]
      congr 1
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hlin, conv_tf hA T ψ c h h' hψ hh', smul_smul, mul_comm c' c]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemSum
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private lemma memSum_cls {X : Type} [Group X] {K KM K₀ : Subgroup X} {h : X}
    (hc : ∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ K₀) (k₁ k₂ : K)
    (e : (QuotientGroup.mk k₁ : K ⧸ KM.subgroupOf K) = QuotientGroup.mk k₂) (y : X) :
    h * (k₁ : X) * y ∈ K₀ ↔ h * (k₂ : X) * y ∈ K₀ := by
  have hu : k₁⁻¹ * k₂ ∈ KM.subgroupOf K := QuotientGroup.eq.1 e
  have hu' : (k₁ : X)⁻¹ * k₂ ∈ KM := by simpa [Subgroup.mem_subgroupOf] using hu
  have hm := hc k₁ k₁.2 _ hu'
  have e2 : h * (k₂ : X) * y = (h * k₁ * ((k₁ : X)⁻¹ * k₂) * (h * k₁)⁻¹) * (h * k₁ * y) := by group
  rw [e2]
  exact (K₀.mul_mem_cancel_left hm).symm

private lemma memSum_eq {X : Type} [Group X] (K KM K₀ : Subgroup X) (h y : X)
    [Fintype (K ⧸ KM.subgroupOf K)] :
    memFn K KM K₀ h y =
      ∑ q : K ⧸ KM.subgroupOf K, if h * (q.out : X) * y ∈ K₀ then (1 : ℂ) else 0 := by
  unfold memFn
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [Finset.sum_boole]

theorem UpperTheory.Gal.W2.Seed.pMemSum :
    MemSum := by
  intro X _ K KM K₀ h hK0 hidx hnorm hc
  haveI : (KM.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  haveI : (KM.subgroupOf K).FiniteIndex := ⟨hidx⟩
  letI : Fintype (K ⧸ KM.subgroupOf K) := Fintype.ofFinite _
  have hex : ∀ y, memFn K KM K₀ h y ≠ 0 →
      ∃ q : K ⧸ KM.subgroupOf K, h * (q.out : X) * y ∈ K₀ := by
    intro y hy
    by_contra hne
    apply hy
    have : IsEmpty {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * y ∈ K₀} :=
      ⟨fun ⟨q, hq⟩ => hne ⟨q, hq⟩⟩
    unfold memFn
    rw [Nat.card_of_isEmpty, Nat.cast_zero]
  have hP : ∀ (a : K) (q : K ⧸ KM.subgroupOf K) (y : X),
      h * (q.out : X) * ((a : X) * y) ∈ K₀ ↔
        h * ((q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out : X) * y ∈ K₀ := by
    intro a q y
    have e : (QuotientGroup.mk (q.out * a) : K ⧸ KM.subgroupOf K) =
        QuotientGroup.mk (q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have hcls := memSum_cls hc (q.out * a) (q * (QuotientGroup.mk a : K ⧸ KM.subgroupOf K)).out e y
    have e2 : h * (q.out : X) * ((a : X) * y) = h * ((q.out * a : K) : X) * y := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e2]
    exact hcls
  refine ⟨?_, ?_, ?_⟩
  · show IsBiInv K₀ (memFn K KM K₀ h) ∧ FinDosetSupp K₀ (memFn K KM K₀ h)
    refine ⟨?_, ?_⟩
    · intro a b g
      unfold memFn
      congr 1
      apply Nat.card_congr
      refine (Equiv.mulRight (QuotientGroup.mk (⟨a, hK0 a.2⟩ : K) : K ⧸ KM.subgroupOf K)).subtypeEquiv ?_
      intro q
      have e1 : h * (q.out : X) * ((a : X) * g * (b : X)) =
          h * (q.out : X) * (((⟨a, hK0 a.2⟩ : K) : X) * g) * (b : X) := by
        rw [← mul_assoc (h * (q.out : X))] <;> rfl
      rw [e1, Subgroup.mul_mem_cancel_right _ b.2]
      exact hP ⟨a, hK0 a.2⟩ q g
    · refine ⟨Finset.univ.image (fun q : K ⧸ KM.subgroupOf K => (h * (q.out : X))⁻¹), fun y hy => ?_⟩
      obtain ⟨q, hq⟩ := hex y hy
      refine ⟨(h * (q.out : X))⁻¹, Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, 1, ⟨_, hq⟩, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      group
  · intro y hy
    obtain ⟨q, hq⟩ := hex y hy
    exact ⟨_, (q.out).2, hq⟩
  · intro V _ _ Φ hΦ g
    unfold hAct
    have hpt : ∀ x : X ⧸ K₀, memFn K KM K₀ h x.out • Φ (g * x.out) =
        ∑ q : K ⧸ KM.subgroupOf K,
          (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) := by
      intro x
      rw [memSum_eq, Finset.sum_smul]
      refine Finset.sum_congr rfl fun q _ => ?_
      have hiff : (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀) = x ↔ h * (q.out : X) * x.out ∈ K₀ := by
        conv_lhs => rw [← QuotientGroup.out_eq' x]
        rw [QuotientGroup.eq, inv_inv]
      by_cases hm : h * (q.out : X) * x.out ∈ K₀
      · rw [if_pos hm, if_pos (hiff.mpr hm), one_smul]
        have hg : g * x.out = g * (h * (q.out : X))⁻¹ * (h * (q.out : X) * x.out) := by group
        rw [hg]
        exact hΦ _ hm _
      · rw [if_neg hm, if_neg (fun e => hm (hiff.mp e)), zero_smul]
    rw [finsum_eq_sum_of_fintype (fun k : K ⧸ KM.subgroupOf K => Φ (g * (h * (k.out : X))⁻¹)),
      finsum_congr hpt, finsum_sum_comm]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [finsum_eq_single _ (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀)]
      · simp
      · intro x hx
        rw [if_neg (Ne.symm hx)]
    · intro q _
      apply Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K₀))
      intro x hx
      by_contra hne
      exact hx (if_neg (Ne.symm hne))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLevFact
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem apart_or {E : Type} [Field E] [NumberField E] [IsCMField E] (u w : Plc E) :
    GlobalTheory.Cong.Apart u w ∨ u = w ∨ u = UpperTheory.Gal.CertificateRingHomMap.cj w := by
  by_cases h : GlobalTheory.Cong.Apart u w
  · exact Or.inl h
  · exact Or.inr (GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc (not_not.1 h))

private theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Plc E) :
    UpperTheory.Gal.CertificateRingHomMap.cj (UpperTheory.Gal.CertificateRingHomMap.cj w) = w := GlobalTheory.CompanionTheory.OnlyStab.conjSrc_invol w

theorem UpperTheory.Gal.W2.Seed.pLevFact :
    AtApart → IntConj → LevFact := by
  intro hA hI E _ _ _ A n p _ S T hc S₀ Kw w hw hp hcj
  have hsec : ∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x := (hA E A n p S T hc w hw hp).1
  have hn : 0 < n := S.facts.pos
  refine ⟨fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩, fun hwS => ⟨fun x hx => ?_, fun g hg => ?_⟩⟩
  · show T.sec _ ∈ lev S₀ Kw
    rw [hsec, CertificateRingHomMap.mem_lev]
    refine ⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; rw [CertificateRingHomMap.comp_loc]; exact hx
      · subst h; exact absurd hu hcj
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; exact absurd hwS hu
      · subst h; exact absurd (by rwa [cj_cj]) hcu
  · exact (CertificateRingHomMap.mem_lev.1 hg).2.1 w hwS
  · show T.sec _ ∈ lev S₀ Kw
    rw [hsec, CertificateRingHomMap.mem_lev]
    refine ⟨by rw [CertificateRingHomMap.sim_loc]; exact one_mem _, fun u hu => ?_, fun u hu hcu => ?_⟩
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; exact absurd hu hwS
      · subst h; exact absurd hu hcj
    · rcases apart_or u w with h | h | h
      · rw [CertificateRingHomMap.comp_loc_of_apart hw h]; exact one_mem _
      · subst h; rw [CertificateRingHomMap.comp_loc]; exact hx
      · subst h
        refine (hI E n (CertificateRingHomMap.loc hw x) w hn).1 ?_ ?_
        · rw [CertificateRingHomMap.sim_loc]; exact one_mem _
        · rw [CertificateRingHomMap.comp_loc]; exact hx
  · exact (CertificateRingHomMap.mem_lev.1 hg).2.2 w hwS hcj
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSumDoset
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

private theorem card_fibre {G : Type} [Group G] (N P : Subgroup G) [N.Normal] (hNP : N ≤ P) (w : G) :
    Nat.card {q : G ⧸ N // (q.out : G) * w⁻¹ ∈ P} = N.relIndex P := by
  have hk := Subgroup.relIndex_ker P (QuotientGroup.mk' N)
  rw [QuotientGroup.ker_mk'] at hk
  rw [hk]
  apply Nat.card_congr
  refine (Equiv.mulRight (QuotientGroup.mk w⁻¹ : G ⧸ N)).subtypeEquiv ?_
  intro q
  rw [Equiv.coe_mulRight, Subgroup.mem_map]
  beta_reduce
  have hq : q * (QuotientGroup.mk w⁻¹ : G ⧸ N) = QuotientGroup.mk ((q.out : G) * w⁻¹) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  rw [hq]
  constructor
  · intro hp
    exact ⟨_, hp, rfl⟩
  · rintro ⟨p, hp, e⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at e
    have hm := P.mul_mem hp (hNP e)
    simpa using hm

theorem UpperTheory.Gal.W2.Seed.pSumDoset :
    SumDoset := by
  intro X _ K KM h hKM hidx hhK V _ _ Φ hΦ hnorm g
  obtain ⟨L, hL⟩ : ∃ L : Subgroup X, L = K ⊓ Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj h)) K :=
    ⟨_, rfl⟩
  rw [← hL]
  haveI : (KM.subgroupOf K).Normal := ⟨fun n hn k => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm k k.2 n hn⟩
  haveI : (KM.subgroupOf K).FiniteIndex := ⟨hidx⟩
  letI : Fintype (K ⧸ KM.subgroupOf K) := Fintype.ofFinite _
  have hLK : L ≤ K := by
    rw [hL]
    exact inf_le_left
  have hKML : KM ≤ L := by
    intro u hu
    rw [hL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact ⟨hKM hu, hhK u hu⟩
  have hmemL : ∀ k : K, k ∈ L.subgroupOf K ↔ h * (k : X) * h⁻¹ ∈ K := by
    intro k
    rw [Subgroup.mem_subgroupOf, hL, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    exact ⟨fun hh => hh.2, fun hh => ⟨k.2, hh⟩⟩
  have hNP : KM.subgroupOf K ≤ L.subgroupOf K := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKML hk
  have hcard : ∀ y : X, y ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K →
      Nat.card {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * y ∈ K} = KM.relIndex L := by
    intro y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hy
    rw [← Subgroup.relIndex_subgroupOf hLK,
      ← card_fibre (KM.subgroupOf K) (L.subgroupOf K) hNP (⟨a, ha⟩ : K)⁻¹]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro q
    rw [inv_inv, hmemL]
    have e : h * (q.out : X) * (a * h⁻¹ * b) = h * ((q.out * ⟨a, ha⟩ : K) : X) * h⁻¹ * b := by
      simp only [Subgroup.coe_mul, mul_assoc]
    rw [e, Subgroup.mul_mem_cancel_right _ hb]
  have hnot : ∀ y : X, y ∉ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K →
      ∀ q : K ⧸ KM.subgroupOf K, h * (q.out : X) * y ∉ K := by
    intro y hy q hq
    apply hy
    rw [DoubleCoset.mem_doubleCoset]
    exact ⟨((q.out : K) : X)⁻¹, K.inv_mem q.out.2, h * (q.out : X) * y, hq, by group⟩
  have hpt : ∀ x : X ⧸ K, ((KM.relIndex L : ℕ) : ℂ) •
      ((DoubleCoset.doubleCoset h⁻¹ (K : Set X) K).indicator (1 : X → ℂ) x.out • Φ (g * x.out)) =
      ∑ q : K ⧸ KM.subgroupOf K,
        (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) := by
    intro x
    have hterm : ∀ q : K ⧸ KM.subgroupOf K,
        (if (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x then Φ (g * (h * (q.out : X))⁻¹) else 0) =
          if h * (q.out : X) * x.out ∈ K then Φ (g * x.out) else 0 := by
      intro q
      have hiff : (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K) = x ↔ h * (q.out : X) * x.out ∈ K := by
        conv_lhs => rw [← QuotientGroup.out_eq' x]
        rw [QuotientGroup.eq, inv_inv]
      by_cases hm : h * (q.out : X) * x.out ∈ K
      · rw [if_pos hm, if_pos (hiff.mpr hm)]
        have hg : g * x.out = g * (h * (q.out : X))⁻¹ * (h * (q.out : X) * x.out) := by group
        rw [hg, hΦ _ hm]
      · rw [if_neg hm, if_neg (fun e => hm (hiff.mp e))]
    rw [Finset.sum_congr rfl (fun q _ => hterm q), ← Finset.sum_filter, Finset.sum_const,
      ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    by_cases hy : x.out ∈ DoubleCoset.doubleCoset h⁻¹ (K : Set X) K
    · rw [Set.indicator_of_mem hy, Pi.one_apply, one_smul, hcard _ hy, Nat.cast_smul_eq_nsmul ℂ]
    · have : IsEmpty {q : K ⧸ KM.subgroupOf K // h * (q.out : X) * x.out ∈ K} :=
        ⟨fun ⟨q, hq⟩ => hnot _ hy q hq⟩
      rw [Set.indicator_of_notMem hy, zero_smul, smul_zero, Nat.card_of_isEmpty, zero_smul]
  unfold hAct dosetInd
  rw [smul_finsum, finsum_eq_sum_of_fintype (fun k : K ⧸ KM.subgroupOf K => Φ (g * (h * (k.out : X))⁻¹)),
    finsum_congr hpt, finsum_sum_comm]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [finsum_eq_single _ (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K)]
    · simp
    · intro x hx
      rw [if_neg (Ne.symm hx)]
  · intro q _
    apply Set.Finite.subset (Set.finite_singleton (QuotientGroup.mk (h * (q.out : X))⁻¹ : X ⧸ K))
    intro x hx
    by_contra hne
    exact hx (if_neg (Ne.symm hne))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemDeck
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pMemDeck :
    MemSum → TfCen → MemDeck := by
  intro hSum hCen X M _ _ T K hT k hk hnorm
  have hconj : ∀ a ∈ T.K₀, ∀ u ∈ T.K₀, a * u * a⁻¹ ∈ T.K₀ := fun a ha u hu =>
    T.K₀.mul_mem (T.K₀.mul_mem ha hu) (T.K₀.inv_mem ha)
  have hmem := hSum X T.K₀ T.K₀ T.K₀ k le_rfl (by simp) hconj (fun a ha u hu => by
    have h1 := hnorm (a * u * a⁻¹) (hconj a ha u hu)
    simpa [mul_assoc, _root_.mul_inv_rev] using h1)
  refine ⟨hmem.1, map_one _, ?_⟩
  intro V _ _ Φ hΦ
  funext g
  have hc : T.Cen 1 := ⟨fun g => by simp, map_one _⟩
  rw [one_smul, hCen X M T 1 hc V Φ hΦ g, mul_one]
  have hinv0 : ∀ k' ∈ T.K₀, ∀ g, Φ (g * k') = Φ g := fun k' hk' g => by
    rw [hΦ k' (T.le hk') g, T.ker k' hk' _]
    simp
  rw [hmem.2.2 V Φ hinv0 g]
  have hall : ∀ a b : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀, a = b := by
    intro a b
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact SetLike.coe_mem _
  letI : Unique (↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀) :=
    ⟨⟨QuotientGroup.mk (1 : ↥T.K₀)⟩, fun a => hall a _⟩
  rw [finsum_unique]
  have hx : (↑(Quotient.out (default : ↥T.K₀ ⧸ T.K₀.subgroupOf T.K₀)) : X) ∈ T.K₀ :=
    SetLike.coe_mem _
  rw [_root_.mul_inv_rev, ← mul_assoc, hΦ k⁻¹ (hT.1 (K.inv_mem hk)) _,
    hT.2 k⁻¹ (K.inv_mem hk) _]
  simp only [Units.val_one, one_smul]
  exact hinv0 _ (T.K₀.inv_mem hx) g
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMemAct
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

theorem UpperTheory.Gal.W2.Seed.pMemAct :
    MemSum → SumDoset → TfAct → (∀ (X M' : Type) [Group X] [Group M'] (L' : Loc X M') (K : Subgroup X) (Kw : Subgroup M'), L'.Fact K Kw → ∀ (t : M') (V : Type) [AddCommGroup V] [Module ℂ V] (Ψ : X → V), (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Ψ y.out = ∑ᶠ x : M' ⧸ Kw, dosetInd ℂ Kw t x.out • Ψ (L'.loc x.out)) → MemAct := by
  intro hMS hSD hTF hS X M M' _ _ _ T L' Kw hfT hap K KM htr hfK hK0 hKM hidx hnor t z h hz hh hc
  have hKMK : KM ≤ K := hKM.trans hK0
  have hcK : ∀ u ∈ KM, h * u * h⁻¹ ∈ K := fun u hu => hK0 (by simpa using hc 1 K.one_mem u hu)
  obtain ⟨hmem, -, hsum⟩ := hMS X K KM T.K₀ h hK0 hidx hnor hc
  refine ⟨hmem, ?_, ?_⟩
  · rw [map_mul, hap.1 t, hz.2, one_mul]
  · intro V _ _ Φ hΦ
    have hΦK : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g := by
      intro k hk g
      rw [hΦ k (htr.1 hk) g, htr.2 k hk, Units.val_one, one_smul]
    have hΦ0 : ∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g := fun k hk g => hΦK k (hK0 hk) g
    funext g
    rw [Pi.smul_apply, hsum V Φ hΦ0 g, hSD X K KM h hKMK hidx hcK V Φ hΦK hnor g,
      hTF X M M' T L' Kw hfT hap t z hz V Φ hΦ g]
    congr 1
    refine Eq.trans ?_ (hS X M' L' K Kw hfK t V (fun y => Φ (g * z * y)) ?_)
    · show ∑ᶠ x : X ⧸ K, dosetInd ℂ K h⁻¹ x.out • Φ (g * x.out) =
        ∑ᶠ y : X ⧸ K, dosetInd ℂ K (L'.loc t) y.out • Φ (g * z * y.out)
      rw [hh, ← finsum_comp_equiv (MulAction.toPerm z : Equiv.Perm (X ⧸ K))]
      refine finsum_congr fun q => ?_
      have hzq : (MulAction.toPerm z q : X ⧸ K) = ((z * q.out : X) : X ⧸ K) := by
        rw [MulAction.toPerm_apply]
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rw [MulAction.Quotient.smul_mk, smul_eq_mul]
      obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (z * q.out)
      have e1 : Φ (g * (z * q.out * k)) = Φ (g * z * q.out) := by
        rw [← mul_assoc, hΦK _ k.2, ← mul_assoc]
      have hmem2 : z * q.out * k ∈ DoubleCoset.doubleCoset (L'.loc t * z) (K : Set X) K ↔
          q.out ∈ DoubleCoset.doubleCoset (L'.loc t) (K : Set X) K := by
        simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
        constructor
        · rintro ⟨a, ha, b, hb, e⟩
          refine ⟨a, ha, b * (k : X)⁻¹, K.mul_mem hb (K.inv_mem k.2), ?_⟩
          have hw : a * (L'.loc t * z) * b = z * (a * L'.loc t * b) := by
            rw [← mul_assoc a, ← hz.1, mul_assoc z]
          calc q.out = z⁻¹ * (z * q.out * k) * (k : X)⁻¹ := by group
            _ = z⁻¹ * (z * (a * L'.loc t * b)) * (k : X)⁻¹ := by rw [e, hw]
            _ = a * L'.loc t * (b * (k : X)⁻¹) := by group
        · rintro ⟨a, ha, b, hb, e⟩
          refine ⟨a, ha, b * k, K.mul_mem hb k.2, ?_⟩
          rw [e, ← mul_assoc a, ← hz.1]
          group
      have e2 : dosetInd ℂ K (L'.loc t * z) (z * q.out * k) = dosetInd ℂ K (L'.loc t) q.out := by
        unfold dosetInd
        simp only [Set.indicator_apply, hmem2, Pi.one_apply]
      rw [hzq, hk, e1, e2]
    · intro k hk y
      show Φ (g * z * (y * k)) = Φ (g * z * y)
      rw [← mul_assoc]
      exact hΦK k hk _
end

namespace UpperTheory.Gal.W2.Seed

open UpperTheory.Gal.Int.Geo.Pl (dict_holds sides_holds levBasic_holds)
open UpperTheory.Gal.CertificateRingHomMap (pLocComm_of pThLoc_of)

theorem tfCen_holds : TfCen := pTfCen pAvgK pTfAdm
theorem tfAct_holds : TfAct := pTfAct pAvgK pDosetCosets pTfAdm
theorem tfIdem_holds : TfIdem := pTfIdem pTfAdm tfCen_holds
theorem tfMulL_holds : TfMulL := pTfMulL pTfAdm tfAct_holds pDosetIff
theorem tfMulR_holds : TfMulR := pTfMulR pAvgK pTfAdm pDosetIff
theorem tfLoc_holds : TfLoc := pTfLoc pTfAdm tfAct_holds pDosetIff
theorem knIff_holds : KNIff := pKNIff latCoord_holds
theorem atApart_holds : AtApart := pAtApart pJEq
theorem levFact_holds : LevFact := pLevFact atApart_holds pIntConj
theorem knIdx_holds : KNIdx := pKNIdx (pKNOpen knIff_holds)
theorem pPart_holds : PPart := pPPart pJEq
theorem memAct_holds : MemAct := pMemAct pMemSum pSumDoset tfAct_holds pDosetCosets
theorem memDeck_holds : MemDeck := pMemDeck pMemSum tfCen_holds
theorem levSec_holds : LevSec := pLevSec pIntConj
theorem knFact_holds : KNFact :=
  pKNFact knIff_holds pFacEq atApart_holds pCongGrpEx (pCongConj pLocComm_of) pLocComm pLocComm_of
theorem siteFact_holds : SiteFact := pSiteFact dict_holds sides_holds pIntConj pLocComm_of
theorem stabKer_holds : StabKer := pStabKer pFacEq knFact_holds pCongGrpEx
theorem seenShape_holds : SeenShape := pSeenShape stabKer_holds siteFact_holds (pCenFacts sides_holds) levBasic_holds pLocComm_of
theorem seenActs_holds : SeenActs := pSeenActs pMemSum memAct_holds memDeck_holds seenShape_holds levBasic_holds knIdx_holds
theorem actsConv_holds : ActsConv := pActsConv pTfAdm tfIdem_holds
theorem phiTy_holds : PhiTy := pPhiTy pPart_holds levSec_holds pFacEq pLocComm

theorem tyFact_holds : Spc.TyFact :=
  pTyFact pFacEq levSec_holds levFact_holds atApart_holds pCongGrpEx pDenom pLocComm pLocComm_of
theorem memFn_holds : Spc.MemFn := pMemFn seenShape_holds seenActs_holds actsConv_holds tyFact_holds
theorem phiEx_holds : Spc.PhiEx :=
  pPhiEx phiTy_holds seenShape_holds seenActs_holds tyFact_holds tfAct_holds tfCen_holds (tEig_of_thLoc (pThLoc_of pLocComm_of CertificateRingHomMap.pOfUBij_of)) atApart_holds pFacEq pJEq
    pLocComm

end UpperTheory.Gal.W2.Seed
