module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OffOfNotMem
noncomputable section

namespace GlobalTheory.LvT.Built.SplitPts

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

theorem exists_ufGL {E : Type} [Field E] [StarRing E] {n : ℕ} (γ : GL (Fin n) E)
    (h : (γ : Matrix (Fin n) (Fin n) E)ᴴ * (γ : Matrix (Fin n) (Fin n) E) = 1) : ∃ g : UF E n, ufGL E n g = γ := by
  obtain ⟨e, rfl⟩ := (toGLm E n).surjective γ
  refine ⟨⟨e, fun x y => ?_⟩, rfl⟩
  rw [← toGLm_mulVec e x, ← toGLm_mulVec e y]
  show star ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ x) ⬝ᵥ ((toGLm E n e : Matrix (Fin n) (Fin n) E) *ᵥ y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_one]

theorem sameOff_gmap {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 E))}
    {N N' : Submodule (𝓞 E) (Sp E n)} (g : Sp E n ≃ₗ[E] Sp E n) (h : SameOff ST N N') :
    SameOff ST (gmap g N) (gmap g N') := fun w hw => by
  ext x
  rw [mem_localization_gmap, mem_localization_gmap, h w hw]

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

variable (sel) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (u : Pr.Word) (i : ℕ)

def offSetoid : Setoid (PtAt R sel mu cst u i) where
  r := SameOffPt sel mu cst u
  iseqv :=
    ⟨fun _ => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩,
      fun h => ⟨fun w hw => (h.1 w hw).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩,
      fun h h' => ⟨fun w hw => (h.1 w hw).trans (h'.1 w hw), h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1,
        h.2.2.2.trans h'.2.2.2⟩⟩

theorem off_of_notMem (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (h : (Pr.T u : 𝓞 X.E) ∉ w.asIdeal) :
    ∀ P ∈ Pr.vT u, w ≠ P ∧ w ≠ conjPrime₂ P := fun P hP => ne_of_T_notMem hPr u ⟨P, hP⟩ h

theorem ys_congr (hPr : Pr.Ok) (hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal)
    {N N' : Submodule (𝓞 X.E) (Sp X.E (R.N i))} (h : SameOff (Pr.vT u) N N') :
    (ysAt R sel mu cst i).ys N' = (ysAt R sel mu cst i).ys N := by
  classical
  have h1 : ∀ w : rowSG Pr sel mu, localization₂ w.1.asIdeal N' = localization₂ w.1.asIdeal N := fun w =>
    (h w.1 (off_of_notMem u hPr
      ((Finset.mem_union.1 w.2).elim (fun h => T_notMem_vGs hPr u ⟨w.1, h⟩) (hQ w.1)))).symm
  unfold ysAt
  split_ifs
  · show ybSet sel mu cst N' = ybSet sel mu cst N
    simp only [ybSet, locLat, h1]
  · rfl

theorem exists_split : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K)), ∃ sp : Split (tdatAt sel mu cst L Tp u i) (Pr.T u), ∀ b p q, (sp.off b).r p q ↔ SameOffPt sel mu cst u p q := by
  intro X Pr R _ Ch sel S mu cst L G m2 u i hX hPr hs hT _ Tp
  classical
  have hQ : ∀ w ∈ QE sel (mu : Chr X.F X.E X.K), (Pr.T u : 𝓞 X.E) ∉ w.asIdeal :=
    fun w hw => notMem_QE hs mu hw (hPr.T_prime u) hT
  have hM := moveHyp_of_ok hPr u
  have hQ' : ∀ (P : Pr.vT u) (w : QE sel (mu : Chr X.F X.E X.K)), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun P w => ne_of_T_notMem hPr u P (hQ w.1 w.2)
  have hy := ysAt_off (R := R) sel mu cst hPr u hQ i
  refine ⟨{ off := fun _ => offSetoid sel mu cst u i
            off_act := ?_
            off_lat := fun _ _ _ h => h.1
            ext := ?_
            surj := ?_
            off_up := ?_
            off_dn := ?_
            off_dia := ?_
            dia_deco := ?_
            gam_surj := ?_
            T_mem := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).1
            T_nsq := fun P hP => (T_unif hX hPr u ⟨P, hP⟩).2
            nonconj := fun P hP Q hQ => (hM ⟨P, hP⟩).st ⟨Q, hQ⟩ }, fun _ _ _ => Iff.rfl⟩
  · rintro b g p q ⟨h1, h2, h3, h4⟩
    refine ⟨sameOff_gmap g.1.1 h1, ?_, ?_, ?_⟩
    · funext w x
      show (g.2.1.1 w).1.mulVec (p.1.1.deco.1.be w (g.1.1.symm x)) = (g.2.1.1 w).1.mulVec (q.1.1.deco.1.be w (g.1.1.symm x))
      rw [h2]
    · funext w
      show g.1.1 * p.1.1.fr w * ((g.2.2.1 w)⁻¹).1 = g.1.1 * q.1.1.fr w * ((g.2.2.1 w)⁻¹).1
      rw [h3]
    · show (fun v => g.1.1 v) '' p.1.2 = (fun v => g.1.1 v) '' q.1.2
      rw [h4]
  · rintro b p q ⟨-, h2, h3, h4⟩ h
    have hN := congrArg Deco.N h
    have hf := congrArg Deco.f h
    exact PtY.ext' (Subtype.ext (Deco.ext hN hf h2)) h3 h4
  · intro b p e he h
    have hok := GlobalTheory.LvT.Pts.ok_of_agree p.1.1.deco.2 he
      fun w => h w.1 (off_of_notMem u hPr (T_notMem_vGs hPr u w))
    have hm := PtY.mv_spec p ⟨_, hok⟩ (fun w => (h w.1 (off_of_notMem u hPr (hQ w.1 w.2))).symm)
      (ys_congr sel mu cst u i hPr hQ h)
    have e1 := congrArg Subtype.val hm.1
    refine ⟨PtY.mv p ⟨_, hok⟩, ⟨?_, (congrArg Deco.be e1).symm, hm.2.1.symm, hm.2.2.symm⟩, ?_⟩
    · rw [e1]; exact h
    · have hN := congrArg Deco.N e1
      have hf := congrArg Deco.f e1
      exact Deco.ext hN hf (funext fun w => absurd w.2 (Finset.notMem_empty _))
  · intro b p P x hx hf
    have hm := mv_up (Pr.T u) p P (hM P) (T_unif hX hPr u P) (hQ' P) (hy P) hx hf
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((upN_spec p.1.1.deco.2.lat p.1.1.deco.2.uni P.1 (hM P).ne hx).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P g hg
    have e : (tdatAt sel mu cst L Tp u i).deco b p = p.1.1.deco.1.res (Finset.empty_subset _) :=
      Deco.ext rfl rfl (funext fun w => absurd w.2 (Finset.notMem_empty _))
    rw [e] at hg
    have hg' := dn_ok_of_res p.1.1.deco.2 P (hM P) (g := g) hg
    have hm := mv_dn p P (hM P) (hQ' P) (hy P) hg'
    refine ⟨fun w hw => ?_, (congrArg Deco.be hm.1).symm, hm.2.1.symm, hm.2.2.symm⟩
    refine Eq.trans ?_ (congrArg (fun d : Deco X.E _ _ _ => localization₂ w.asIdeal d.N) hm.1).symm
    exact ((p.1.1.deco.2.dnN_spec P (hM P).ne).2.2.1 w (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm
  · intro b p P a
    show SameOffPt sel mu cst u p (PtY.mv p (DecoSet.dia1 P a p.1.1.deco))
    rw [PtY.mv_dia]
    exact ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  · intro b p P P' a hne
    show (PtY.mv p (DecoSet.dia1 P a p.1.1.deco)).1.1.deco.1.f P' = p.1.1.deco.1.f P'
    rw [PtY.mv_dia]
    funext x
    show ((Pi.mulSingle P a : DiaG (E := X.E) (ST := Pr.vT u)) P').1 * _ = _
    rw [Pi.mulSingle_eq_of_ne hne, Units.val_one, one_mul]
  · intro b γ h
    obtain ⟨g, hg⟩ := exists_ufGL γ h
    exact ⟨(g, 1, 1), hg⟩

end GlobalTheory.LvT.Built.SplitPts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UkTermOfMoveStep
noncomputable section

namespace GlobalTheory.KerT.UK

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (AgreeOff InBox moveScal idxExp locScal)
open GlobalTheory.CharValCompare (IsFr exists_isFr ordDet_eq intAt_iff dt dt_eq dt_ne)

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n a b : ℕ} {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

omit [StarRing E] in
theorem mem_localization_of_smul_mem {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {s : 𝓞 E} (hs : s ∉ P.asIdeal) {v : Sp E n}
    (h : s • v ∈ localization₂ P.asIdeal N) : v ∈ localization₂ P.asIdeal N := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim ht hs, by rw [mul_smul]; exact h⟩

omit [StarRing E] in
theorem intAt_smul_mem {P : HeightOneSpectrum (𝓞 E)} {N : Submodule (𝓞 E) (Sp E n)} {t : E} (ht : IntAt P t) {v : Sp E n}
    (h : v ∈ localization₂ P.asIdeal N) : t • v ∈ localization₂ P.asIdeal N := by
  obtain ⟨r, s, hs, e⟩ := ht
  refine mem_localization_of_smul_mem hs ?_
  rw [← algebraMap_smul E s, smul_smul, e, algebraMap_smul]
  exact Submodule.smul_mem _ r h

theorem f_sub {d : Deco E n ST SG} (hd : d.Ok) (P : ST) {x y : Sp E n} (hx : x ∈ d.at P.1) (hy : y ∈ d.at P.1) :
    d.f P (x - y) = d.f P x - d.f P y := by
  have := hd.f_add P (x - y) (sub_mem hx hy) y hy
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem f_smul_eq_zero_iff {d : Deco E n ST SG} (hd : d.Ok) (P : ST) {s : 𝓞 E} (hs : s ∉ P.1.asIdeal) {x : Sp E n}
    (hx : x ∈ d.at P.1) : d.f P (s • x) = 0 ↔ d.f P x = 0 := by
  have := P.1.isPrime
  rw [hd.f_smul P s x hx, mul_eq_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact ⟨fun h => h.resolve_left hs, Or.inr⟩

theorem mem_dnN_at {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) (v : Sp E n) :
    v ∈ localization₂ P.1.asIdeal (d.dnN P) ↔ v ∈ d.at P.1 ∧ d.f P v = 0 := by
  rw [(hd.dnN_spec P hne).2.2.2, mem_locP]
  constructor
  · rintro ⟨s, hs, h⟩
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P _).1 h
    have hv : v ∈ d.at P.1 := ⟨s, hs, h1⟩
    exact ⟨hv, (f_smul_eq_zero_iff hd P hs hv).1 h2⟩
  · rintro ⟨hv, h0⟩
    obtain ⟨s, hs, h⟩ := (mem_locP _ _ _).1 hv
    exact ⟨s, hs, (hd.mem_kerAt P _).2 ⟨h, (f_smul_eq_zero_iff hd P hs hv).2 h0⟩⟩

theorem exists_f_one {d : Deco E n ST SG} (hd : d.Ok) (P : ST) : ∃ e ∈ d.N, d.f P e = 1 := by
  obtain ⟨e, h1, h2, -⟩ := hd.exists_dualBasis
  exact ⟨e P, h1 P, h2 P⟩

theorem f_sum {d : Deco E n ST SG} (hd : d.Ok) (P : ST) {ι : Type} (s : Finset ι) (v : ι → Sp E n) (h : ∀ i, v i ∈ d.at P.1) :
    d.f P (∑ i ∈ s, v i) = ∑ i ∈ s, d.f P (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hd.f_zero P
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hd.f_add P _ (h i) _ (Submodule.sum_mem _ fun j _ => h j), ih]

theorem exists_lift {d : Deco E n ST SG} (hd : d.Ok) (P : ST) :
    ∃ φ : Module.Dual E (Sp E n), ∀ v ∈ d.at P.1, P.1.valuation E (φ v) ≤ 1 ∧ (d.f P v = 0 ↔ P.1.valuation E (φ v) < 1) := by
  classical
  obtain ⟨fr, hfr⟩ := exists_isFr P.1 ⟨hd.lat, hd.uni⟩
  have hb : ∀ i : Fin n, fr (Pi.single i 1) ∈ d.at P.1 := fun i => (hfr _).2 (GlobalTheory.CharValCompare.single_mem_stdAt P.1 i)
  choose c hc using fun i : Fin n => Ideal.Quotient.mk_surjective (d.f P (fr (Pi.single i 1)))
  refine ⟨(∑ i, algebraMap (𝓞 E) E (c i) • (LinearMap.proj i : Sp E n →ₗ[E] E)) ∘ₗ fr.symm.toLinearMap, fun v hv => ?_⟩
  obtain ⟨x, rfl⟩ := fr.surjective v
  obtain ⟨s, hs, hx⟩ := (mem_locP _ _ _).1 ((hfr x).1 hv)
  have hr : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = (s • x) i := fun i => by
    have := hx i trivial
    exact Submodule.mem_one.1 this
  choose r hr using hr
  have e1 : s • fr x = ∑ i, r i • fr (Pi.single i 1) := by
    rw [← equiv_osmul]
    simp_rw [← equiv_osmul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    congr 1
    funext j
    rw [← hr j, Finset.sum_apply, Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_eq_of_ne hi.symm]) (by simp)]
    simp [Algebra.smul_def]
  have e2 : algebraMap (𝓞 E) E s * ((∑ i, algebraMap (𝓞 E) E (c i) • (LinearMap.proj i : Sp E n →ₗ[E] E)) ∘ₗ
      fr.symm.toLinearMap) (fr x) = algebraMap (𝓞 E) E (∑ i, r i * c i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, map_sum, map_mul, hr, Finset.mul_sum, smul_eq_mul, Pi.smul_apply, Algebra.smul_def]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 := congrArg (P.1.valuation E) e2
  rw [map_mul, GlobalTheory.CharValCompare.val_of_notMem hs, one_mul] at e3
  rw [e3]
  refine ⟨P.1.valuation_le_one _, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [P.1.valuation_lt_one_iff_mem, ← f_smul_eq_zero_iff hd P hs hv, e1,
    f_sum hd P _ _ fun i => Submodule.smul_mem _ _ (hb i), ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  simp_rw [fun i => hd.f_smul P (r i) _ (hb i), map_mul, hc]

theorem idxExp_dnN {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1) : idxExp P.1 d.N (d.dnN P) = 1 := by
  obtain ⟨φ, hφ⟩ := exists_lift hd P
  obtain ⟨e, he, hfe⟩ := exists_f_one hd P
  have he' : e ∈ d.at P.1 := le_locP _ _ he
  have hP := P.1.isPrime
  have hve : P.1.valuation E (φ e) = 1 :=
    le_antisymm (hφ e he').1 (not_lt.1 fun h => one_ne_zero (hfe.symm.trans ((hφ e he').2.2 h)))
  have he0 : φ e ≠ 0 := fun h => by simp [h] at hve
  obtain ⟨π, hπ⟩ := P.1.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := fun h => by
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hπ1 : P.1.valuation E π < 1 := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hc : P.1.valuation E ((π - 1) / φ e) ≤ 1 := by
    rw [map_div₀, hve, div_one]
    exact (Valuation.map_sub _ _ _).trans (max_le hπ1.le (by simp))
  set g := LinearMap.transvection (((π - 1) / φ e) • φ) e with hg
  have hdet : LinearMap.det g = π := by
    rw [hg, LinearMap.transvection.det, LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ he0]
    ring
  have hgv : ∀ v, g v = v + ((π - 1) / φ e * φ v) • e := fun v => by
    rw [hg, LinearMap.transvection.apply, LinearMap.smul_apply, smul_eq_mul]
  have hφg : ∀ v, φ (g v) = π * φ v := fun v => by
    rw [hgv, map_add (f := _), map_smul, smul_eq_mul]
    field_simp
    ring
  have hkey : ∀ t : E, P.1.valuation E (π * t) < 1 ↔ P.1.valuation E t ≤ 1 := fun t => by
    by_cases ht : t = 0
    · simp [ht]
    · have h1 : P.1.valuation E t ≠ 0 := (Valuation.ne_zero_iff _).2 ht
      rw [map_mul, hπ, ← WithZero.exp_log h1, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
      omega
  have hint : ∀ v, P.1.valuation E (φ v) ≤ 1 → ((π - 1) / φ e * φ v) • e ∈ d.at P.1 := fun v hv =>
    intAt_smul_mem (intAt_iff.2 (by rw [map_mul]; exact mul_le_one' hc hv)) he'
  obtain ⟨fr, hfr⟩ := exists_isFr P.1 ⟨hd.lat, hd.uni⟩
  let g' := g.equivOfDetNeZero (hdet ▸ hπ0)
  have hg' : ∀ v, g' v = g v := fun v => rfl
  have hfr' : IsFr P.1 (d.dnN P) (g' * fr) := fun x => by
    rw [← hfr x, LinearEquiv.mul_apply, hg', mem_dnN_at hd P hne]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := (hφ _ h1).2.1 h2
      rw [hφg, hkey] at h3
      rw [hgv] at h1
      exact (Submodule.add_mem_iff_left _ (hint _ h3)).1 h1
    · intro h1
      have h3 : g (fr x) ∈ d.at P.1 := by
        rw [hgv]
        exact add_mem h1 (hint _ (hφ _ h1).1)
      refine ⟨h3, (hφ _ h3).2.2 ?_⟩
      rw [hφg, hkey]
      exact (hφ _ h1).1
  have hd' : dt (g' * fr) = π * dt fr := by
    rw [dt, map_mul, Units.val_mul, LinearEquiv.coe_det g', ← hdet]
    rfl
  have h1 : P.1.valuation E (dt fr) ≠ 0 := (Valuation.ne_zero_iff _).2 (dt_ne fr)
  unfold idxExp
  rw [ordDet_eq hfr', ordDet_eq hfr, hd', ordE, ordE, map_mul, hπ, WithZero.log_mul (by simp) h1, WithZero.log_exp]
  ring

omit [StarRing E] in
theorem idxExp_of_eq {P : HeightOneSpectrum (𝓞 E)} {N₁ N₂ : Submodule (𝓞 E) (Sp E n)}
    (h : localization₂ P.asIdeal N₂ = localization₂ P.asIdeal N₁) : idxExp P N₁ N₂ = 0 := by
  unfold idxExp ordDet frameAt
  rw [h, sub_self]

def Rel (d : Deco E a ST SG) (d' : Deco E b ST SG') (x : HomE E a b) : Prop :=
  ∀ P : ST, ∀ y ∈ d.at P.1, x y ∈ d'.at P.1 ∧ d'.f P (x y) = d.f P y

open Classical in
omit [StarRing E] in
theorem phiT_eq (K : Type) [Field K] (d : Deco E a ST SG) (d' : Deco E b ST SG') (x : HomE E a b) :
    phiT K d d' x = if Rel d d' x then 1 else 0 := by
  unfold phiT Rel
  congr

omit [StarRing E] in
theorem hom_smul (x : HomE E a b) (s : 𝓞 E) (v : Sp E a) : x (s • v) = s • x v := by
  rw [← algebraMap_smul E s v, map_smul, algebraMap_smul]

theorem dnN_at_ne {d : Deco E n ST SG} (hd : d.Ok) {P : ST} (hP : MoveHyp ST SG P) {Q : ST} (hQ : Q ≠ P) :
    localization₂ Q.1.asIdeal (d.dnN P) = d.at Q.1 :=
  ((hd.dnN_spec P hP.ne).2.2.1 Q.1 (fun h => hQ (Subtype.ext h)) (hP.st Q)).localization_eq

section Up

variable {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
  {d₀ d : Deco E n ST SG} (hd₀ : d₀.Ok) (h : d₀.IsUp P q d)

include hP hq hq2 hd₀ h

theorem up_ok : d.Ok := by
  obtain ⟨x, hx, hfx, rfl⟩ := h
  exact hd₀.up P hP hq hq2 hx hfx

theorem up_N : d₀.N = d.dnN P := by
  obtain ⟨x, hx, hfx, rfl⟩ := h
  exact (hd₀.dnN_up P hP hq hq2 hx hfx).symm

theorem up_at (v : Sp E n) : v ∈ d₀.at P.1 ↔ v ∈ d.at P.1 ∧ d.f P v = 0 := by
  rw [Deco.at, up_N hP hq hq2 hd₀ h, mem_dnN_at (up_ok hP hq hq2 hd₀ h) P hP.ne]

theorem up_at_ne {Q : ST} (hQ : Q ≠ P) : d₀.at Q.1 = d.at Q.1 := by
  rw [Deco.at, up_N hP hq hq2 hd₀ h, dnN_at_ne (up_ok hP hq hq2 hd₀ h) hP hQ]

omit hP hq hq2 hd₀ in
theorem up_f_ne {Q : ST} (hQ : Q ≠ P) : d₀.f Q = d.f Q := by
  obtain ⟨x, -, -, rfl⟩ := h
  exact (d₀.up_f_ne P q x hQ).symm

omit hP hq hq2 hd₀ in
theorem up_f {v : Sp E n} (hv : v ∈ d.at P.1) : d.f P v = d₀.f P (q • v) := by
  obtain ⟨x, -, -, rfl⟩ := h
  rw [Deco.up_f]
  exact if_pos hv

omit hP hq hq2 hd₀ in
theorem up_be : d₀.be = d.be := by
  obtain ⟨x, -, -, rfl⟩ := h
  rfl

theorem up_smul_mem {v : Sp E n} (hv : v ∈ d.at P.1) : q • v ∈ d₀.at P.1 := by
  rw [up_at hP hq hq2 hd₀ h, (up_ok hP hq hq2 hd₀ h).f_smul P q v hv, Ideal.Quotient.eq_zero_iff_mem.2 hq, zero_mul]
  exact ⟨Submodule.smul_mem _ _ hv, rfl⟩

end Up

theorem inv_mem_up {P : ST} (hP : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
    {d : Deco E n ST SG} (hd : d.Ok) {x : Sp E n} (hx : x ∈ d.N) (hfx : d.f P x = 1) :
    (algebraMap (𝓞 E) E q)⁻¹ • x ∈ (d.up P q x).at P.1 := by
  by_contra hn
  have h1 := hd.up_f_inv P hP hq hq2 hx hfx
  rw [(hd.up P hP hq hq2 hx hfx).f_off P _ hn] at h1
  exact zero_ne_one h1

theorem intAt_inv_mul {P : HeightOneSpectrum (𝓞 E)} {q p : 𝓞 E} (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2)
    (hp : p ∈ P.asIdeal) : IntAt P ((algebraMap (𝓞 E) E q)⁻¹ * algebraMap (𝓞 E) E p) := by
  obtain ⟨c, hc, r, hr, hcr⟩ := exists_inv_unif P hq hq2
  obtain ⟨β, hβ⟩ := neighbourConstruct_mem_inv.1 hc p hp
  have hq0 : algebraMap (𝓞 E) E q ≠ 0 := fun h0 => hq2 (by
    rw [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 E) E).1 h0]
    exact Ideal.zero_mem _)
  refine ⟨β, r, hr, ?_⟩
  rw [← hcr, hβ]
  field_simp

section Count

variable {P : ST} (hP : MoveHyp ST SG P) (hP' : MoveHyp ST SG' P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2)
  {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd : d.Ok) (hd' : d'.Ok) {x : HomE E a b}


include hP' hq hq2 hd hd' in
theorem up_unique {d₁ d₂ : Deco E b ST SG'} (h₁ : d'.IsUp P q d₁) (h₂ : d'.IsUp P q d₂) (r₁ : Rel d d₁ x) (r₂ : Rel d d₂ x) :
    d₁ = d₂ := by
  obtain ⟨e, he, hfe⟩ := exists_f_one hd P
  have key : ∀ x₁ ∈ d'.N, d'.f P x₁ = 1 → Rel d (d'.up P q x₁) x → x e - (algebraMap (𝓞 E) E q)⁻¹ • x₁ ∈ d'.at P.1 := by
    intro x₁ hx₁ hf₁ r
    have hu : d'.IsUp P q (d'.up P q x₁) := ⟨x₁, hx₁, hf₁, rfl⟩
    obtain ⟨m1, m2⟩ := r P e (le_locP _ _ he)
    have m3 := inv_mem_up hP' hq hq2 hd' hx₁ hf₁
    rw [up_at hP' hq hq2 hd' hu, f_sub (up_ok hP' hq hq2 hd' hu) P m1 m3, m2, hfe, hd'.up_f_inv P hP' hq hq2 hx₁ hf₁, sub_self]
    exact ⟨sub_mem m1 m3, rfl⟩
  obtain ⟨x₁, hx₁, hf₁, rfl⟩ := h₁
  obtain ⟨x₂, hx₂, hf₂, rfl⟩ := h₂
  have h3 := sub_mem (key x₂ hx₂ hf₂ r₂) (key x₁ hx₁ hf₁ r₁)
  rw [sub_sub_sub_cancel_left, ← smul_sub] at h3
  obtain ⟨s, hs, h4⟩ := (mem_locP _ _ _).1 h3
  have hq0 : algebraMap (𝓞 E) E q ≠ 0 := fun h0 => hq2 (by
    rw [(FaithfulSMul.algebraMap_eq_zero_iff (𝓞 E) E).1 h0]
    exact Ideal.zero_mem _)
  refine d'.up_congr P q (mem_smul_of_loc (sub_mem hx₁ hx₂) hs ?_)
  have e1 : s • (x₁ - x₂) = q • s • (algebraMap (𝓞 E) E q)⁻¹ • (x₁ - x₂) := by
    rw [smul_comm q s, ← algebraMap_smul E q, smul_smul (algebraMap (𝓞 E) E q), mul_inv_cancel₀ hq0, one_smul]
  rw [e1]
  exact Submodule.smul_mem_smul hq h4


include hP hq hq2 in
theorem dn_unique {d₁ d₂ : Deco E a ST SG} (hd₁ : d₁.Ok) (hd₂ : d₂.Ok) (h₁ : d₁.IsUp P q d) (h₂ : d₂.IsUp P q d)
    (r₁ : Rel d₁ d' x) (r₂ : Rel d₂ d' x) : d₁ = d₂ := by
  have hN : d₁.N = d₂.N := (up_N hP hq hq2 hd₁ h₁).trans (up_N hP hq hq2 hd₂ h₂).symm
  refine hd₁.ext_on hd₂ hN (fun Q y hy => ?_) fun w y _ => by rw [up_be h₁, up_be h₂]
  rw [← (r₁ Q y (le_locP _ _ hy)).2, ← (r₂ Q y (le_locP _ _ (hN ▸ hy))).2]

include hP hP' hq hq2 hd hd' in
theorem exists_dn_of_up {d₁ : Deco E b ST SG'} (h₁ : d'.IsUp P q d₁) (r₁ : Rel d d₁ x) :
    ∃ d₀ : Deco E a ST SG, d₀.Ok ∧ d₀.IsUp P q d ∧ Rel d₀ d' x := by
  classical
  have hx : ∀ y ∈ localization₂ P.1.asIdeal (d.dnN P), x y ∈ d'.at P.1 := fun y hy => by
    obtain ⟨m1, m2⟩ := (mem_dnN_at hd P hP.ne y).1 hy
    rw [up_at hP' hq hq2 hd' h₁, (r₁ P y m1).2]
    exact ⟨(r₁ P y m1).1, m2⟩
  let f₀ : Sp E a → 𝓞 E ⧸ P.1.asIdeal := fun y => if y ∈ localization₂ P.1.asIdeal (d.dnN P) then d'.f P (x y) else 0
  have hone : ∀ e ∈ d.N, d.f P e = 1 → q • e ∈ d.dnN P ∧ f₀ (q • e) = 1 := fun e he hfe => by
    have m1 : q • e ∈ d.dnN P := (le_sup_left : d.kerAt P ≤ d.dnN P) (hd.smul_mem_kerAt P hq he)
    refine ⟨m1, ?_⟩
    simp only [f₀, if_pos (le_locP _ _ m1)]
    rw [hom_smul, ← up_f h₁ (r₁ P e (le_locP _ _ he)).1, (r₁ P e (le_locP _ _ he)).2, hfe]
  have hok : (d.dn P f₀).Ok := by
    refine hd.dn P hP (fun y hy z hz => ?_) (fun c y hy => ?_) (fun y hy => if_neg hy) ?_
    · simp only [f₀, if_pos hy, if_pos hz, if_pos (add_mem hy hz)]
      rw [map_add (f := _), hd'.f_add P _ (hx y hy) _ (hx z hz)]
    · simp only [f₀, if_pos hy, if_pos (Submodule.smul_mem _ c hy)]
      rw [hom_smul, hd'.f_smul P c _ (hx y hy)]
    · obtain ⟨e, he, hfe⟩ := exists_f_one hd P
      exact ⟨_, (hone e he hfe).1, by rw [(hone e he hfe).2]; exact one_ne_zero⟩
  have hf : (d.dn P f₀).f P = f₀ := by simp [Deco.dn]
  have hup : (d.dn P f₀).IsUp P q d :=
    Deco.IsDn.isUp hok hd hP hq hq2 ⟨by rw [hf], fun e he hfe => by rw [hf]; exact (hone e he hfe).2⟩
  refine ⟨_, hok, hup, fun Q y hy => ?_⟩
  by_cases hQ : Q = P
  · subst hQ
    have hy' : y ∈ localization₂ Q.1.asIdeal (d.dnN Q) := hy
    rw [hf]
    exact ⟨hx y hy', (if_pos hy').symm⟩
  · rw [up_at_ne hP hq hq2 hok hup hQ] at hy
    rw [up_at_ne hP' hq hq2 hd' h₁ hQ, up_f_ne h₁ hQ, up_f_ne hup hQ]
    exact r₁ Q y hy

include hP hP' hq hq2 hd' in
theorem exists_up_of_dn {d₀ : Deco E a ST SG} (hd₀ : d₀.Ok) (h₀ : d₀.IsUp P q d) (r₀ : Rel d₀ d' x) :
    ∃ d₁ : Deco E b ST SG', d₁.Ok ∧ d'.IsUp P q d₁ ∧ Rel d d₁ x := by
  have hd := up_ok hP hq hq2 hd₀ h₀
  have h₀' := h₀
  obtain ⟨x₀, hx₀, hf₀, hd0⟩ := h₀'
  obtain ⟨m1, m2⟩ := r₀ P x₀ (le_locP _ _ hx₀)
  obtain ⟨s, hs, m3⟩ := (mem_locP _ _ _).1 m1
  obtain ⟨t, p, hp, etp⟩ := P.1.isMaximal.exists_inv hs
  have e1 : x x₀ = t • s • x x₀ + p • x x₀ := by rw [← mul_smul, ← add_smul, etp, one_smul]
  have hw : t • s • x x₀ ∈ d'.N := Submodule.smul_mem _ t m3
  have hfw : d'.f P (t • s • x x₀) = 1 := by
    have := hd'.f_add P _ (le_locP _ _ hw) _ (Submodule.smul_mem _ p m1)
    rw [← e1, hd'.f_smul P p _ m1, Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul, add_zero, m2, hf₀] at this
    exact this.symm
  have h₁ : d'.IsUp P q (d'.up P q (t • s • x x₀)) := ⟨_, hw, hfw, rfl⟩
  have hle : ∀ v ∈ d'.at P.1, v ∈ (d'.up P q (t • s • x x₀)).at P.1 := fun v hv => ((up_at hP' hq hq2 hd' h₁ v).1 hv).1
  refine ⟨_, up_ok hP' hq hq2 hd' h₁, h₁, fun Q y hy => ?_⟩
  by_cases hQ : Q = P
  · subst hQ
    have he : (algebraMap (𝓞 E) E q)⁻¹ • x₀ ∈ d.at Q.1 := hd0 ▸ inv_mem_up hP hq hq2 hd₀ hx₀ hf₀
    have hfe : d.f Q ((algebraMap (𝓞 E) E q)⁻¹ • x₀) = 1 := hd0 ▸ hd₀.up_f_inv Q hP hq hq2 hx₀ hf₀
    have hxe : x ((algebraMap (𝓞 E) E q)⁻¹ • x₀) ∈ (d'.up Q q (t • s • x x₀)).at Q.1 := by
      have e2 : x ((algebraMap (𝓞 E) E q)⁻¹ • x₀) = (algebraMap (𝓞 E) E q)⁻¹ • (t • s • x x₀) +
          ((algebraMap (𝓞 E) E q)⁻¹ * algebraMap (𝓞 E) E p) • x x₀ := by
        rw [mul_smul, algebraMap_smul, ← smul_add, ← e1, map_smul]
      rw [e2]
      exact add_mem (inv_mem_up hP' hq hq2 hd' hw hfw) (hle _ (intAt_smul_mem (intAt_inv_mul hq hq2 hp) m1))
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (d.f Q y)
    have hl : y - c • (algebraMap (𝓞 E) E q)⁻¹ • x₀ ∈ d₀.at Q.1 := by
      rw [up_at hP hq hq2 hd₀ h₀, f_sub hd Q hy (Submodule.smul_mem _ c he), hd.f_smul Q c _ he, hfe, mul_one, hc, sub_self]
      exact ⟨sub_mem hy (Submodule.smul_mem _ c he), rfl⟩
    have hxy : x y ∈ (d'.up Q q (t • s • x x₀)).at Q.1 := by
      have := add_mem (hle _ (r₀ Q _ hl).1) (Submodule.smul_mem _ c hxe)
      rwa [← hom_smul x c, ← map_add, sub_add_cancel] at this
    refine ⟨hxy, ?_⟩
    rw [up_f h₁ hxy, ← hom_smul, (r₀ Q _ (up_smul_mem hP hq hq2 hd₀ h₀ hy)).2, up_f h₀ hy]
  · rw [← up_at_ne hP hq hq2 hd₀ h₀ hQ] at hy
    rw [← up_at_ne hP' hq hq2 hd' h₁ hQ, ← up_f_ne h₁ hQ, ← up_f_ne h₀ hQ]
    exact r₀ Q y hy

end Count

open Classical in
theorem sum_ite_unique {α K : Type} [Field K] (s : Finset α) (p : α → Prop) (h : ∀ u ∈ s, ∀ v ∈ s, p u → p v → u = v) :
    (∑ u ∈ s, if p u then (1 : K) else 0) = if ∃ u ∈ s, p u then 1 else 0 := by
  split_ifs with he
  · obtain ⟨u, hu, hp⟩ := he
    rw [Finset.sum_eq_single_of_mem u hu fun v hv hne => if_neg fun hv' => hne (h v hv u hu hv' hp), if_pos hp]
  · exact Finset.sum_eq_zero fun v hv => if_neg fun hv' => he ⟨v, hv, hv'⟩

theorem sum_phiT (K : Type) [Field K] {P : ST} (hP : MoveHyp ST SG P) (hP' : MoveHyp ST SG' P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal)
    (hq2 : q ∉ P.1.asIdeal ^ 2) (d : DecoSet (E := E) (n := a) (ST := ST) (SG := SG)) (d' : DecoSet (E := E) (n := b) (ST := ST) (SG := SG')) (U : Finset (DecoSet (E := E) (n := b) (ST := ST) (SG := SG')))
    (D : Finset (DecoSet (E := E) (n := a) (ST := ST) (SG := SG))) (hU : ∀ d₁, d₁ ∈ U ↔ d'.1.IsUp P q d₁.1) (hD : ∀ d₀, d₀ ∈ D ↔ d₀.1.IsUp P q d.1)
    (x : HomE E a b) : ∑ d₁ ∈ U, phiT K d.1 d₁.1 x = ∑ d₀ ∈ D, phiT K d₀.1 d'.1 x := by
  classical
  simp_rw [phiT_eq]
  rw [sum_ite_unique U (fun d₁ => Rel d.1 d₁.1 x) fun u hu v hv ru rv =>
      Subtype.ext (up_unique hP' hq hq2 d.2 d'.2 ((hU u).1 hu) ((hU v).1 hv) ru rv),
    sum_ite_unique D (fun d₀ => Rel d₀.1 d'.1 x) fun u hu v hv ru rv =>
      Subtype.ext (dn_unique hP hq hq2 u.2 v.2 ((hD u).1 hu) ((hD v).1 hv) ru rv)]
  refine if_congr ⟨?_, ?_⟩ rfl rfl
  · rintro ⟨u, hu, ru⟩
    obtain ⟨d₀, h1, h2, h3⟩ := exists_dn_of_up hP hP' hq hq2 d.2 d'.2 ((hU u).1 hu) ru
    exact ⟨⟨d₀, h1⟩, (hD _).2 h2, h3⟩
  · rintro ⟨u, hu, ru⟩
    obtain ⟨d₁, h1, h2, h3⟩ := exists_up_of_dn hP hP' hq hq2 d'.2 u.2 ((hD u).1 hu) ru
    exact ⟨⟨d₁, h1⟩, (hU _).2 h2, h3⟩

theorem rel_add {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok) {x y : HomE E a b}
    (hy : ∀ Q : ST, ∀ v ∈ d.at Q.1, y v ∈ d'.at Q.1 ∧ d'.f Q (y v) = 0) : Rel d d' (x + y) ↔ Rel d d' x := by
  refine forall_congr' fun Q => forall₂_congr fun v hv => ?_
  obtain ⟨m1, m2⟩ := hy Q v hv
  rw [LinearMap.add_apply, Submodule.add_mem_iff_left _ m1]
  exact and_congr_right fun m => by rw [hd'.f_add Q _ m _ m1, m2, add_zero]

theorem inBox_of {K : Type} [Field K] {SA SB : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ Q, Q ∈ SA ↔ Q ∈ ST ∨ Q ∈ SB) {cA cB : ℕ}
    {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok) {M : Submodule (𝓞 E) (Sp E a)} {M' : Submodule (𝓞 E) (Sp E b)}
    {Ξ₀ : HomE E a b → K} (h₀ : InBox SB cA cB M M' Ξ₀)
    (h1 : ∀ x, Rel d d' x → ∀ Q : ST, ∀ v ∈ localization₂ Q.1.asIdeal M, x v ∈ localization₂ Q.1.asIdeal M')
    (h2 : ∀ z : HomE E a b, ∀ Q : ST, (∀ v ∈ localization₂ Q.1.asIdeal M, z v ∈ localization₂ Q.1.asIdeal M') →
      ∀ v ∈ d.at Q.1, (cB : 𝓞 E) • z v ∈ d'.at Q.1 ∧ d'.f Q ((cB : 𝓞 E) • z v) = 0) :
    InBox SA cA cB M M' fun x => phiT K d d' x * Ξ₀ x := by
  refine ⟨fun x hx Q hQ v hv => ?_, ?_⟩
  · rcases (hS Q).1 hQ with hQ | hQ
    · have hr : Rel d d' x := by
        by_contra hr
        exact left_ne_zero_of_mul hx (by rw [phiT_eq, if_neg hr])
      exact Submodule.smul_mem _ (cA : 𝓞 E) (h1 x hr ⟨Q, hQ⟩ v hv)
    · exact h₀.1 x (right_ne_zero_of_mul hx) Q hQ v hv
  · rintro x _ ⟨z, hz, rfl⟩
    have e := h₀.2 x _ ⟨z, fun Q hQ => hz Q ((hS Q).2 (Or.inr hQ)), rfl⟩
    simp only []
    rw [e, phiT_eq, phiT_eq, rel_add hd' fun Q v hv => h2 z Q (hz Q.1 ((hS Q.1).2 (Or.inl Q.2))) v hv]

omit [StarRing E] in
theorem inBox_congr {K : Type} [Field K] {SB : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ} {N M : Submodule (𝓞 E) (Sp E a)}
    {N' M' : Submodule (𝓞 E) (Sp E b)} {Ξ₀ : HomE E a b → K} (h₀ : InBox SB cA cB N N' Ξ₀)
    (h : ∀ Q ∈ SB, localization₂ Q.asIdeal N = localization₂ Q.asIdeal M) (h' : ∀ Q ∈ SB, localization₂ Q.asIdeal N' = localization₂ Q.asIdeal M') :
    InBox SB cA cB M M' Ξ₀ := by
  have e : homAt SB M M' = homAt SB N N' := by
    ext x
    refine forall₂_congr fun Q hQ => ?_
    rw [h Q hQ, h' Q hQ]
  unfold InBox at h₀ ⊢
  rwa [e]

theorem agreeOff_dnN {T : ℕ} {d : Deco E n ST SG} (hd : d.Ok) {P : ST} (hne : conjPrime₂ P.1 ≠ P.1) (hT : (T : 𝓞 E) ∈ P.1.asIdeal) :
    AgreeOff T d.N (d.dnN P) := fun Q hQ =>
  ((hd.dnN_spec P hne).2.2.1 Q (fun e => hQ (e ▸ hT)) fun e => hQ (by rw [e, mem_conjP, map_natCast]; exact hT)).localization_eq.symm

theorem inBox_up {K : Type} [Field K] {SA SB : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ Q, Q ∈ SA ↔ Q ∈ ST ∨ Q ∈ SB) {cA cB : ℕ}
    (hc : ∀ Q : ST, (cB : 𝓞 E) ∈ Q.1.asIdeal) {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd' : d'.Ok)
    {Ξ₀ : HomE E a b → K} (h₀ : InBox SB cA cB d.N d'.N Ξ₀) : InBox SA cA cB d.N d'.N fun x => phiT K d d' x * Ξ₀ x :=
  inBox_of hS hd' h₀ (fun _ hr Q v hv => (hr Q v hv).1) fun z Q hz v hv =>
    ⟨Submodule.smul_mem _ _ (hz v hv), by rw [hd'.f_smul Q _ _ (hz v hv), Ideal.Quotient.eq_zero_iff_mem.2 (hc Q), zero_mul]⟩

theorem inBox_dn {K : Type} [Field K] {SA SB : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ Q, Q ∈ SA ↔ Q ∈ ST ∨ Q ∈ SB) {cA cB : ℕ}
    (hc : ∀ Q : ST, (cB : 𝓞 E) ∈ Q.1.asIdeal) {d : Deco E a ST SG} {d' : Deco E b ST SG'} (hd : d.Ok) (hd' : d'.Ok) {P : ST}
    (hP : MoveHyp ST SG P) (hP' : MoveHyp ST SG' P) {Ξ₀ : HomE E a b → K} (h₀ : InBox SB cA cB (d.dnN P) (d'.dnN P) Ξ₀) :
    InBox SA cA cB (d.dnN P) (d'.dnN P) fun x => phiT K d d' x * Ξ₀ x := by
  refine inBox_of hS hd' h₀ (fun x hr Q v hv => ?_) fun z Q hz v hv => ?_
  · by_cases hQ : Q = P
    · subst hQ
      obtain ⟨m1, m2⟩ := (mem_dnN_at hd Q hP.ne v).1 hv
      exact (mem_dnN_at hd' Q hP'.ne _).2 ⟨(hr Q v m1).1, (hr Q v m1).2.trans m2⟩
    · rw [dnN_at_ne hd hP hQ] at hv
      rw [dnN_at_ne hd' hP' hQ]
      exact (hr Q v hv).1
  · by_cases hQ : Q = P
    · subst hQ
      rw [← hom_smul, ← mem_dnN_at hd' Q hP'.ne]
      refine hz _ ((mem_dnN_at hd Q hP.ne _).2 ⟨Submodule.smul_mem _ _ hv, ?_⟩)
      rw [hd.f_smul Q _ _ hv, Ideal.Quotient.eq_zero_iff_mem.2 (hc Q), zero_mul]
    · rw [dnN_at_ne hd hP hQ, dnN_at_ne hd' hP' hQ] at hz
      exact ⟨Submodule.smul_mem _ _ (hz v hv), by
        rw [hd'.f_smul Q _ _ (hz v hv), Ideal.Quotient.eq_zero_iff_mem.2 (hc Q), zero_mul]⟩

theorem kerOf_sum {K : Type} [Field K] {SB : Finset (HeightOneSpectrum (𝓞 E))} {V V' : Type} [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (th : ThDist E K a b SB V V') (SA : Finset (HeightOneSpectrum (𝓞 E))) {cA cB : ℕ}
    (hA : 0 < cA) (hB : 0 < cB) {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} (hN : Submodule.IsLattice E N)
    (hN' : Submodule.IsLattice E N') (fr : Frs E a SB) (fr' : Frs E b SB) {ι : Type} (s : Finset ι) (Ξ : ι → HomE E a b → K) :
    ∑ k ∈ s, kerOf th SA cA cB N fr N' fr' (Ξ k) = kerOf th SA cA cB N fr N' fr' fun x => ∑ k ∈ s, Ξ k x := by
  have card_finset_le {V A Q : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] [AddCommGroup A] [AddCommGroup Q]
      (f : A →+ V) (hf : Function.Injective f) (π : A →+ Q) (hπ : Function.Surjective π) (n : ℕ) (hn : 0 < n)
      (h0 : ∀ x : A, π (n • x) = 0) (s : Finset Q) : s.card ≤ n ^ Module.finrank ℚ V := by
    classical
    obtain ⟨σ, hσ⟩ := hπ.hasRightInverse
    let F : Submodule ℤ A := Submodule.span ℤ (↑(s.image σ) : Set A)
    haveI : Module.Finite ℤ F := Module.Finite.span_of_finite ℤ (Finset.finite_toSet _)
    let g : F →ₗ[ℤ] V := f.toIntLinearMap ∘ₗ F.subtype
    have hg : Function.Injective g := hf.comp F.subtype_injective
    haveI : HasUniqueDiv V := HasUniqueDiv.of_module_rat V
    haveI : Module.IsTorsionFree ℤ F := Function.Injective.moduleIsTorsionFree g hg (by simp)
    haveI : Module.Free ℤ F := Module.free_of_finite_type_torsion_free'
    have hr : Module.finrank ℤ F ≤ Module.finrank ℚ V := by
      let b := Module.finBasis ℤ F
      have h1 : LinearIndependent ℤ (g ∘ b) := b.linearIndependent.map' g (LinearMap.ker_eq_bot.2 hg)
      have h2 : LinearIndependent ℚ (g ∘ b) := (LinearIndependent.iff_fractionRing ℤ ℚ).1 h1
      simpa using h2.fintype_card_le_finrank
    let p : F →+ Q := π.comp F.subtype.toAddMonoidHom
    have hle : (nsmulAddMonoidHom (α := F) n).range ≤ p.ker := by
      rintro _ ⟨x, rfl⟩
      simpa [p] using h0 x
    have hidx : (nsmulAddMonoidHom (α := F) n).range.index = n ^ Module.finrank ℤ F :=
      AddSubgroup.index_range_nsmul F n
    have hpos : 0 < n ^ Module.finrank ℤ F := pow_pos hn _
    have hdvd : p.ker.index ∣ n ^ Module.finrank ℤ F := hidx ▸ AddSubgroup.index_dvd_of_le hle
    rw [AddSubgroup.index_ker] at hdvd
    have hne : Nat.card p.range ≠ 0 := fun h => by
      rw [h] at hdvd; exact hpos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
    haveI : Finite p.range := Nat.finite_of_card_ne_zero hne
    have hsub : (↑s : Set Q) ⊆ (p.range : Set Q) := fun q hq =>
      ⟨⟨σ q, Submodule.subset_span (by simpa using ⟨q, hq, rfl⟩)⟩, hσ q⟩
    calc s.card = Nat.card (↑s : Set Q) := by simp
      _ ≤ Nat.card p.range := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ n ^ Module.finrank ℤ F := Nat.le_of_dvd hpos hdvd
      _ ≤ n ^ Module.finrank ℚ V := Nat.pow_le_pow_right hn hr
  have finite_card_le {V A Q : Type} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V] [AddCommGroup A] [AddCommGroup Q]
      (f : A →+ V) (hf : Function.Injective f) (π : A →+ Q) (hπ : Function.Surjective π) (n : ℕ) (hn : 0 < n)
      (h0 : ∀ x : A, π (n • x) = 0) : Finite Q ∧ Nat.card Q ≤ n ^ Module.finrank ℚ V := by
    have h := card_finset_le f hf π hπ n hn h0
    have hfin : Finite Q := by
      by_contra hinf
      haveI : Infinite Q := not_finite_iff_infinite.1 hinf
      obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq Q (n ^ Module.finrank ℚ V + 1)
      have := h s
      omega
    refine ⟨hfin, ?_⟩
    haveI := Fintype.ofFinite Q
    rw [Nat.card_eq_fintype_card]
    exact h Finset.univ
  haveI : Module.Finite ℚ (HomE E a b) := Module.Finite.trans E (HomE E a b)
  have : Finite (↥(divLat cA (homAt SA N N')) ⧸ (mulLat cB (homAt SA N N')).comap (divLat cA (homAt SA N N')).subtype) := by
    refine (finite_card_le (divLat cA (homAt SA N N')).subtype.toAddMonoidHom (Submodule.subtype_injective _)
      ((mulLat cB (homAt SA N N')).comap (divLat cA (homAt SA N N')).subtype).mkQ.toAddMonoidHom
      (Submodule.mkQ_surjective _) (cA * cB) (Nat.mul_pos hA hB) ?_).1
    intro x
    refine (Submodule.Quotient.mk_eq_zero _).2 ⟨(cA : 𝓞 E) • (x : HomE E a b), x.2, ?_⟩
    show (cB : 𝓞 E) • (cA : 𝓞 E) • (x : HomE E a b) = (cA * cB) • (x : HomE E a b)
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, mul_nsmul]
  have := Fintype.ofFinite (↥(divLat cA (homAt SA N N')) ⧸ (mulLat cB (homAt SA N N')).comap (divLat cA (homAt SA N N')).subtype)
  unfold kerOf latSum
  simp_rw [finsum_eq_sum_of_fintype, Finset.sum_smul]
  exact Finset.sum_comm

end Local

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem moveScal_dnN (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (u : Pr.Word) (i : ℕ)
    {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} {d : Deco X.E (R.N i) (Pr.vT u) SG} {d' : Deco X.E (R.N (i + 1)) (Pr.vT u) SG'}
    (hd : d.Ok) (hd' : d'.Ok) {P : Pr.vT u} (hP : MoveHyp (Pr.vT u) SG P) (hP' : MoveHyp (Pr.vT u) SG' P) :
    moveScal Ch mu u i d.N (d.dnN P) d'.N (d'.dnN P) = (Pr.T u : X.K) ^ ((R.t + 1) / 2) := by
  unfold moveScal
  rw [Finset.prod_eq_single_of_mem P.1 P.2 fun Q hQ hne => ?_, idxExp_dnN hd P hP.ne, idxExp_dnN hd' P hP'.ne,
    GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.locScal_one_one]
  have hne' : (⟨Q, hQ⟩ : Pr.vT u) ≠ P := fun e => hne (congrArg Subtype.val e)
  rw [idxExp_of_eq (dnN_at_ne hd hP hne'), idxExp_of_eq (dnN_at_ne hd' hP' hne'), GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.locScal_zero_zero]

theorem qOf_pos {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : 0 < qOf P :=
  Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)

theorem ukTerm_of_moveStep : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S)
    (cst : LocCst X (rowSG Pr sel mu)) (A : Amb X) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S →
    MoveStep W Ch sel mu cst A u i (i + 1) → UKTerm W Ch sel mu cst A u i (i + 1) := by
  intro X Pr R W Ch sel S mu cst A u i hX hPr hsel hT hmove SG SG' d fr d' fr' Ξ₀ P y hP hP' hbox
  classical
  obtain ⟨hq, hq2⟩ := T_unif hX hPr u P
  have hU := (above_finite_nonempty hX hPr hP' d').1
  have hD := (below_finite_nonempty hX hPr hP d).1
  have hoff := T_notMem_rowSG mu hPr hsel hT
  have hS : ∀ Q, Q ∈ Sall sel mu u ↔ Q ∈ Pr.vT u ∨ Q ∈ rowSG Pr sel mu := fun Q => by
    unfold Sall
    convert Finset.mem_union
  have hc : ∀ Q : Pr.vT u, (cBof sel mu cst u : 𝓞 X.E) ∈ Q.1.asIdeal := fun Q => by
    unfold cBof
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (T_mem hPr u Q)
  have hA : 0 < cAof sel mu cst := pow_pos (Finset.prod_pos fun Q _ => qOf_pos _) _
  have hB : 0 < cBof sel mu cst u := mul_pos (hPr.T_prime u).pos (pow_pos (Finset.prod_pos fun Q _ => qOf_pos _) _)
  obtain ⟨l0, l1, -, -⟩ := d.2.dnN_spec P hP.ne
  have ag := agreeOff_dnN d.2 hP.ne hq
  have hl : ∀ d₁ ∈ hU.toFinset, term W Ch sel mu cst A u i (i + 1) d fr d₁ fr' Ξ₀ =
      ((Pr.T u : X.K) ^ ((R.t + 1) / 2)) • ker W Ch sel mu cst A u i (i + 1) (d.1.dnN P) fr d'.1.N fr'
        fun x => phiT X.K d.1 d₁.1 x * Ξ₀ x := fun d₁ h₁ => by
    have h₁' : d'.1.IsUp P (Pr.T u : 𝓞 X.E) d₁.1 := hU.mem_toFinset.1 h₁
    have e := up_N hP' hq hq2 d'.2 h₁'
    have ag' := agreeOff_dnN d₁.2 hP'.ne hq
    have hb : InBox (rowSG Pr sel mu) (cAof sel mu cst) (cBof sel mu cst u) d.1.N (d₁.1.dnN P) Ξ₀ := e ▸ hbox
    rw [← moveScal_dnN Ch mu u i d.2 d₁.2 hP hP', e]
    exact hmove _ _ _ _ fr fr' _ ⟨d.2.lat, d.2.uni⟩ ⟨l0, l1⟩ ⟨d₁.2.lat, d₁.2.uni⟩ (e ▸ ⟨d'.2.lat, d'.2.uni⟩) ag ag'
      (inBox_up hS hc d₁.2 (inBox_congr hb (fun _ _ => rfl) fun Q hQ => (ag' Q (hoff Q hQ)).symm))
      (inBox_dn hS hc d.2 d₁.2 hP hP' (inBox_congr hb (fun Q hQ => ag Q (hoff Q hQ)) fun _ _ => rfl))
  have hr : ∀ d₀ ∈ hD.toFinset, term W Ch sel mu cst A u i (i + 1) d₀ fr d' fr' Ξ₀ =
      ker W Ch sel mu cst A u i (i + 1) (d.1.dnN P) fr d'.1.N fr' fun x => phiT X.K d₀.1 d'.1 x * Ξ₀ x := fun d₀ h₀ => by
    have h₀' : d₀.1.IsUp P (Pr.T u : 𝓞 X.E) d.1 := hD.mem_toFinset.1 h₀
    rw [← up_N hP hq hq2 d₀.2 h₀']
    rfl
  rw [finsum_mem_eq_finite_toFinset_sum _ hU, finsum_mem_eq_finite_toFinset_sum _ hD, ← LinearMap.sum_apply, ← LinearMap.sum_apply,
    Finset.sum_congr rfl hl, Finset.sum_congr rfl hr, ← Finset.smul_sum, LinearMap.smul_apply]
  unfold ker
  rw [kerOf_sum _ _ hA hB l0 d'.2.lat, kerOf_sum _ _ hA hB l0 d'.2.lat]
  simp_rw [← Finset.sum_mul, sum_phiT X.K hP hP' hq hq2 d d' hU.toFinset hD.toFinset (fun _ => hU.mem_toFinset)
    (fun _ => hD.mem_toFinset)]

end Main

end GlobalTheory.KerT.UK
end
end

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2
open _root_.Formalism.L2.Col

local instance starHost (B : Base) : StarRing B.host.E := B.fields.starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev dat (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) : Dat (I.rec7 l Z) u :=
  Inh.ofOk B (I.cols l) Z.W Z.V Z.S Z.N Z.G u (I.chIn u a) (I.atIn u a) (I.perIn u a) (I.fmIn l.pr u a) (l.ch u a) (l.lev u a)
    (l.per u a) (l.ovr u a)

instance datFE (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Bd : Dat (I.rec7 l Z) u) : Field Bd.E := Bd.fE

instance datSE (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (Bd : Dat (I.rec7 l Z) u) : StarRing Bd.E := Bd.sE

theorem dat_ch (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) :
    (dat I l Z u a).ch = tw (I.tw l l0 Z) u a := rfl

theorem own_eq (l : I.Laws) (l0 : I.Law0 l) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    own (I.rec7 l Z) u = tw (I.tw l l0 Z) u I.mu0 := rfl

variable {I}

theorem isTerm (h : I.Ok) (u : B.Word) (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    KerIsTerm (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  exact IsTerm.kerIsTerm B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr h.sel_ok
    (h.T_mem u) (h.idx_ok a) hi h.ch_ok h.g_mem ⟨_, _, _, _, h.ch_tied⟩ I.A

theorem kerDil (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    Dat.KerDil (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro b b' d d' P c
  exact kAt_dia B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr h.sel_ok (h.T_mem u)
    (h.idx_ok a) (I.Tp a) I.A (isTerm h u a hi) b b' d d' P c

theorem split (u : B.Word) (a : I.ι) (h : I.Ok) (i : ℕ) :
    Nonempty (Split ((I.atIn u a).A i) (B.T u)) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  obtain ⟨sp, -⟩ := SplitPts.exists_split B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr
    h.sel_ok (h.T_mem u) (h.idx_ok a) (I.Tp a)
  exact ⟨⟨sp.off, sp.off_act, sp.off_lat, sp.ext, sp.surj, sp.off_up, sp.off_dn, sp.off_dia, sp.dia_deco, sp.gam_surj, sp.T_mem,
    sp.T_nsq, sp.nonconj⟩⟩

open Classical in
theorem sees (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) : (dat I l Z u a).Sees :=
  Inh.sees_ofOk B (I.cols l) Z.W Z.V Z.S Z.N Z.G u X (I.chIn u a) (I.atIn u a) (I.perIn u a) (I.fmIn l.pr u a) (l.ch u a)
    (l.lev u a) (l.per u a) (l.ovr u a) rfl (fun _ h => h) (fun _ _ => rfl) (fun _ => decide_eq_true_iff)

local instance moveStepDatNumberField (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) : @NumberField (dat I l Z u a).E (dat I l Z u a).fE :=
  (dat I l Z u a).nE

theorem kerEq (h : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (hth : _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a) (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)))
    {i : ℕ} (hi : i < B.R.m)
    (hk : ∀ c c' F, (dat I l Z u a).ch.C.Kmap i c c' ((dat I l Z u a).ev i F) = (dat I l Z u a).ev (i + 1)
      (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i c.1 c'.1 (((dat I l Z u a).I.S i).rep c)
        (((dat I l Z u a).I.S (i + 1)).rep c') F)) :
    Dat.KerEq (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  refine ⟨fun b b' g g' d d' => ?_, hk⟩
  rcases lt_trichotomy (i + 2) B.R.m with h1 | h1 | h1
  · exact MatLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth h1 b b' g g' d d'
  · exact CoupledLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth h1 b b' g g' d d'
  · exact TopEq.kAt_top_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i I.A
      hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) hth (by omega) b b' g g' d d'

end GlobalTheory.LvT.Built.TrueLaws
