module

public import Formalism.LocalToGlobal.Columns.MtHeckeLoc
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Formalism.LocalToGlobal.Columns.TwQLat

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.MtHeckeSum
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG Formalism.UG.P
open Formalism.L2.DIV (Pl kP St redAt)

section Sum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {v : HeightOneSpectrum (𝓞 F)} {Pb : Pl E} (U : MhlUnif Pb) (k : ℕ)

theorem mhs_cosets_finite (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) : (mhlCosets hc (n := n) v U k).Finite := by
  have hB := mhl_split_bij' hc U k ST SG hov hST hSG hsp hk 1
  refine Set.Finite.of_finite_image ?_ hB.injOn
  rw [hB.image_eq]
  exact DecoSet.heckeSet_finite (conjPrime₂ Pb).ne_bot (conjIdeal_ne_bot (conjPrime₂ Pb).ne_bot) k _

theorem mhs_exists_reps (ST SG : Finset (Pl E)) (hov : IsOver v Pb) (hST : ∀ Q ∈ ST, ¬ IsOver v Q)
    (hSG : ∀ Q ∈ SG, ¬ IsOver v Q) (hsp : conjPrime₂ Pb ≠ Pb) (hk : k ≤ n) :
    ∃ R : Finset (UAd hc n), Set.BijOn (fun η : UAd hc n => (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v)) R
      (mhlCosets hc v U k) := by
  classical
  have hfin := mhs_cosets_finite hc U k ST SG hov hST hSG hsp hk
  refine ⟨hfin.toFinset.image Quotient.out, ?_, ?_, ?_⟩
  · intro η hη
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη
    obtain ⟨c, hc', rfl⟩ := hη
    show (QuotientGroup.mk c.out : UAd hc n ⧸ mhlKv hc n v) ∈ mhlCosets hc v U k
    rw [QuotientGroup.out_eq']
    exact hc'
  · intro η hη η' hη' h
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset] at hη hη'
    obtain ⟨c, -, rfl⟩ := hη
    obtain ⟨c', -, rfl⟩ := hη'
    have h' : c = c' := (QuotientGroup.out_eq' c).symm.trans (h.trans (QuotientGroup.out_eq' c'))
    rw [h']
  · intro c hc'
    refine ⟨c.out, ?_, QuotientGroup.out_eq' c⟩
    simp only [Finset.coe_image, Set.mem_image, Set.Finite.coe_toFinset]
    exact ⟨c, hc', rfl⟩

theorem mhs_decoOf_out (ST SG : Finset (Pl E)) (hST : ∀ Q ∈ ST, ¬ IsOver v Q) (hSG : ∀ Q ∈ SG, ¬ IsOver v Q)
    (x η : UAd hc n) :
    decoOf ST SG ((x * (QuotientGroup.mk η : UAd hc n ⧸ mhlKv hc n v).out : UAd hc n) :
      GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = decoOf ST SG ((x * η : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  obtain ⟨h, e⟩ := QuotientGroup.mk_out_eq_mul (mhlKv hc n v) η
  rw [e, ← mul_assoc, Subgroup.coe_mul]
  exact decoOf_mul_mhlKv ST SG hST hSG _ h.2

end Sum

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.RecChainUnfOne
open NumberField IsDedekindDomain Module Matrix MvPolynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

section Unf

variable {X : Fields}

def frCo (σ₀ : X.K →+* ℂ) (n : ℕ) : FrS X σ₀ n → X.Tau → Matrix (Fin n) (Fin n) ℂ := fun y τ => y.1 τ

def polFn (σ₀ : X.K →+* ℂ) (n : ℕ) : Pol ℂ X.Tau n →ₗ[ℂ] (FrS X σ₀ n → ℂ) := frPolyG (frCo σ₀ n)

theorem polFn_apply (σ₀ : X.K →+* ℂ) (n : ℕ) (Q : Pol ℂ X.Tau n) (y : FrS X σ₀ n) :
    polFn σ₀ n Q y = eval (fun x : X.Tau × Fin n × Fin n => y.1 x.1 x.2.1 x.2.2) Q := rfl

theorem polFn_injective (σ₀ : X.K →+* ℂ) (n : ℕ) : Function.Injective (polFn (X := X) σ₀ n) :=
  frPolyG_inj (frCo σ₀ n) fun f hf => ⟨⟨f, fun τ => (hf τ).isUnit⟩, rfl⟩

end Unf

section BaseChange

variable {K L : Type} [Field K] [Field L] {ι : Type} [Fintype ι] {a b : ℕ}

theorem map_jetLin (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    MvPolynomial.map σ (jetLin J Q) = jetLin (fun m => σ (J m)) (MvPolynomial.map σ Q) := by
  induction Q using MvPolynomial.induction_on' with
  | monomial m c => rw [jetLin_monomial, map_monomial, map_monomial, jetLin_monomial, map_mul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

theorem map_subD (σ : K →+* L) (P : Pol K ι a) :
    MvPolynomial.map σ (subD K ι a b P) = subD L ι a b (MvPolynomial.map σ P) := by
  have h : (MvPolynomial.map σ).comp (subD K ι a b).toRingHom =
      (subD L ι a b).toRingHom.comp (MvPolynomial.map σ) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [subD]
    · intro v
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, subD, aeval_X, map_X]
      split_ifs with hv
      · simp
      · simp
  exact RingHom.congr_fun h P

theorem map_frDet (σ : K →+* L) (τ : ι) : MvPolynomial.map σ (frDet K a τ) = frDet L a τ := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp

theorem map_jetMap (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    MvPolynomial.map σ (jetMap J n P) = jetMap (fun m => σ (J m)) n (MvPolynomial.map σ P) := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply]
  rw [map_jetLin, map_subD, map_mul, map_prod]
  simp only [map_pow, map_frDet]

theorem jetMap_shift (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    jetMap J (fun _ => 0) (P * ∏ τ, frDet K a τ ^ n τ) = jetMap J n P := by
  unfold jetMap
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, pow_zero, Finset.prod_const_one, mul_one]

theorem eval_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    eval (fun x : ι × Fin a × Fin a => y x.1 x.2.1 x.2.2) (frDet ℂ a τ) = (y τ).det := by
  unfold frDet
  rw [RingHom.map_det]
  congr 1
  ext α s
  simp

end BaseChange

section Ev

variable {X : Fields} {a b : ℕ}

end Ev

section Arg

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

variable {W Λ}

end Arg

section Wt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Wt

section Zero

variable {X : Fields}

end Zero

section Rho

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))


open Classical in
def frsD {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (p : DecoSet (E := X.E) (n := n) (ST := ST) (SG := Pr.vGs)) : Frs X.E n (rowSG Pr sel mu) := fun P =>
  if h : P.1 ∈ Pr.vGs then p.1.liftFr ⟨P.1, h⟩ else 1

def repN (u : Pr.Word) (j : ℕ) (c : StCl W Λ u j) : Submodule (𝓞 X.E) (Sp X.E (R.N j)) := ((stepGSD W Λ u j).outSec.rep c).1.N

def repFr (u : Pr.Word) (j : ℕ) (c : StCl W Λ u j) : Frs X.E (R.N j) (rowSG Pr sel mu) := frsD sel mu ((stepGSD W Λ u j).outSec.rep c)

def RhoScal {σ₀ : X.K →+* ℂ} (G : ChainGlob W σ₀) (Am : Amb X) (u : Pr.Word) : Prop :=
  ∀ i, i < R.m → ∀ (c : StCl W Λ u i) (c' : StCl W Λ u (i + 1)),
    σ₀ (rhoK W Λ G.chr u i c : X.K) * σ₀ (rhoK' W Λ G.chr u i c' : X.K) * Am.chiF (R.N i) (R.N (i + 1)) (repN W Λ u i c) (repN W Λ u (i + 1) c') =
      σ₀ (scalK Ch sel mu cst i (repN W Λ u i c) (repFr W Λ sel mu u i c) (repN W Λ u (i + 1) c') (repFr W Λ sel mu u (i + 1) c'))

variable {W Λ Ch sel mu cst}

end Rho

section Xi

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (Am : Amb X) (u : Pr.Word)

abbrev XiFam (Pr : Primes X) (R : Ranks) (u : Pr.Word) : Type :=
  ∀ i, DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := Pr.vGs) → DecoSet (E := X.E) (n := R.N (i + 1)) (ST := Pr.vT u) (SG := Pr.vGs) → HomE X.E (R.N i) (R.N (i + 1)) → X.K

variable (Ξ : XiFam Pr R u)

def xiKer (i : ℕ) (p : DecoSet (E := X.E) (n := R.N i) (ST := Pr.vT u) (SG := Pr.vGs)) (p' : DecoSet (E := X.E) (n := R.N (i + 1)) (ST := Pr.vT u) (SG := Pr.vGs)) :
    (stepGSD W Λ u i).V →ₗ[X.K] (stepGSD W Λ u (i + 1)).V :=
  kerOf (stepC W Ch sel mu cst Am u i (W.lamTrue u (i + 1))) (Sall sel mu u) (cAof sel mu cst) (cBof sel mu cst u)
    p.1.N (frsD sel mu p) p'.1.N (frsD sel mu p') (Ξ i p p')

def XiEquiv : Prop :=
  ∀ i, ClsEq (S := stepGSD W Λ u i) (S' := stepGSD W Λ u (i + 1)) (xiKer W Λ Ch sel mu cst Am u Ξ i)


variable {W Λ Ch sel mu cst Am u Ξ}

end Xi

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.ChainInstS
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

theorem LocE.symmetric_level_bound_le (k₀ rS s : ℕ) : LocE.bd5 k₀ rS s ≤ s := by
  unfold LocE.bd5
  split_ifs <;> omega

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

def symPhiCond (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (k₀ rS r t j c n : ℕ) (M : ℕ → ℕ → E) : Prop :=
  (∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (M p p')) ∧
    (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (M p p' / (q : E))) ∧
    (∀ p', p' < r → redP P (M p' p') = 1 ∧ ∀ p, p < r + (j - 1) * t → p ≠ p' →
      (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (M p p') = 0) ∧
    (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t → redP P (M p p') = 0)

open Classical in
theorem phiGS_eq (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    (k₀ rS r t j c' n' c n : ℕ) (x : HomE E (n' + c') (n + c)) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x =
      if symPhiCond P q k₀ rS r t j c n (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) then
        LocE.lamGvS ψ₀ χ k₀ r t (j - 1) (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x) *
          (LocE.unitV (χ (j - 1)) (Matrix.det (Matrix.of fun s s' : Fin (r + (j - 1) * t) =>
            LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x s.1 s'.1)))⁻¹
      else 0 := rfl

theorem symFPos_fIdx {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fPos k₀ c n (LocE.fIdx k₀ c n p) = p := by
  unfold LocE.fPos LocE.fIdx
  split_ifs <;> omega

theorem symFIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem JGsym_entry (hq0 : (q : E) ≠ 0) {k₀ rS r t n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS ≤ r)
    {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hκ : κ ∈ LocE.JGsym P q k₀ rS r t n c) {p p' : ℕ} (hp : p < n + c) (hp' : p' < r) (hpn : p' < n + c)
    (hb : symIdx k₀ rS p' ≤ symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) :
    IntAt P ((LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p' - if p = p' then 1 else 0) / (q : E)) := by
  have hm := (hκ.2.2 (symIdx k₀ rS p') (symIdx_lt hr hp')).2
  unfold LocE.bvecS LocE.flagS at hm
  rw [symIdxInv_symIdx, ciMem_sclLat] at hm
  have h3 := hm ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩
  have hbd : LocE.bd5 k₀ rS (symIdx k₀ rS p') ≤ symIdx k₀ rS p := by
    rcases hb with hb | ⟨h1, h2⟩
    · exact le_trans (LocE.symmetric_level_bound_le _ _ _) hb
    · subst h1
      unfold LocE.bd5 symIdx
      split_ifs <;> omega
  simp only [symFPos_fIdx hk hp, if_pos hbd] at h3
  unfold LocE.bvecG at h3
  rw [map_smul, Pi.sub_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul] at h3
  have hat : Loc.atN (κ.toLinearMap (Loc.eN E (n + c) (LocE.fIdx k₀ c n p'))) (LocE.fIdx k₀ c n p) =
      κ (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ := by
    unfold Loc.atN
    rw [dite_eq_left (symFIdx_lt hk hp)]
    rfl
  unfold LocE.entB
  rw [hat]
  generalize κ (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ = Xv at h3 ⊢
  have he : Loc.eN E (n + c) (LocE.fIdx k₀ c n p') ⟨LocE.fIdx k₀ c n p, symFIdx_lt hk hp⟩ = if p = p' then 1 else 0 := by
    unfold Loc.eN
    by_cases hpp : p = p'
    · subst hpp
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpp, if_neg]
      intro h
      apply hpp
      have h' : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p' := h
      have h1 := symFPos_fIdx (c := c) hk hp
      have h2 := symFPos_fIdx (c := c) hk hpn
      rw [h'] at h1
      omega
  rw [he] at h3
  have e : ((q : E) ^ (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p) + 1))⁻¹ *
      ((q : E) ^ LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') * Xv -
        (q : E) ^ LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') * (if p = p' then 1 else 0)) =
      (Xv * (q : E) ^ (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p') - LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) -
        if p = p' then 1 else 0) / (q : E) := by
    by_cases hpp : p = p'
    · subst hpp
      rw [if_pos rfl, sub_self, zpow_zero, zpow_add₀ hq0, zpow_one]
      have hA := zpow_ne_zero (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) hq0
      field_simp
    · rw [if_neg hpp, zpow_sub₀ hq0, zpow_add₀ hq0, zpow_one]
      have hA := zpow_ne_zero (LocE.scE n (fun i => i + 1) (LocE.fIdx k₀ c n p)) hq0
      field_simp
      ring
  rw [← e]
  exact h3

theorem JGsym_red (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) {k₀ rS r t n c : ℕ} (hk : k₀ ≤ n) (hr : k₀ + rS ≤ r)
    {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hκ : κ ∈ LocE.JGsym P q k₀ rS r t n c) {p p' : ℕ} (hp : p < n + c) (hp' : p' < r) (hpn : p' < n + c)
    (hne : p ≠ p') (hb : symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) :
    redP P (LocE.entB q k₀ c n c n (fun i => i + 1) (fun i => i + 1) κ.toLinearMap p p') = 0 := by
  have h := JGsym_entry hq0 hk hr hκ hp hp' hpn (hb.imp le_of_lt id)
  rw [if_neg hne, sub_zero] at h
  exact (ciRed_of_div hq hq0 h).2

theorem phiGS_col (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ rS r t j c' n' c n : ℕ} (hkr : k₀ < r) (x : HomE E (n' + c') (n + c)) (h : LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x ≠ 0)
    {p : ℕ} (hp : p < n + c) :
    IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p k₀) ∧
      redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p k₀) = if p = k₀ then 1 else 0 := by
  classical
  rw [phiGS_eq] at h
  have hC := (ite_ne_right_iff.1 h).1
  have hka : k₀ < r + (j - 1) * t := Nat.lt_of_lt_of_le hkr (Nat.le_add_right _ _)
  refine ⟨hC.1 p k₀ hp hka, ?_⟩
  by_cases hpk : p = k₀
  · rw [if_pos hpk, hpk]
    exact (hC.2.2.1 k₀ hkr).1
  · rw [if_neg hpk]
    by_cases hpa : p < r + (j - 1) * t
    · refine (hC.2.2.1 k₀ hkr).2 p hpa hpk (Or.inr ?_)
      unfold symIdx
      by_cases h0 : rS = 0
      · subst h0
        by_cases hlt : p < k₀
        · exact Or.inr ⟨rfl, hlt⟩
        · left
          split_ifs <;> omega
      · left
        split_ifs <;> omega
    · exact (ciRed_of_div hq hq0 (hC.2.1 p k₀ (Nat.le_of_not_lt hpa) hp hka)).2

theorem symEntB_join_col (q : ℕ) {k₀ n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0)
    (x₀ : HomE E n' n) (y' : Sp E n) {p : ℕ} (hp : p < n) :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (joinCol (c' := c') (c := c) x₀ y') p k₀ = (q : E) * y' ⟨p, hp⟩ := by
  subst hc' hc
  have f1 : LocE.fIdx k₀ 1 n' k₀ = n' := by
    unfold LocE.fIdx
    rw [if_neg (lt_irrefl _), if_pos (by omega)]
    omega
  have f2 : LocE.fIdx k₀ 0 n p = p := ciFIdx (Or.inl rfl) (by omega)
  unfold LocE.entB joinCol atNL
  rw [f1, f2, ciScE_lt _ hp, dite_eq_left (show n' < n' + 1 by omega)]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [ciAtN_inX hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (n' + 1) n') = (0 : Fin n' → E) := by
    funext i
    show Loc.eN E (n' + 1) n' (Fin.castAdd 1 i) = 0
    unfold Loc.eN
    simp only [Fin.val_castAdd]
    rw [if_neg (by have := i.2; omega)]
  have e2 : Loc.eN E (n' + 1) n' ⟨n', by omega⟩ = 1 := by
    unfold Loc.eN
    rw [if_pos rfl]
  have e3 : LocE.scE n' (fun i => i + 1) n' = 1 := by simp [LocE.scE]
  rw [e1, e2, e3, map_zero, Pi.zero_apply, zero_add, one_mul, sub_zero, zpow_one, mul_comm]

end Loc

section Glob

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem psiAt_sym {m2 : ℕ} (hc' : cOf R m2 = 1) (hc : cOf R (m2 + 1) = 0) (hs : cst.sharp = true) (P : rowSG Pr sel mu)
    (hP : P.1 ∈ Pr.vGs) (x₀ : HomE X.E (R.N m2) (R.N (m2 + 1))) (y' : Sp X.E (R.N (m2 + 1)))
    (h : PsiAt Ch sel mu cst m2 P 1 x₀ y' ≠ 0) (i : Fin (R.N (m2 + 1))) :
    IntAt P.1 ((qOf P.1 : X.E) * y' i) ∧ redP P.1 ((qOf P.1 : X.E) * y' i) = if i.1 = R.k then 1 else 0 := by
  classical
  unfold PsiAt omPhi at h
  rw [ciOm_one] at h
  have h' := right_ne_zero_of_mul h
  unfold PhiAt at h'
  rw [if_pos hP, if_pos hs] at h'
  have hkr : R.k < R.r := by
    have := R.two_le_m
    unfold Ranks.r
    omega
  have hi : i.1 < R.N (m2 + 1) + cOf R (m2 + 1) := Nat.lt_of_lt_of_le i.2 (Nat.le_add_right _ _)
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := Nat.cast_ne_zero.2 (qOf_pos P.1).ne'
  have a := phiGS_col (xqQ_mem P.1) hq0 _ _ hkr _ h' hi
  rw [symEntB_join_col _ hc' hc x₀ y' i.2] at a
  exact a

end Glob

end Formalism.L2.Col
end
end

section -- merged from Formalism.LocalToGlobal.Columns.TwQExact
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP underPl St)
open Formalism.UG Formalism.HermitianLatticesTheory

section QExact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}

def FrExact (q : QLoc hc n Q Θ) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (p : DecoF E n ST SG Q) : Prop :=
  decoOf ST SG x = p.deco ∧ ∀ P : Q, q.at P x = bc (q.phi P) (qGL n (p.fr P))

theorem FrExact.over {q : QLoc hc n Q Θ} {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {p : DecoF E n ST SG Q} (h : FrExact q x p) :
    FrOver q x p := by
  refine ⟨h.1, fun P => ?_⟩
  rw [h.2 P, inv_mul_cancel]
  exact (q.U P).one_mem

variable {H : Subgroup (GLG (E := E) (n := n) (SG := SG))}

def recClsFy (q : QLoc hc n Q Θ) (hF : FrLat ST SG q) (hE : FrExists (n := n) ST SG Q)
    (s : DecoFCl (K := K) n ST SG Q H Θ → DecoF E n ST SG Q) (hs : ∀ c, (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q H Θ) = c)
    (y : DecoFCl (K := K) n ST SG Q H Θ → UAd hc n) (hy : ∀ c, FrOver q (y c).1 (s c)) :
    RecClsF hc n ST SG Q H q s where
  y c := y c
  y_bij := by
    constructor
    · intro c c' h
      have hr := Quotient.exact' h
      obtain ⟨h0, hh, k, hk, e⟩ := DoubleCoset.rel_iff.1 hr
      obtain ⟨γ, hγ⟩ := Formalism.L2.DIV.ratEl_surjective (⟨h0, hh⟩ : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E))
      have hh' : ((h0 : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) = Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) :=
        (congrArg (fun z : Formalism.L2.DIV.UQ hc (1 : Matrix (Fin n) (Fin n) E) =>
          ((z : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) hγ).symm
      have hk' : ((k : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ ∈ levUQ hc n ST SG Q H q :=
        Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.1 hk)
      have e' : ((y c' : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) (γ : GL (Fin n) E) * ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            (((⟨_, hk'⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)))⁻¹ := by
        have e2 := congrArg (fun z : UAd hc n => (z : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))) e
        simp only [Subgroup.coe_mul] at e2
        rw [e2, hh', inv_inv]
      obtain ⟨a, -, -, ha⟩ := qdf_orbit_of_rel H q (hy c) (hy c') γ ⟨_, hk'⟩ e'
      rw [← hs c, ← hs c']
      exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨a⁻¹, by show a⁻¹ • s c' = s c; rw [ha, inv_smul_smul]⟩)
    · intro Qc
      induction Qc using Quotient.inductionOn' with
      | h x =>
        obtain ⟨p, hp⟩ := qdf_over_exists q hF hE x
        refine ⟨Quotient.mk'' p, ?_⟩
        obtain ⟨a, ha⟩ := MulAction.orbitRel_apply.1 (Quotient.exact (hs (Quotient.mk'' p)))
        have ha' : a • p = s (Quotient.mk'' p) := ha
        have hx' : FrOver q (y (Quotient.mk'' p)).1 (a • p) := by
          rw [ha']; exact hy _
        obtain ⟨γ, κ, -, e⟩ := qdf_rel_of_orbit H q a hp hx'
        exact (qdf_mk_eq H q γ κ e).symm
  y_lat c x := by
    have h := decoRaw_carries hc n ST SG (y c).2 x
    rw [← rlc_decoOf_val hc n ST SG (y c).2, (hy c).1] at h
    exact h
  stabI c := qdStab H (s c)
  stabI_inj c := by
    intro a b hab
    have h1 : a.1.1 = b.1.1 := by rw [← qdf_ratHom_stab (hc := hc) H (s c) a, ← qdf_ratHom_stab (hc := hc) H (s c) b, hab]
    have ha := qdf_stab_deco H (s c) a
    have hb := qdf_stab_deco H (s c) b
    have hab' : ((a.1.1, (a.1.2.1 : GLG (E := E) (n := n) (SG := SG))) : UF E n × GLG (E := E) (n := n) (SG := SG)) • (s c).deco = (s c).deco := ha
    have hbb' : ((b.1.1, (b.1.2.1 : GLG (E := E) (n := n) (SG := SG))) : UF E n × GLG (E := E) (n := n) (SG := SG)) • (s c).deco = (s c).deco := hb
    have h2 := DecoSet.stab_fst_injective (s c).deco hab' hbb' h1
    have h3 : a.1.2.2 = b.1.2.2 := by
      apply Subtype.ext
      funext P
      apply Subtype.ext
      rw [qdf_stab_fr H (s c) a P, qdf_stab_fr H (s c) b P, h1]
    exact Subtype.ext (Prod.ext h1 (Prod.ext (Subtype.ext (congrArg Prod.snd h2)) h3))
  stabI_range c γ hγ := by
    constructor
    · rintro ⟨a, ha⟩
      have hx := hy c
      have hx' : FrOver q (y c).1 (a.1 • s c) := by rw [a.2]; exact hx
      obtain ⟨γ', κ, h1, e⟩ := qdf_rel_of_orbit H q a.1 hx hx'
      have hγ' : γ' = ⟨γ, hγ⟩ := by
        rw [← ha]
        exact (ratHom_bijective hc n).1 (h1.trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
      refine ⟨κ.1, κ.2, ?_⟩
      show ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * κ.1 *
        ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ = _
      have e' : Formalism.UG.bc (iA F E) (γ' : GL (Fin n) E) = ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          κ.1 * ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ :=
        eq_mul_inv_of_mul_eq (eq_mul_inv_iff_mul_eq.1 e).symm
      rw [← e', hγ']
    · rintro ⟨k, hk, e⟩
      have e' : ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * k *
          ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) := e
      have e2 : ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
          Formalism.UG.bc (iA F E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) E) *
            ((y c : UAd hc n) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
            ((⟨k, hk⟩ : levUQ hc n ST SG Q H q) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ := by
        rw [← e']; group
      obtain ⟨a, ha1, -, ha⟩ := qdf_orbit_of_rel H q (hy c) (hy c) ⟨γ, hγ⟩ ⟨k, hk⟩ e2
      refine ⟨⟨a, ha.symm⟩, ?_⟩
      apply (ratHom_bijective hc n).1
      rw [qdf_ratHom_stab (hc := hc) H (s c) ⟨a, ha.symm⟩, ha1]
  stabI_lat c a x := by
    have h := stabRat_lat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ x
    have e : stabRat hc n ST SG H (s c).deco ⟨_, qdf_stab_deco H (s c) a⟩ = qdStab H (s c) a :=
      (ratHom_bijective hc n).1 ((rlc_ratHom_stabRat hc n ST SG H _ _).trans (qdf_ratHom_stab (hc := hc) H (s c) a).symm)
    rw [e] at h
    exact h

end QExact

end Formalism.L2.Col
end
end
