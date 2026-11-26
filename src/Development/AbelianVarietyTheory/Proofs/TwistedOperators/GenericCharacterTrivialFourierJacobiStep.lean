module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdealMembershipOffModulus
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdealMembershipOffModulus
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.DepthIdeal

open GlobalTheory.SeeSaw (FI idV dI)
open GlobalTheory.FinPlLoc (idem)
open Formalism.IndefR.Fin

variable {D : D7}

theorem phiE_one (v : GlobalTheory.FinPl.Pl D) : phiE (D := D) v 1 = idem D (· = v) := by
  classical
  have h : sglV v (1 : v.adicCompletion D.host.F) = GlobalTheory.FinPlLoc.ePl D (· = v) := by
    apply af_ext; intro u
    rw [GlobalTheory.FinPlLoc.evalV_ePl]
    by_cases hu : u = v
    · subst hu; rw [sglV_same, if_pos rfl]
    · rw [sglV_ne v _ hu, if_neg hu]
  unfold idem
  rw [← h]
  rfl

variable {T : Type} {L : LevCh D T}

theorem belowPl_w (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) : belowPl (P.w v) = v := by
  conv_rhs => rw [← P.under_w hv]
  rfl

theorem exists_idem (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) {e : AE D} (he : IsIdemSum e P.W0) :
    ∃ f : AE D, Formalism.L2.NTheta.IsIdemAt f (P.w v) ∧ (1 - e) * idem D (· = v) = cA D f := by
  classical
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have hmem : ∀ PP, PP ∈ P.W0 ↔ ∃ u ∈ P.S0, P.w u = PP := fun PP => by
    unfold Places.W0
    convert Finset.mem_image
  have hw : P.w v ∈ P.W0 := (hmem _).2 ⟨v, hv, rfl⟩
  have heps : ∀ u ∈ P.S0, es (P.w u) + cA D (es (P.w u)) = phiE u 1 := fun u hu => by
    have := below_of_idemAt (hes _ ((hmem _).2 ⟨u, hu, rfl⟩))
    rwa [belowPl_w P hu] at this
  have hfix : ∀ u ∈ P.S0, es (P.w u) * phiE u 1 = es (P.w u) := fun u hu => by
    have h := hes _ ((hmem _).2 ⟨u, hu, rfl⟩)
    rw [← heps u hu, mul_add, h.1.1, h.1.2.1, add_zero]
  refine ⟨es (P.w v), hes _ hw, ?_⟩
  have hsum : (∑ PP ∈ P.W0, es PP) * phiE v 1 = es (P.w v) := by
    rw [Finset.sum_mul, Finset.sum_eq_single (P.w v), hfix v hv]
    · intro PP hPP hne
      obtain ⟨u, hu, rfl⟩ := (hmem _).1 hPP
      have huv : u ≠ v := fun h => hne (h ▸ rfl)
      rw [← hfix u hu, mul_assoc, phiE_orth huv, mul_zero]
    · intro h; exact absurd hw h
  rw [← phiE_one, sub_mul, one_mul, hsum, ← heps v hv, add_sub_cancel_left]

theorem exists_modul_conj (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    ∃ x ∈ P.modul sc, ∃ y : 𝓞 D.host.E, y ∉ (P.w v).asIdeal ∧ (y : D.host.E) = star (x : D.host.E) := by
  classical
  have hu : ∀ u ∈ P.S0, ∃ a ∈ (P.w u).asIdeal, ∃ b : 𝓞 D.host.E, b ∉ (P.w v).asIdeal ∧
      (b : D.host.E) = star (a : D.host.E) := by
    intro u hu
    by_cases huv : u = v
    · subst huv
      obtain ⟨f, hf⟩ := P.w_split u hu
      have hs := idemAt_split hf
      unfold Formalism.IndefR.Lev.IsConjPl at hs
      push Not at hs
      obtain ⟨a, ha, hb⟩ := hs
      exact ⟨a, ha, starO a, fun h => hb _ h rfl, rfl⟩
    · have hne : ¬ u.asIdeal ≤ v.asIdeal := fun hle =>
        huv (HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle))
      obtain ⟨t, htu, htv⟩ := Set.not_subset.1 hne
      refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t, ?_, ?_⟩
      · have : t ∈ (belowPl (P.w u)).asIdeal := by rw [belowPl_w P hu]; exact htu
        exact this
      · intro h
        apply htv
        have : t ∈ (belowPl (P.w v)).asIdeal := h
        rwa [belowPl_w P hv] at this
      · rw [algebraMap_O]
        exact (D.sp.cm.sig.commutes _).symm
  choose! a ha b hb hab using hu
  refine ⟨∏ u ∈ P.S0, a u ^ P.depth sc u, ?_, ∏ u ∈ P.S0, b u ^ P.depth sc u, ?_, ?_⟩
  · exact Ideal.prod_mem_prod fun u hu => Ideal.pow_mem_pow (ha u hu) _
  · intro hmem
    obtain ⟨u, hu, hmem'⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (P.w v).isPrime)).1 hmem
    exact hb u hu ((P.w v).isPrime.mem_of_pow_mem _ hmem')
  · change algebraMap (𝓞 D.host.E) D.host.E _ = star (algebraMap (𝓞 D.host.E) D.host.E _)
    rw [map_prod, map_prod, star_prod]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [map_pow, map_pow, star_pow]
    exact congrArg (· ^ P.depth sc u) (hab u hu)

theorem idV_le_dI (P : Places L) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) :
    idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v ≤ idV (dI D) v := by
  refine GlobalTheory.StairLine.idV_le_of_loc fun z hz => ⟨_, GlobalTheory.AAUnit.absNorm_cmIdeal_not_mem_gridPlaces P hv, ?_⟩
  have e : dI D = D.host.AA * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) := by
    unfold dI; ring
  have e2 : algebraMap D.host.F D.host.E ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.F) =
      ((Ideal.absNorm D.host.ccK : ℕ) : D.host.E) := by
    rw [← algebraMap_O, map_natCast]; rfl
  rw [e, e2]
  exact FractionalIdeal.mul_mem_mul (GlobalTheory.HostClear.absNorm_mem_AA D) hz

theorem compl_mem (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D} (hv : v ∈ P.S0) {e : AE D} (he : IsIdemSum e P.W0)
    (𝔞 : FI D) {s : AE D} (hs : s ∈ idV (𝔞 * ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) v) :
    (1 - e) * idem D (· = v) * s ∈ idV 𝔞 v := by
  obtain ⟨f, hf, hfe⟩ := exists_idem P hv he
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_modul_conj P sc hv
  have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  have hx0 : (x : D.host.E) ≠ 0 := by
    intro h
    apply hy0
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    rw [map_zero]
    change (y : D.host.E) = 0
    rw [hxy, h, star_zero]
  have hm0 : ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 (P.modul_ne_bot sc)
  have h1 : idem D (· = v) * incA D x ∈ idV ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) v := by
    unfold idem
    rw [mul_comm, GlobalTheory.SeeSaw.IdVMul.incA_mul_tmul, mul_one]
    refine GlobalTheory.SeeSaw.IdVMul.gen_mem (GlobalTheory.FinPlLoc.ePl_int _) (fun w hw => ?_)
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨x, hx, rfl⟩)
    rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw]
  have h2 := GlobalTheory.SeeSaw.IdVMul.mul_mem_idV h1 hs
  rw [mul_left_comm, mul_inv_cancel₀ hm0, mul_one] at h2
  have hint : finPart D (cA D f * incA D (x : D.host.E)⁻¹) ∈ intAE D := by
    have h3 : finPart D (f * incA D (y : D.host.E)⁻¹) ∈ intAE D := not_not.1 (mt (hf.2 y hy0).2 hy)
    have h4 := cF_int h3
    rwa [← finPart_cA, cA_mul_incA, hxy, star_inv₀, star_star] at h4
  have h5 : cA D f * incA D (x : D.host.E)⁻¹ ∈ idV (1 : FI D) v := by
    refine (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).2 ⟨?_, hint⟩
    rw [← hfe]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _))
  have h6 := GlobalTheory.SeeSaw.IdVMul.mul_mem_idV h5 h2
  rw [one_mul, ← hfe] at h6
  have e1 : incA D (x : D.host.E)⁻¹ * incA D x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  have e2 := GlobalTheory.FinPlLoc.idem_mul_self (D := D) (· = v)
  have e3 : (1 - e) * idem D (· = v) * incA D (x : D.host.E)⁻¹ * (idem D (· = v) * incA D x * s) =
      (1 - e) * idem D (· = v) * s := by
    calc _ = (1 - e) * (idem D (· = v) * idem D (· = v)) * (incA D (x : D.host.E)⁻¹ * incA D x) * s := by ring
      _ = _ := by rw [e1, e2, mul_one]
  rwa [e3] at h6

theorem mem_dI_of_half : All fun {D} _ _ _ {G} _ _ => ∀ v ∈ G.pl.S0, ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ s ∈ idAt D (· = v), s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D * ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → e * s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v → s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
  intro D _ T L μ0 _ sc G W M _ v hv e he s hs h1 h2
  have hA := idV_le_dI G.pl hv h2
  have hB := compl_mem G.pl sc hv he (dI D) h1
  rw [mul_assoc, (GlobalTheory.FinPlLoc.mem_idAt_iff _ s).1 hs] at hB
  have := add_mem hA hB
  rwa [← add_mul, add_sub_cancel, one_mul] at this

end GlobalTheory.DepthIdeal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdealMembershipOffModulusStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_membership_off_modulus : All fun {D} _ _ _ {G} _ _ => ∀ v ∈ G.pl.S0, ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ s ∈ idAt D (· = v), s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D * ((G.modul : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v → e * s ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar) v → s ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
  first | exact @GlobalTheory.DepthIdeal.mem_dI_of_half | exact GlobalTheory.DepthIdeal.mem_dI_of_half | (intros; apply GlobalTheory.DepthIdeal.mem_dI_of_half <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemIdVOfLines
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem pX_xLast_castSucc {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k l : Fin σ) :
    (dW.pX ⬝ xLast dW z) k l.castSucc = (1 : Mx D σ σ) k l := by
  rw [← dW.pX_jX]
  simp only [Matrix.mul_apply, SuppShift.xLast_castSucc]

theorem pX_xLast_last {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (k : Fin σ) :
    (dW.pX ⬝ xLast dW z) k (Fin.last σ) = 0 := by
  have h : (dW.pX ⬝ xLast dW z) k (Fin.last σ) = ((dW.pX ⬝ dW.j0) *ᵥ ratV z) k := by
    rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, SuppShift.xLast_last]
  rw [h, dW.pX_j0, Matrix.zero_mulVec, Pi.zero_apply]

theorem pX_xLast_mul_apply {W W₀ : HSp D} {σ : ℕ} (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E)
    (N : Mx D (σ + 1) (σ + 1)) (k : Fin σ) (j : Fin (σ + 1)) :
    (dW.pX ⬝ (xLast dW z ⬝ N)) k j = N k.castSucc j := by
  rw [← Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_castSucc, pX_xLast_last, zero_mul, add_zero]
  simp only [pX_xLast_castSucc, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem psiE_idem_entry {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V V₀ W W₀ : HSp D} {σ : ℕ}
    (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (z : Fin W₀.rank → D.host.E) (LV : Lat V) (LW : Lat W) (LW₀ : Lat W₀)
    {v : Pl D} (hm : MonoAt dW LW LW₀ v) (hp : PrimAt ψ dV LV v) (hc : ColsAt dV (xLast dW z) LV LW v)
    (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ latA W LW (· = v))
    (i j : Fin (σ + 1)) (hij : j.1 = i.1 + 1) : psiE ψ (idem D (· = v) * N i j) = 1 := by
  obtain ⟨-, -, -, -, -, -, f7⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D ψ hψ v
  have hiσ : i.1 < σ := by have := j.2; omega
  set i' : Fin σ := ⟨i.1, hiσ⟩ with hi'
  have hii : i'.castSucc = i := Fin.ext rfl
  set s := idem D (· = v) * N i j with hsdef
  have hs : s ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have key : ∀ a : AE D, colMul dV.jX j a ∈ latV V LV (· = v) → colMul dV.jX i (s * a) ∈ latV V LV (· = v) := by
    intro a ha
    have haA : a ∈ idAt D (· = v) := GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul dV ha
    have h1 := hY _ ha
    rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
    have hb : N i j * a ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ haA
    have h2 : colMul (xLast dW z) i (N i j * a) ∈ latA W LW (· = v) := by
      refine (f7 W LW _).2 ⟨fun k => Ideal.mul_mem_right _ _ hb, fun t ht => ?_⟩
      have h3 := ((f7 W LW _).1 h1).2 t ht
      have h4 := ((hm _).1 h3).1 i'
      have e1 : (dW.pX *ᵥ (t • colMul (xLast dW z ⬝ N) j a)) i' = t * (a * N i j) := by
        rw [Matrix.mulVec_smul, PsiUnit.mulVec_colMul, Pi.smul_apply, smul_eq_mul, colMul,
          pX_xLast_mul_apply dW z N, hii]
      rw [e1] at h4
      convert h4 using 1
      ext k
      simp [colMul, ← hii, SuppShift.xLast_castSucc, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    have h5 := (hc i (N i j * a) hb).2 h2
    have e2 : s * a = N i j * a := by
      rw [hsdef, mul_comm (idem D (· = v)), mul_assoc, (mem_idAt_iff _ a).1 haA]
    rwa [e2]
  have h6 := (hp i j hij s hs).1 key (idem D (· = v)) (idem_mem_intAt _)
  rwa [hsdef, mul_assoc, mul_comm (N i j), ← mul_assoc, idem_mul_self] at h6

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_mem_idV_of_lines {V V₀ W W₀ : HSp D} {σ : ℕ} (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ)
    (z : Fin W₀.rank → D.host.E) (LV : Lat V) (A : AddSubgroup (Fin W.rank → AE D)) (𝔟V 𝔟W : GlobalTheory.SeeSaw.FI D) {v : Pl D}
    (k : Fin σ) (j : Fin (σ + 1)) (hV : ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, colMul dV.jX j a ∈ latV V LV (· = v))
    (hW : ∀ y ∈ A, (dW.pX *ᵥ y) k ∈ GlobalTheory.SeeSaw.idV 𝔟W v) (N : Mx D (σ + 1) (σ + 1))
    (hY : ∀ y ∈ latV V LV (· = v), (xLast dW z ⬝ N ⬝ dV.pX) *ᵥ y ∈ A) :
    ∀ a ∈ GlobalTheory.SeeSaw.idV 𝔟V v, N k.castSucc j * a ∈ GlobalTheory.SeeSaw.idV 𝔟W v := by
  intro a ha
  have h1 := hY _ (hV a ha)
  rw [PsiUnit.mulVec_colMul, Matrix.mul_assoc, dV.pX_jX, Matrix.mul_one] at h1
  have h2 := hW _ h1
  rwa [PsiUnit.mulVec_colMul, colMul, pX_xLast_mul_apply dW z N k j, mul_comm] at h2

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

variable {D : D7}

theorem span_neg (x : D.host.E) : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (-x) = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x :=
  (FractionalIdeal.spanSingleton_eq_spanSingleton).2 ⟨-1, by simp⟩

theorem line_ratio (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    I * (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) *
      ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1 + 1)))⁻¹ * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  have hs : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x ≠ 0 := by
    rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
  rw [pow_succ x (k + 1), ← FractionalIdeal.spanSingleton_mul_spanSingleton, pow_succ 𝔞' (k + 1)]
  have h1 : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (x ^ (k + 1)) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact pow_ne_zero _ hx
  have h2 : 𝔞' ^ (k + 1) ≠ 0 := pow_ne_zero _ h𝔞'
  have h3 : 𝔞 ^ n ≠ 0 := pow_ne_zero _ h𝔞
  field_simp

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

variable {D : D7}

theorem line_ratio' (I 𝔞 𝔞' : GlobalTheory.SeeSaw.FI D) (h𝔞 : 𝔞 ≠ 0) (h𝔞' : 𝔞' ≠ 0) (x : D.host.E) (hx : x ≠ 0) (n k : ℕ) :
    FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1))⁻¹) * I *
      (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x ^ (k + 1 + 1))⁻¹) * (𝔞 ^ n * (𝔞' ^ (k + 1 + 1))⁻¹))⁻¹ =
      I * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ x * 𝔞' := by
  rw [← FractionalIdeal.spanSingleton_inv, ← FractionalIdeal.spanSingleton_inv]
  rw [← line_ratio I 𝔞 𝔞' h𝔞 h𝔞' x hx n k]
  ring

end GlobalTheory.UniStepFB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledLatticeCompletionSupportedInvIdealSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledLatticeCompletionSupportedInvIdealSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.LatMulAt

variable {D : D7}

theorem exists_int_of_mem_inv {I : GlobalTheory.SeeSaw.FI D} {a t : D.host.E} (ha : a ∈ I) (ht : t ∈ I⁻¹) :
    ∃ r : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E r = t * a := by
  have h1 : t * a ∈ I⁻¹ * I := FractionalIdeal.mul_mem_mul ht ha
  rw [FractionalIdeal.inv_eq, mul_comm] at h1
  exact (FractionalIdeal.mem_one_iff _).1 (FractionalIdeal.mul_one_div_le_one h1)

theorem gen_mul (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D)
    {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F)
    (hαv : ∀ w, ¬ w = v → evalV D.host.F w α = 0) (hβv : ∀ w, w ≠ v → evalV D.host.F w β = 0)
    {a t : D.host.E} (ha : a ∈ I) (ht : t ∈ I⁻¹) {x : Fin S.rank → D.host.E} (hx : x ∈ L) :
    (pairA D.host.F 0 β ⊗ₜ[D.host.F] t) • (fun i => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i)) ∈
      latV S L (· = v) := by
  obtain ⟨r, hr⟩ := exists_int_of_mem_inv ha ht
  refine AddSubgroup.subset_closure ⟨β * α, ?_, ?_, 1, rfl, r • x, L.smul_mem r hx, ?_⟩
  · intro w
    rw [map_mul]
    exact mul_mem (hβ w) (hα w)
  · intro w hw
    rw [map_mul, hβv w hw, zero_mul]
  · funext i
    rw [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, ← GlobalTheory.FinPlLoc.pairA_mul, Pi.smul_apply,
      Algebra.smul_def, hr, one_mul, mul_assoc]

theorem latMul_inv_smul : ∀ {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (y : Fin S.rank → AE D), y ∈ GlobalTheory.FinPl.latMul S {a | a ∈ I} L (· = v) → (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ GlobalTheory.SeeSaw.idV I⁻¹ v, s • y ∈ latV S L (· = v) := by
  intro D S L I v y hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, hαv, a, ha, x, hx, rfl⟩ := hy
    refine ⟨fun i => GlobalTheory.FinPlLoc.pair_mem_idAt _ α hαv _, fun s hs => ?_⟩
    induction hs using AddSubgroup.closure_induction with
    | mem s hs =>
      obtain ⟨β, hβ, hβv, t, ht, rfl⟩ := hs
      exact gen_mul S L I v hα hβ hαv hβv ha ht hx
    | zero => rw [zero_smul]; exact zero_mem _
    | add s s' _ _ h h' => rw [add_smul]; exact add_mem h h'
    | neg s _ h => rw [neg_smul]; exact neg_mem h
  | zero => exact ⟨fun i => zero_mem _, fun s _ => by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    exact ⟨fun i => add_mem (hy.1 i) (hz.1 i), fun s hs => by rw [smul_add]; exact add_mem (hy.2 s hs) (hz.2 s hs)⟩
  | neg y _ hy =>
    exact ⟨fun i => neg_mem (hy.1 i), fun s hs => by rw [smul_neg]; exact neg_mem (hy.2 s hs)⟩

end GlobalTheory.LatMulAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledLatticeCompletionSupportedInvIdealSmulStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledLatticeCompletion_supported_invIdeal_smul : ∀ {D : D7} (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (I : GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (y : Fin S.rank → AE D), y ∈ GlobalTheory.FinPl.latMul S {a | a ∈ I} L (· = v) → (∀ i, y i ∈ idAt D (· = v)) ∧ ∀ s ∈ GlobalTheory.SeeSaw.idV I⁻¹ v, s • y ∈ latV S L (· = v) := by
  first | exact @GlobalTheory.LatMulAt.latMul_inv_smul | exact GlobalTheory.LatMulAt.latMul_inv_smul | (intros; apply GlobalTheory.LatMulAt.latMul_inv_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialFourierJacobiStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.SeeSaw
open scoped Pointwise

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem lineV (F : GlobalTheory.Asc.Frames G) (hF : Std F) (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (p : Fin ρ) (v : Pl D) (a : AE D)
    (ha : a ∈ idV (FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)) v) :
    colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  obtain ⟨_hc, he, -⟩ := hF.hJ ρ h
  have e1 : colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
      (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
    funext k
    simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]
  rw [e1]
  have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  rw [e2]
  exact (GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega)
    (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v a).2 ha


set_option maxHeartbeats 1000000 in
theorem lineW (F : GlobalTheory.Asc.Frames G) (hF : Std F) (σ : ℕ) (h' : 2 * σ + 2 ≤ D.R.m) (v : Pl D)
    (hm : MonoAt (F.dB σ h') (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v) (p : Fin σ) (I : FI D) (hI : I ≠ 0)
    (y : Fin (G.V (.grid (2 * σ + 2) 0)).rank → AE D) (hy : y ∈ latMul _ {a | a ∈ I} (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) :
    ((F.dB σ h').pX *ᵥ y) p ∈ idV (FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p) * I) v := by
  obtain ⟨_hc, he, -⟩ := hF.hB σ h'
  obtain ⟨hsupp, hsm⟩ := GlobalTheory.T.scaledLatticeCompletion_supported_invIdeal_smul _ _ I v y hy
  have hc : ((F.dB σ h').pX *ᵥ y) p ∈ idAt D (· = v) := by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hsupp k)
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (by
      unfold Places.modulBar
      intro h0
      apply G.pl.modul_ne_bot sc
      have h1 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
      simpa using h1)
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hB : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hb : FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p) ≠ 0 :=
    mul_ne_zero (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)))
      (mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)))
  have key := (GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v I⁻¹ _ (inv_ne_zero hI) hb _ hc).1 fun s hs => by
    have h1 := ((hm _).1 (hsm s hs)).1 p
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h1
    have e1 : colMul (F.dB σ h').jX p (s * ((F.dB σ h').pX *ᵥ y) p) = fun k => s * ((F.dB σ h').pX *ᵥ y) p *
        incA D ((-D.host.xi0) ^ (p.1 + 1) * (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]
    rw [e1] at h1
    have e2 : G.Λ (.grid (2 * σ + 2) 0) = (G.colDec (2 * σ + 2) (by omega) h').lat (G.Λ (.core (2 * σ + 2)))
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)) := G.sp.colLat (2 * σ + 2) (by omega) h'
    rw [e2] at h1
    rw [mul_comm (((F.dB σ h').pX *ᵥ y) p) s]
    exact (GlobalTheory.StairLine.line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega)
      (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v _).1 h1
  rwa [inv_inv] at key

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc GlobalTheory.SeeSaw
open scoped Pointwise


set_option maxHeartbeats 2000000 in
theorem unipotent_character_trivial_at_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u : UX D (σ + 1), MxAt (fun _ => True) (u.1.1 - 1) → xFB F σ h' ⬝ u.1.1 - xFB F σ h' ∈ (pcFB W F σ h h').A₁ → ∀ v ∈ G.pl.S0, ∀ i j : Fin (σ + 1), j.1 = i.1 + 1 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * u.1.1 i j) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA1 v hv i j hij
  obtain ⟨-, -, -, -, f5, -, -⟩ := GlobalTheory.T.fractionalIdealCompletion_properties_at_place D W.ψ W.ψ_std v
  have hiσ : i.1 < σ := by have := j.2; omega
  have hii : (⟨i.1, hiσ⟩ : Fin σ).castSucc = i := Fin.ext rfl
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  have e0 : u.1.1 i j = (u.1.1 - 1) i j := by rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
  rw [e0]
  set N := u.1.1 - 1 with hNdef
  set s := idem D (· = v) * N i j with hsdef
  have hs : s ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (idem_mem_idAt _)
  have hN0 : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (by
      unfold Places.modulBar
      intro h0
      apply G.pl.modul_ne_bot sc
      have h1 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
      simpa using h1)
  have hAA : D.host.AA ≠ 0 := GlobalTheory.CuspCharLattice.host_AA_ne_zero _
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero hAA (inv_ne_zero hN')
  have hB : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN0)
  have hx : ∀ n : ℕ, FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ n)⁻¹) ≠ 0 := fun n => by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero))
  have hst : ∀ c (p : Fin c), stairId (G.pl.stA sc) (G.pl.stAbar sc) c p ≠ 0 := fun c p =>
    mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

  set 𝔟V : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (j.1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) (Fin.castLE (by omega) j) with h𝔟V
  have hbV : 𝔟V ≠ 0 := mul_ne_zero (hx _) (hst _ _)
  have hV : ∀ a ∈ idV 𝔟V v, colMul (F.dJ (σ + 1) h).jX j a ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v) :=
    fun a ha => lineV F hF (σ + 1) h j v a ha
  have hsupp : ∀ a ∈ idV 𝔟V v, a ∈ idAt D (· = v) := fun a ha =>
    GlobalTheory.SeeSaw.PrimSplit.idAt_of_colMul (F.dJ (σ + 1) h) (hV a ha)
  have hmW := (((GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hq T L μ0 hL sc G W M hM F hF).2.1 σ h').2.1 v).1
  set 𝔟W1 : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ ((⟨i.1, hiσ⟩ : Fin σ).1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) (⟨i.1, hiσ⟩ : Fin σ)) * D.host.AA with h𝔟W1
  set 𝔟W2 : FI D := FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ ((⟨i.1, hiσ⟩ : Fin σ).1 + 1))⁻¹) *
    stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) (⟨i.1, hiσ⟩ : Fin σ)) *
    ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) with h𝔟W2
  have hbW1 : 𝔟W1 ≠ 0 := mul_ne_zero (mul_ne_zero (hx _) (hst _ _)) hAA
  have hbW2 : 𝔟W2 ≠ 0 := mul_ne_zero (mul_ne_zero (hx _) (hst _ _)) hN0

  have hrow : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ∈ latRow G (2 * σ + 2) := hA1
  have eY : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') = xFB F σ h' ⬝ N ⬝ (F.dJ (σ + 1) h).pX := by
    show (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ⬝ (F.dJ (σ + 1) h).pX = _
    rw [Matrix.mul_sub, Matrix.mul_one]

  have hloc := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v _ (idem_mem_intAt (· = v)) _ hrow
  have sdV : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    (G.isV (X := .grid (2 * σ + 2 + 1) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd
  have hmem := ((LatMem.mem_latO_iff D _ _ _ _ sdV sdW _ _).1 hloc).2
  have hY1 : ∀ y ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v),
      (xFB F σ h' ⬝ N ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y ∈ latA _ (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro y hy
    have h1 := hmem y hy
    have hyid := latV_idAt hy
    have ey : idem D (· = v) • y = y := funext fun k => (mem_idAt_iff _ _).1 (hyid k)
    rwa [eY, Matrix.smul_mulVec, ← Matrix.mulVec_smul, ey] at h1
  have r1 := mul_mem_idV_of_lines (F.dJ (σ + 1) h) (F.dB σ h') _ _ (latA _ (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) 𝔟V 𝔟W1
    ⟨i.1, hiσ⟩ j hV (fun y hy => lineW F hF σ h' v hmW ⟨i.1, hiσ⟩ D.host.AA hAA y hy) N hY1
  rw [hii] at r1
  have hs1 : s ∈ idV (𝔟W1 * 𝔟V⁻¹) v := (GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔟V 𝔟W1 hbV hbW1 s hs).1 fun a ha => by
    rw [hsdef, mul_comm (idem D (· = v)) (N i j), mul_assoc, (mem_idAt_iff _ a).1 (hsupp a ha)]
    exact r1 a ha

  obtain ⟨e, he, -⟩ := W.cosVec_is
  have hY2 : ∀ y ∈ latV _ (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v),
      (xFB F σ h' ⬝ (e • N) ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y ∈
        latMul _ {a | a ∈ ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)} (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro y hy
    have h1 := GlobalTheory.T.depthLatticeRow_mulVec_mem_modulus_scaledCompletion D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) e he _ hrow v y hy
    rwa [eY, ← Matrix.smul_mul, ← Matrix.mul_smul] at h1
  have r2 := mul_mem_idV_of_lines (F.dJ (σ + 1) h) (F.dB σ h') _ _ _ 𝔟V 𝔟W2
    ⟨i.1, hiσ⟩ j hV (fun y hy => lineW F hF σ h' v hmW ⟨i.1, hiσ⟩ _ hN0 y hy) (e • N) hY2
  rw [hii] at r2
  have hs2 : e * s ∈ idV (𝔟W2 * 𝔟V⁻¹) v :=
    (GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v 𝔟V 𝔟W2 hbV hbW2 (e * s) (Ideal.mul_mem_left _ _ hs)).1 fun a ha => by
      have h3 := r2 a ha
      rw [Matrix.smul_apply, smul_eq_mul] at h3
      have e4 : e * s * a = e * N i j * (idem D (· = v) * a) := by rw [hsdef]; ring
      rw [e4, (mem_idAt_iff _ a).1 (hsupp a ha)]
      exact h3

  have e5 : 2 * (σ + 1) + 1 - 1 - j.1 = 2 * σ + 2 - 1 - i.1 := by omega
  have q1 : 𝔟W1 * 𝔟V⁻¹ = dI D * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹ := by
    rw [h𝔟W1, h𝔟V]
    simp only [stairId, Fin.val_castLE]
    rw [e5, hij, line_ratio' _ _ _ hA hB _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero), span_neg, dI, Places.stAbar]
    ring
  have q2 : 𝔟W2 * 𝔟V⁻¹ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar := by
    rw [h𝔟W2, h𝔟V]
    simp only [stairId, Fin.val_castLE]
    rw [e5, hij, line_ratio' _ _ _ hA hB _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero), span_neg, Places.stAbar]
    rw [show ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 *
        (D.host.AAbar * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) =
        FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ D.host.xi0 * D.host.AAbar *
          (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) by ring,
      mul_inv_cancel₀ hN0, mul_one]
  rw [q1] at hs1
  rw [q2] at hs2
  have hdI := GlobalTheory.T.ideal_membership_off_modulus D hq T L μ0 hL sc G W M hM v hv e he s hs hs1 hs2
  have h6 := (f5 s hs).1 hdI (idem D (· = v)) (idem_mem_intAt _)
  rwa [hsdef, mul_assoc, mul_comm (N i j), ← mul_assoc, idem_mul_self] at h6

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

theorem unipotent_character_trivial_off_S0 : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u : UX D (σ + 1), xFB F σ h' ⬝ u.1.1 - xFB F σ h' ∈ (pcFB W F σ h h').A₁ → ∀ v ∉ G.pl.S0,
      ∀ i j : Fin (σ + 1), j.1 = i.1 + 1 → psiE W.ψ (idem D (· = v) * u.1.1 i j) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hA v hv i j hij
  obtain ⟨hgood, -⟩ := GlobalTheory.T.standard_frames_successive_levels D hq T L μ0 hL sc G W M hM F hF σ h h' v hv
  have hrow : (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h') ∈ latRow G (2 * σ + 2) := hA
  have hloc := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v _ (idem_mem_intAt (· = v)) _ hrow
  have sdV : IsSelfDualC (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) :=
    (G.isV (X := .grid (2 * σ + 2 + 1) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd
  have sdW : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) ⟨by omega, by omega⟩ fun j e => by cases e).sd
  have hmem := ((LatMem.mem_latO_iff D _ _ _ _ sdV sdW _ _).1 hloc).2
  have hne : i ≠ j := fun e => by rw [e] at hij; omega
  have e0 : u.1.1 i j = (u.1.1 - 1) i j := by rw [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
  rw [e0]
  refine psiE_idem_entry W.ψ_std (F.dJ (σ + 1) h) (F.dB σ h') _ _ _ _ hgood.monoW hgood.prim hgood.cols _ ?_ i j hij
  intro y hy
  have h1 := hmem y hy
  have e1 : (idem D (· = v) • (F.dJ (σ + 1) h).extX _ (xFB F σ h' ⬝ u.1.1 - xFB F σ h')) *ᵥ y =
      (xFB F σ h' ⬝ (u.1.1 - 1) ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y := by
    have hyid := latV_idAt hy
    have ey : idem D (· = v) • y = y := funext fun k => (mem_idAt_iff _ _).1 (hyid k)
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_smul, ey]
    show ((xFB F σ h' ⬝ u.1.1 - xFB F σ h') ⬝ (F.dJ (σ + 1) h).pX) *ᵥ y = _
    rw [Matrix.mul_sub, Matrix.mul_one]
  rwa [e1] at h1

end GlobalTheory.UniStepFB

namespace GlobalTheory.UniStepFB

open GlobalTheory.FinPl GlobalTheory.FinPlLoc

theorem psiUni_pcFB : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    ∀ u : UX D (σ + 1), MxAt (fun _ => True) (u.1.1 - 1) → xFB F σ h' ⬝ u.1.1 - xFB F σ h' ∈ (pcFB W F σ h h').A₁ →
      psiUni W.ψ u.1 = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA
  have key : ∀ i j : Fin (σ + 1), j.1 = i.1 + 1 → psiE W.ψ (u.1.1 i j) = 1 := fun i j hij => by
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    have hs : u.1.1 i j ∈ idAt D (fun _ => True) := by
      have := hu i j
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero] at this
    refine PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 hs fun v _ => ?_
    by_cases hv : v ∈ G.pl.S0
    · exact unipotent_character_trivial_at_S0 D hq T L μ0 hL sc G W M hM F hF σ h h' u hu hA v hv i j hij
    · exact unipotent_character_trivial_off_S0 D hq T L μ0 hL sc G W M hM F hF σ h h' u hA v hv i j hij
  unfold psiUni upSum
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero W.ψ) fun i _ => ?_
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero W.ψ) fun j _ => ?_
  split_ifs with hij
  · exact key i j hij
  · exact psiE_zero W.ψ

end GlobalTheory.UniStepFB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialFourierJacobiStepStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericCharacter_trivial_fourierJacobi_step : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u : UX D (σ + 1), MxAt (fun _ => True) (u.1.1 - 1) → xFB F σ h' ⬝ u.1.1 - xFB F σ h' ∈ (pcFB W F σ h h').A₁ → psiUni W.ψ u.1 = 1 := by
  first | exact @GlobalTheory.UniStepFB.psiUni_pcFB | exact GlobalTheory.UniStepFB.psiUni_pcFB | (intros; apply GlobalTheory.UniStepFB.psiUni_pcFB <;> assumption)
end
