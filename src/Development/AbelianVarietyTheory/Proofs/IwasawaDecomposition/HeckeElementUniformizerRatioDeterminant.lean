module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.MtHeckeSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemUnipSymBc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIneOfUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminant
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet


open _root_.Formalism.L2.Col in
theorem prod_diag_inv {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ) (π : 𝓞 E) (d : ℕ) (hd : d ≤ n) :
    ∏ i : Fin n, (mhlDiag n π d i)⁻¹ = (mhlA π)⁻¹ ^ d := by
  have h1 : ∀ i : Fin n, (mhlDiag n π d i)⁻¹ = (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) i.1 := by
    intro i
    unfold mhlDiag
    by_cases h : i.1 < d <;> simp [h]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Fin.prod_univ_eq_prod_range (fun j : ℕ => if j < d then (mhlA π)⁻¹ else 1) n,
    Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  have : (Finset.range n).filter (fun j => j < d) = Finset.range d := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [this, Finset.card_range]

theorem idem_mul_pow {R : Type} [CommRing R] {e : R} (hee : e * e = e) (x : R) (d : ℕ) : e * (e * x) ^ d = e * x ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ, pow_succ, ← mul_assoc, ih]
    rw [show e * x ^ d * (e * x) = (e * e) * (x ^ d * x) by ring, hee]

theorem pow_mem_int {D : D7} {x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hx : x ∈ intAE D) (d : ℕ) :
    x ^ d ∈ intAE D := by
  induction d with
  | zero => rw [pow_zero]; exact GlobalTheory.HeckeConj.one_mem_intAE D
  | succ d ih => rw [pow_succ]; exact GlobalTheory.HeckeConj.mul_mem_intAE D ih hx

theorem unit_mem {D : D7} {e a : Formalism.L2.Theta.AE D} (hee : e * e = e) (ha : finPart D (e * a) ∈ intAE D) (d : ℕ) :
    finPart D (e * a ^ d + (1 - e)) ∈ intAE D := by
  have he : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  rw [← idem_mul_pow hee a d, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, RingHom.map_mul, RingHom.map_pow]
  exact add_mem (GlobalTheory.HeckeConj.mul_mem_intAE D he (pow_mem_int ha d)) (sub_mem (GlobalTheory.HeckeConj.one_mem_intAE D) he)

theorem det_castGL {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) :
    Matrix.GeneralLinearGroup.det (castGL h g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, castGL, Matrix.det_reindex_self]

theorem det_fin {D : D7} (V : HSp D) (α : GA D V) : finPart D (Formalism.L2.Theta.mt V α).det = (finHom V α).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_swap {D : D7} {m : ℕ} (g : GL (Fin m) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :
    swapAE D g.val.det = (Formalism.UG.bc (swapAE D) g).val.det := by
  rw [RingHom.map_det]; rfl

theorem det_cast {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (g : GL (Fin m) R) : (castGL h g).val.det = g.val.det := by
  have := congrArg Units.val (det_castGL h g)
  simpa only [Matrix.GeneralLinearGroup.val_det_apply] using this

theorem det_conj_inv {R : Type} [CommRing R] {n : ℕ} (C η : GL (Fin n) R) : ((C * η * C⁻¹)⁻¹).val.det = (η⁻¹).val.det := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.GeneralLinearGroup.val_det_apply]
  congr 1
  rw [map_inv, map_inv, map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem cast_inv {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) :
    castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)))⁻¹ := by
  rw [map_inv (finHom V) α, map_inv (Formalism.UG.bc (swapAE D)), map_inv (castGL h.symm)]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_transport {D : D7} (V : HSp D) {n : ℕ} (h : n = V.rank) (α : GA D V) (C η : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (hC : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * η * C⁻¹) :
    swapAE D (finPart D (Formalism.L2.Theta.mt V α⁻¹).det) = (η⁻¹).val.det := by
  have hg : castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)) = (C * η * C⁻¹)⁻¹ := by
    rw [cast_inv V h α, hC]
  rw [det_fin V α⁻¹, det_swap (finHom V α⁻¹), ← det_cast h.symm (Formalism.UG.bc (swapAE D) (finHom V α⁻¹)), hg,
    det_conj_inv C η]

theorem prV_det_eta {D : D7} (n : ℕ) [NeZero n] (v : HeightOneSpectrum (𝓞 D.host.F)) {π : 𝓞 D.host.E} (hπ0 : π ≠ 0)
    (d : ℕ) :
    Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val.det -
        Formalism.L2.Col.iA D.host.F D.host.E (∏ k : Fin n, (Formalism.L2.Col.mhlDiag n π d k)⁻¹)) = 0 := by
  have hdiag : ∀ i j : Fin n, Formalism.UG.prV v ((((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val i j) =
      Formalism.UG.prV v ((Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) i j) := by
    intro i j
    rw [Formalism.L2.Col.mhl_prV_eta_inv, Matrix.diagonal_apply]
    by_cases hij : i = j <;> simp [hij]
  have hm : (Formalism.UG.prV v).mapMatrix (((Formalism.L2.Col.mhlEta D.sp.cm n v hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) :
      GL (Fin n) (Formalism.IndefR.Lev.EAf D))⁻¹).val =
      (Formalism.UG.prV v).mapMatrix (Matrix.diagonal fun k => Formalism.L2.Col.iA D.host.F D.host.E (Formalism.L2.Col.mhlDiag n π d k)⁻¹) :=
    Matrix.ext hdiag
  rw [RingHom.map_sub, RingHom.map_det, hm, ← RingHom.map_det, Matrix.det_diagonal,
    map_prod (Formalism.L2.Col.iA D.host.F D.host.E), sub_self]

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem hom_mul_pow {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a b : R) (d : ℕ) :
    f ((a * b) ^ d) = f a ^ d * f b ^ d := by
  rw [map_pow, map_mul, mul_pow]

theorem final_alg {R : Type} [CommRing R] {e Δ c X W : R} (hee : e * e = e) (key : e * Δ = e * c) (hc : c = X * W) :
    e * Δ = e * W * (e * X + (1 - e)) := by
  linear_combination key + e * hc + (W - W * X) * hee

theorem swap_inj {D : D7} {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (h : swapAE D x = swapAE D y) :
    x = y :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective h

theorem idem_eq_of_swap {D : D7} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {x c : Formalism.L2.Theta.AE D}
    (h : swapAE D (finPart D e) * swapAE D (finPart D x) = swapAE D (finPart D e) * swapAE D (finPart D c)) :
    e * x = e * c := by
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul]
  · apply swap_inj
    rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
    exact h

end GlobalTheory.Mem.R3.LiftBrg.EtaDet

namespace GlobalTheory.Mem.R3.LiftBrg.EtaDet

theorem det_clause : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), d ≤ n → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    ∃ u u' : Formalism.L2.Theta.AE D, finPart D u ∈ intAE D ∧ finPart D u' ∈ intAE D ∧ e * u * u' = e ∧
      e * (mt V α⁻¹).det = e * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d * u := by
  intro D V n _ h v Pb Ut d e C α hd he hε hα hC
  have hπ0 : ((Ut.π : 𝓞 D.host.E) : D.host.E) ≠ 0 := Formalism.L2.Col.mhl_alg_ne Ut.hπ0
  have hee : e * e = e := he.1.1
  have hfe : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hee])
  have hinv : finPart D (e * incA D ((Ut.π : D.host.E))⁻¹) ∈ intAE D := by
    by_contra hc
    exact Ut.hπP ((he.2 Ut.π Ut.hπ0).2 hc)
  have hpi : finPart D (e * incA D (Ut.π : D.host.E)) ∈ intAE D := by
    rw [RingHom.map_mul]
    exact GlobalTheory.HeckeConj.mul_mem_intAE D hfe (AddSubgroup.subset_closure ⟨1, fun v => one_mem _, Ut.π, rfl⟩)
  have hXY : incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d = 1 := by
    rw [← mul_pow, ← RingHom.map_mul, inv_mul_cancel₀ hπ0, RingHom.map_one, one_pow]
  refine ⟨e * incA D ((Ut.π : D.host.E))⁻¹ ^ d + (1 - e), e * incA D (Ut.π : D.host.E) ^ d + (1 - e),
    unit_mem hee hinv d, unit_mem hee hpi d, ?_, ?_⟩
  · linear_combination e * hXY + ((e + 1) * (incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D (Ut.π : D.host.E) ^ d) -
      e * (incA D ((Ut.π : D.host.E))⁻¹ ^ d + incA D (Ut.π : D.host.E) ^ d) + (e - 1)) * hee
  ·
    have hdet := det_transport V h α C _ hC
    have hε' := hε _ (prV_det_eta (D := D) n v Ut.hπ0 d)
    rw [mul_sub, sub_eq_zero, prod_diag_inv n Ut.π d hd, Formalism.L2.Col.mhlA_inv Ut, ← hdet] at hε'
    have key : e * (Formalism.L2.Theta.mt V α⁻¹).det = e * incA D ((((Ut.π : D.host.E))⁻¹ *
        ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) :=
      idem_eq_of_swap he.1 hε'
    have hc : incA D ((((Ut.π : D.host.E))⁻¹ * ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E)) ^ d) =
        incA D ((Ut.π : D.host.E))⁻¹ ^ d * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d :=
      hom_mul_pow (incA D) _ _ d
    exact final_alg hee key hc

end GlobalTheory.Mem.R3.LiftBrg.EtaDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeElementUniformizerRatioDeterminantStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeElement_uniformizerRatio_determinant : ∀ {D : D7} (V : HSp D) (n : ℕ) [NeZero n] (h : n = V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb) (d : ℕ) (e : Formalism.L2.Theta.AE D) (C : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (α : GA D V), d ≤ n → Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) → (∀ z : Formalism.IndefR.Lev.EAf D, Formalism.UG.prV v z = 0 → swapAE D (finPart D e) * z = 0) → α ∈ GfC V → castGL h.symm (Formalism.UG.bc (swapAE D) (finHom V α)) = C * ((Formalism.L2.Col.mhlEta D.sp.cm n v Ut.hπ0 d : Formalism.L2.Col.UAd D.sp.cm n) : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) * C⁻¹ →
    ∃ u u' : Formalism.L2.Theta.AE D, finPart D u ∈ intAE D ∧ finPart D u' ∈ intAE D ∧ e * u * u' = e ∧
      e * (mt V α⁻¹).det = e * incA D ((Formalism.L2.Col.cO D.host.E Ut.π : 𝓞 D.host.E) : D.host.E) ^ d * u := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.EtaDet.det_clause | exact GlobalTheory.Mem.R3.LiftBrg.EtaDet.det_clause | (intros; apply GlobalTheory.Mem.R3.LiftBrg.EtaDet.det_clause <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideRationalCharacterData
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
open Neutral.B1 hiding G IsPlaceOver

namespace GlobalTheory.ChiTame

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem val_pow_sub_pow_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x ≤ 1) (hy : A.valuation y ≤ 1)
    (h : A.valuation (x - y) < 1) (k : ℕ) : A.valuation (x ^ k - y ^ k) < 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : x ^ (k + 1) - y ^ (k + 1) = (x ^ k - y ^ k) * x + (x - y) * y ^ k := by ring
    rw [e]
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hx) ih
    · rw [map_mul, map_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hy k)) h

theorem ine_fix_root {A : ValuationSubring Ω} {m : ℕ} (hm : A.valuation (m : Ω) = 1) (hm0 : m ≠ 0) {ζ : Ω}
    (hζ : ζ ^ m = 1) {ρ : G E Ω} (hρ : ρ ∈ Ine (F := E) A) : ρ ζ = ζ := by
  have hζ1 : A.valuation ζ = 1 := GlobalTheory.val_eq_one_of_pow_eq_one A hm0 hζ
  have hζ0 : ζ ≠ 0 := by intro h; rw [h, zero_pow hm0] at hζ; exact zero_ne_one hζ
  have hclose : A.valuation (ρ ζ - ζ) < 1 := hρ.2 ζ hζ1.le
  have hξ : ρ ζ * ζ⁻¹ = 1 := by
    refine GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt A hm ?_ ?_
    · rw [mul_pow, ← map_pow, inv_pow, hζ, map_one, inv_one, one_mul]
    · have e : ρ ζ * ζ⁻¹ - 1 = (ρ ζ - ζ) * ζ⁻¹ := by field_simp
      rw [e, Valuation.map_mul, map_inv₀, hζ1, inv_one, mul_one]; exact hclose
  exact (mul_inv_eq_one₀ hζ0).1 hξ

theorem eq_one_of_wild [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {K : Type} [Field K] [TopologicalSpace K] [T2Space K] (r : G E Ω →* Kˣ)
    (hr : Continuous r) {m : ℕ} (hm : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal) (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ m = 1)
    (τ : G E Ω) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) : r τ = 1 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  by_contra hne
  have hd : orderOf (r τ) ∣ m := orderOf_dvd_of_pow_eq_one (hI τ (GlobalTheory.TameGenPowers.wild_mem_Ine hτ))
  have hne1 : orderOf (r τ) ≠ 1 := by rwa [Ne, orderOf_eq_one_iff]
  obtain ⟨l, hl, k, hk⟩ := Nat.exists_prime_and_dvd hne1
  have hlv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal := by
    intro h
    apply hm
    obtain ⟨c, hc⟩ := hd
    rw [hc, hk]
    push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ h)
  have h1 : r (τ ^ k) = 1 := by
    refine GlobalTheory.TameGenPowers.eq_one_of_wild_prime E Ω v A hA K r hr l hl hlv _
      (GlobalTheory.WildInertiaChar.wild_pow A τ hτ k) ?_
    rw [map_pow, ← pow_mul, mul_comm, ← hk, pow_orderOf_eq_one]
  rw [map_pow] at h1
  have h2 := orderOf_dvd_of_pow_eq_one h1
  have ho : orderOf (r τ) ≠ 0 := fun h => hm0 (by simpa [h] using hd)
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact ho (by simpa using hk)
  have h3 := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) h2
  rw [hk] at h3
  have := hl.two_le
  have := Nat.pos_of_ne_zero hk0
  nlinarith

theorem exists_pow_pair [IsAlgClosure E Ω] {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {γ : G E Ω} (hγ : TameGenAt A γ) {K : Type} [Field K] [TopologicalSpace K] [T2Space K]
    (r : G E Ω →* Kˣ) (hr : Continuous r) {m : ℕ} (hm : ((m : ℕ) : 𝓞 E) ∉ v.asIdeal)
    (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ m = 1) {π : Ω} (hπ0 : π ≠ 0) {c : E} (hπ : π ^ m = algebraMap E Ω c)
    {ρ : G E Ω} (hρ : ρ ∈ Ine (F := E) A) : ∃ n : ℕ, ρ π = (γ π / π) ^ n * π ∧ r ρ = r γ ^ n := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hmA : A.valuation (m : Ω) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (natCast_mem A m)) (not_lt.mp fun h => hm ?_)
    rw [← hA]
    simpa using h
  have hroot : ∀ σ : G E Ω, (σ π / π) ^ m = 1 := fun σ => by
    rw [div_pow, ← map_pow, hπ, σ.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  set ζ := γ π / π with hζ
  have hζm : ζ ^ m = 1 := hroot γ
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hK : ∀ σ ∈ Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}),
      σ ∈ Ine (F := E) A ∧ ∃ n : ℕ, σ π = ζ ^ n * π ∧ r σ = r γ ^ n := by
    intro σ hσ
    induction hσ using Subgroup.closure_induction with
    | mem τ hτ =>
      rcases hτ with rfl | hτ
      · exact ⟨hγ.1, 1, by rw [pow_one, hζ, div_mul_cancel₀ _ hπ0], (pow_one _).symm⟩
      · refine ⟨GlobalTheory.TameGenPowers.wild_mem_Ine hτ, 0, ?_, by rw [pow_zero, eq_one_of_wild hA r hr hm hI τ hτ]⟩
        have := GlobalTheory.eq_one_of_pow_eq_one_of_val_sub_lt A hmA (hroot τ) (hτ π hπ0)
        rw [pow_zero, one_mul]
        exact (div_eq_one_iff_eq hπ0).1 this
    | one => exact ⟨one_mem _, 0, by simp, by simp⟩
    | mul σ τ _ _ h1 h2 =>
      obtain ⟨i1, a, a1, a2⟩ := h1
      obtain ⟨i2, b, b1, b2⟩ := h2
      refine ⟨mul_mem i1 i2, a + b, ?_, by rw [map_mul, a2, b2, pow_add]⟩
      rw [AlgEquiv.mul_apply, b1, map_mul, map_pow, ine_fix_root hmA hm0 hζm i1, a1]
      ring
    | inv σ _ h1 =>
      obtain ⟨i1, a, a1, a2⟩ := h1
      refine ⟨inv_mem i1, a * m', ?_, ?_⟩
      · apply σ.injective
        rw [mul_inv_apply, map_mul, map_pow, ine_fix_root hmA hm0 hζm i1, a1, ← mul_assoc, ← pow_add,
          show a * m' + a = (m' + 1) * a by ring, pow_mul, hζm, one_pow, one_mul]
      · rw [map_inv, a2, inv_eq_iff_mul_eq_one, ← pow_add, show a + a * m' = (m' + 1) * a by ring, pow_mul,
          hI γ hγ.1, one_pow]
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  have hfin : ({u : Kˣ | u ^ (m' + 1) = 1} \ {r ρ}).Finite := (GlobalTheory.TameGenPowers.finite_roots K _ hm0).diff
  have ho1 : IsOpen (r ⁻¹' ({u : Kˣ | u ^ (m' + 1) = 1} \ {r ρ})ᶜ) := hfin.isClosed.isOpen_compl.preimage hr
  have ho2 := (stabilizer_isOpen_of_isIntegral (K := E) π).preimage (continuous_const_mul ρ⁻¹)
  obtain ⟨σ, ⟨h1, h2⟩, h3⟩ := mem_closure_iff.1 (hγ.2 hρ) _ (ho1.inter ho2) ⟨by simp, by simp⟩
  obtain ⟨i1, n, n1, n2⟩ := hK σ h3
  refine ⟨n, ?_, ?_⟩
  · have h4 : (ρ⁻¹ * σ) π = π := h2
    rw [← n1]
    conv_lhs => rw [← h4]
    rw [AlgEquiv.mul_apply, mul_inv_apply]
  · rw [← n2]
    by_contra hne
    exact h1 ⟨hI σ i1, fun h => hne (Eq.symm h)⟩

theorem exists_tameRep (hP : GlobalTheory.Published.GlobalArtinReciprocity) [_root_.NumberField.IsTotallyComplex E] [IsAlgClosure E Ω]
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {g : ℕ} (hg : g.Prime) (hN : normV v = g) (hgv : ((g : ℕ) : 𝓞 E) ∈ v.asIdeal)
    (hgv2 : ((g : ℕ) : 𝓞 E) ∉ v.asIdeal ^ 2)
    (hunit : ∀ a : ℕ, a.Coprime g → ∀ x : Eˣ, (x : E) = a → IsUnitAt v (atFin v x))
    {γ : G E Ω} (hγ : TameGenAt A γ) {K : Type} [Field K] [TopologicalSpace K] [T2Space K]
    (r : G E Ω →* Kˣ) (hr : Continuous r) (hI : ∀ σ ∈ Ine (F := E) A, r σ ^ (g - 1) = 1) :
    ∃ (u : 𝓞 E) (hu : (u : E) ≠ 0), NX.TameRep v 1 γ u ∧ IsUnitAt v (atFin v (Units.mk0 (u : E) hu)) ∧
      ∃ σ : G E Ω, art (localIdele E v (atFin v (Units.mk0 (u : E) hu))) = toAb E Ω σ ∧ r σ = r γ := by
  haveI : Fact g.Prime := ⟨hg⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hg2 := hg.two_le
  have hm : 0 < g - 1 := by omega
  have hg1 : ((g - 1 : ℕ) : 𝓞 E) ∉ v.asIdeal := fun h => by
    apply v.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := v.asIdeal.sub_mem hgv h
    rwa [Nat.cast_sub hg.one_le, Nat.cast_one, sub_sub_cancel] at this
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (((g : ℕ) : 𝓞 E) : E)) hm
  have hgE : (((g : ℕ) : 𝓞 E) : E) ≠ 0 := by simpa using hg.ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm.ne', eq_comm, map_eq_zero] at hπ
    exact hgE hπ
  obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod g)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hb
  set a : ℕ := (b : ZMod g).val with hadef
  have hac : a.Coprime g := ZMod.val_coe_unit_coprime b
  have ha0 : ((a : 𝓞 E) : E) ≠ 0 := by
    have : a ≠ 0 := by
      intro h
      rw [h, Nat.coprime_zero_left] at hac
      exact hg.ne_one hac
    simpa using this
  have hx := hunit a hac (Units.mk0 _ ha0) (by simp)
  obtain ⟨σ, hσ, eσ, vσ⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hP E Ω art ha v A hA g hgv hgv2 π (by rw [hN]; exact hπ)
    _ (a : 𝓞 E) hx (by
      show Valued.v (algebraMap E (v.adicCompletion E) ((a : 𝓞 E) : E) - _) < 1
      rw [sub_self, map_zero]
      exact zero_lt_one)
  obtain ⟨n, n1, n2⟩ := exists_pow_pair hA hγ r hr hg1 hI hπ0 hπ hσ
  set ζ := γ π / π with hζ
  have hζm : ζ ^ (g - 1) = 1 := by
    rw [hζ, div_pow, ← map_pow, hπ, γ.commutes, ← hπ, div_self (pow_ne_zero _ hπ0)]
  rw [n1, mul_div_cancel_right₀ _ hπ0] at vσ
  have hζ1 : A.valuation (ζ ^ n) ≤ 1 := by
    rw [map_pow, GlobalTheory.val_eq_one_of_pow_eq_one A hm.ne' hζm, one_pow]
  have haA : A.valuation (algebraMap E Ω ((a : 𝓞 E) : E)) ≤ 1 := by
    have : algebraMap E Ω ((a : 𝓞 E) : E) = (a : Ω) := by simp
    rw [this]
    exact (A.valuation_le_one_iff _).mpr (natCast_mem A a)
  have hpow := val_pow_sub_pow_lt A hζ1 haA vσ
  have hcop : n.Coprime (g - 1) := by
    obtain ⟨e, he⟩ := Nat.gcd_dvd_right n (g - 1)
    obtain ⟨n', hn'⟩ := Nat.gcd_dvd_left n (g - 1)
    have h1 : (ζ ^ n) ^ e = 1 := by
      rw [← pow_mul, show n * e = (g - 1) * n' by rw [he]; nth_rewrite 1 [hn']; ring, pow_mul, hζm, one_pow]
    have h2 := hpow e
    rw [h1] at h2
    have h3 : ((1 - (a : ℤ) ^ e : ℤ) : 𝓞 E) ∈ v.asIdeal := by
      rw [← hA]
      simpa using h2
    have h4 : (g : ℤ) ∣ 1 - (a : ℤ) ^ e := by
      by_contra hnd
      obtain ⟨s, t, hst⟩ := ((Nat.prime_iff_prime_int.1 hg).irreducible.coprime_iff_not_dvd.2 hnd).map
        (Int.castRingHom (𝓞 E))
      apply v.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hst]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ (by simpa using hgv)) (v.asIdeal.mul_mem_left _ h3)
    have h5 : b ^ e = 1 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ g).2 h4
      apply Units.ext
      push_cast at this
      rw [hadef, ZMod.natCast_zmod_val, sub_eq_zero] at this
      rw [Units.val_pow_eq_pow_val, ← this, Units.val_one]
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hb] at h6
    have he0 : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have h7 := Nat.le_of_dvd he0 h6
    have h8 : 0 < Nat.gcd n (g - 1) := Nat.gcd_pos_of_pos_right _ hm
    show Nat.gcd n (g - 1) = 1
    generalize Nat.gcd n (g - 1) = d at *
    nlinarith
  obtain ⟨k, hk⟩ : ∃ k, n * k ≡ 1 [MOD g - 1] :=
    ⟨n ^ (Nat.totient (g - 1) - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.totient_pos.2 hm)]
      exact Nat.ModEq.pow_totient hcop⟩
  have hu : (((a : 𝓞 E) ^ k : 𝓞 E) : E) ≠ 0 := by
    push_cast
    exact pow_ne_zero _ (by simpa using ha0)
  have hmk : Units.mk0 _ hu = Units.mk0 _ ha0 ^ k := Units.ext (by simp)
  refine ⟨(a : 𝓞 E) ^ k, hu, ⟨A, hA, hγ.1, g, π, hgv, hgv2, by rw [hN]; exact hπ, ?_⟩,
    hunit (a ^ k) (hac.pow_left k) _ (by simp), σ ^ k, ?_, ?_⟩
  · have h1 := hpow k
    rw [← pow_mul, pow_eq_pow_of_modEq hk hζm, pow_one, ← map_pow] at h1
    simpa using h1
  · rw [hmk, map_pow, map_pow, map_pow, map_pow, eσ]
  · rw [map_pow, n2, ← pow_mul, pow_eq_pow_of_modEq hk (hI γ hγ.1), pow_one]

end General

end GlobalTheory.ChiTame

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIff
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIff
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd Formalism.UG.P

namespace GlobalTheory.SatInd

section CosetTransport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cosetT_le_of_nonunit {x : K} (h1 : Valued.v x ≤ 1) (h2 : ¬ Valued.v x⁻¹ ≤ 1) (h0 : x ≠ 0) :
    Valued.v x ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hx0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨k, hk⟩ := WithZero.ne_zero_iff_exists.1 hx0
  rw [map_inv₀, ← hk] at h2
  rw [← hk] at h1 ⊢
  have h2' : ¬ (k⁻¹ : Multiplicative ℤ) ≤ 1 := by
    intro h; apply h2; rw [← WithZero.coe_inv]; exact_mod_cast h
  rw [WithZero.coe_le_coe]
  have : (k⁻¹ : Multiplicative ℤ) = Multiplicative.ofAdd (- Multiplicative.toAdd k) := rfl
  rw [this, ← ofAdd_zero, Multiplicative.ofAdd_le] at h2'
  rw [← ofAdd_toAdd k, Multiplicative.ofAdd_le]
  omega

theorem cosetT_v_image (g : K ≃+* K) (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ : K}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (g ϖ) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact absurd hv WithZero.zero_ne_coe
  have hmem : ∀ x : K, x ∈ intL K ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  apply cosetT_le_of_nonunit
  · rw [← hmem, ← hint, hmem, hv]; exact_mod_cast (by decide : (Multiplicative.ofAdd (-1 : ℤ)) ≤ 1)
  · rw [← map_inv₀, ← hmem, ← hint, hmem, map_inv₀, hv]
    rw [← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe]
    decide
  · exact (map_ne_zero g).2 hϖ0

theorem cosetT_unit (g : K ≃+* K) (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {ϖ ϖ' : K}
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (hv' : Valued.v ϖ' = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) :
    Valued.v (g ϖ * ϖ'⁻¹) = 1 := by
  have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := by
    intro x; rw [hint (g.symm x), RingEquiv.apply_symm_apply]
  have hmem : ∀ x : K, x ∈ intL K ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact absurd hv WithZero.zero_ne_coe
  have hinv : Valued.v ϖ⁻¹ = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv, ← WithZero.coe_inv]; rfl
  have hinv' : Valued.v ϖ'⁻¹ = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [map_inv₀, hv', ← WithZero.coe_inv]; rfl
  have hone : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) *
      ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = 1 := by
    rw [← WithZero.coe_mul, ← ofAdd_add]; rfl
  have h1 : Valued.v (g ϖ * ϖ'⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, hinv', ← hone]
    exact mul_le_mul' (cosetT_v_image g hint hv) le_rfl
  have h2 : Valued.v (g.symm ϖ' * ϖ⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, hinv, ← hone]
    exact mul_le_mul' (cosetT_v_image g.symm hint' hv') le_rfl
  have h3 : Valued.v (g ϖ * ϖ'⁻¹)⁻¹ ≤ 1 := by
    have e : (g ϖ * ϖ'⁻¹)⁻¹ = g (g.symm ϖ' * ϖ⁻¹) := by
      rw [map_mul, RingEquiv.apply_symm_apply, map_inv₀, mul_inv, inv_inv, mul_comm]
    rw [e, ← hmem, ← hint, hmem]; exact h2
  rw [map_inv₀] at h3
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv'; exact absurd hv' WithZero.zero_ne_coe
  have hne : Valued.v (g ϖ * ϖ'⁻¹) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (mul_ne_zero ((map_ne_zero g).2 hϖ0) (inv_ne_zero hϖ'0))
  exact le_antisymm h1 (by
    have := mul_le_mul' (le_refl (Valued.v (g ϖ * ϖ'⁻¹))) h3
    rwa [mul_inv_cancel₀ hne, mul_one] at this)

end CosetTransport
end GlobalTheory.SatInd

namespace GlobalTheory.SatInd

section CosetTransport2

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cosetT_tMat_map (g : K →+* K) (x : K) (n m : ℕ) (a : Fin m → ℤ) :
    (tMat x n m a).map g = tMat (g x) n m a := by
  unfold tMat
  rw [Matrix.diagonal_map (map_zero g)]
  congr 1
  funext i
  split_ifs <;> simp [map_zpow₀]

theorem cosetT_tMat_mul (x y : K) (n m : ℕ) (a : Fin m → ℤ) :
    tMat (x * y) n m a = tMat x n m a * tMat y n m a := by
  unfold tMat
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> first | exact mul_zpow _ _ _ | exact (mul_one 1).symm

theorem cosetT_tMat_unit {σ : K →+* K} {u : K} (hσ : σ u = u) (hv : Valued.v u = 1) {n m : ℕ}
    (hm : 2 * m ≤ n) (a : Fin m → ℤ) :
    ∃ t : GU σ n, (((t : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat u n m a ∧
      t ∈ KU σ n := by
  have h0 : u ≠ 0 := by
    intro h; rw [h, Valuation.map_zero] at hv; exact zero_ne_one hv
  let f : Fin n → K := fun i : Fin n =>
    if h : i.val < m then u ^ (a ⟨i.val, h⟩)
    else if h' : n - m ≤ i.val ∧ n - 1 - i.val < m then u ^ (-(a ⟨n - 1 - i.val, h'.2⟩)) else 1
  have hf : ∀ i, σ (f i) * f i.rev = 1 := by
    intro i
    simp only [f]
    have hs : ∀ k : ℤ, σ (u ^ k) = u ^ k := fun k => by rw [map_zpow₀, hσ]
    have hi := i.isLt
    have hr : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
    by_cases h1 : (i : ℕ) < m
    · have h2 : ¬ (i.rev : ℕ) < m := by omega
      have h3 : n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m := by omega
      simp only [dif_pos h1, dif_neg h2, dif_pos h3, hs]
      have : (⟨n - 1 - (i.rev : ℕ), h3.2⟩ : Fin m) = ⟨i, h1⟩ := Fin.ext (by simp only; omega)
      rw [this, ← zpow_add₀ h0, add_neg_cancel, zpow_zero]
    · by_cases h1' : n - m ≤ (i : ℕ) ∧ n - 1 - (i : ℕ) < m
      · have h2 : (i.rev : ℕ) < m := by omega
        simp only [dif_neg h1, dif_pos h1', dif_pos h2, hs]
        have : (⟨(i.rev : ℕ), h2⟩ : Fin m) = ⟨n - 1 - i, h1'.2⟩ := Fin.ext (by simp only; omega)
        rw [this, ← zpow_add₀ h0, neg_add_cancel, zpow_zero]
      · have h2 : ¬ (i.rev : ℕ) < m := by omega
        have h3 : ¬ (n - m ≤ (i.rev : ℕ) ∧ n - 1 - (i.rev : ℕ) < m) := by omega
        simp only [dif_neg h1, dif_neg h1', dif_neg h2, dif_neg h3, map_one, one_mul]
  obtain ⟨t, ht, ht'⟩ := fSatake_diag_exists f hf
  have hfval : ∀ i, Valued.v (f i) = 1 := by
    intro i
    simp only [f]
    split_ifs <;> simp [map_zpow₀, hv]
  exact ⟨t, ht, fSatake_diag_mem_K ht ht' hfval⟩

theorem cosetT_guMap_mem_KU (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {n : ℕ} {k : GU σ n} (hk : k ∈ KU σ n) :
    guMap g hg n k ∈ KU σ' n := by
  have hmem : ∀ M : Matrix (Fin n) (Fin n) K, (∀ i j, M i j ∈ intL K) →
      M ∈ (RingHom.mapMatrix (m := Fin n) (intL K).subtype).range := by
    intro M hM
    exact ⟨Matrix.of fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  unfold KU intPts
  rw [Subgroup.mem_subgroupOf]
  refine ⟨(guMap g hg n k).2, glint_mem_range_of_integral (intL K) _ ?_ ?_⟩
  · refine hmem _ (fun i j => ?_)
    rw [guMap_val, Matrix.map_apply]
    exact (hint _).1 (fSatake_K_int hk i j)
  · rw [← Subgroup.coe_inv, ← map_inv]
    refine hmem _ (fun i j => ?_)
    rw [guMap_val, Matrix.map_apply]
    exact (hint _).1 (fSatake_K_int (inv_mem hk) i j)

end CosetTransport2
end GlobalTheory.SatInd

namespace GlobalTheory.SatInd

section CosetTransport3

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem cosetT_fwd (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) (ϖ ϖ' : K) (q q' n m : ℕ)
    (hU : IsUnramInv ϖ σ q) (hU' : IsUnramInv ϖ' σ' q') (hm : 2 * m ≤ n) (a : Fin m → ℤ)
    (y : GU σ n)
    (h : ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :
    ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n,
      ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨u₁, hu₁, k, hk, hy⟩ := h
  have hϖ'0 : ϖ' ≠ 0 := by
    intro h0; have := hU'.2.2.2.1; rw [h0, Valuation.map_zero] at this
    exact absurd this WithZero.zero_ne_coe
  have hcv : Valued.v (g ϖ * ϖ'⁻¹) = 1 := cosetT_unit g hint hU.2.2.2.1 hU'.2.2.2.1
  have hcσ : σ' (g ϖ * ϖ'⁻¹) = g ϖ * ϖ'⁻¹ := by
    rw [map_mul, map_inv₀, ← hg, hU.2.2.1, hU'.2.2.1]
  obtain ⟨t, ht, htK⟩ := cosetT_tMat_unit hcσ hcv hm a
  have hgϖ : g ϖ = ϖ' * (g ϖ * ϖ'⁻¹) := by field_simp
  have hmap : ∀ M N : Matrix (Fin n) (Fin n) K, (M * N).map g = M.map g * N.map g :=
    fun M N => Matrix.map_mul (f := (g : K →+* K))
  have htm : (tMat ϖ n m a).map g = tMat (g ϖ) n m a := cosetT_tMat_map (g : K →+* K) ϖ n m a
  have hgu : IsBorelU (guMap g hg n u₁) := fun i j hij => by
    rw [guMap_val, Matrix.map_apply, hu₁.1 i j hij, map_zero]
  have htb : IsBorelU t := fSatake_borel_tMat ht
  refine ⟨t * guMap g hg n u₁ * t⁻¹,
    ⟨fSatake_borel_mul (fSatake_borel_mul htb hgu) (fSatake_borel_inv htb), fun i => ?_⟩,
    t * guMap g hg n k, mul_mem htK (cosetT_guMap_mem_KU g hg hint hk), ?_⟩
  · rw [fSatake_borel_diag_mul (fSatake_borel_mul htb hgu) (fSatake_borel_inv htb),
      fSatake_borel_diag_mul htb hgu, guMap_val, Matrix.map_apply, hu₁.2 i, map_one, mul_one,
      mul_comm]
    exact fSatake_borel_diag_inv htb i
  · have e : t * guMap g hg n u₁ * t⁻¹ * (t * guMap g hg n k) =
        t * guMap g hg n u₁ * guMap g hg n k := by group
    rw [Matrix.mul_assoc (tMat ϖ' n m a), ← Units.val_mul, ← Subgroup.coe_mul, e, guMap_val, hy,
      hmap, hmap, htm, hgϖ, cosetT_tMat_mul, ← ht]
    simp only [Subgroup.coe_mul, Units.val_mul, guMap_val, Matrix.mul_assoc]

theorem cosetT_iff : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q q' n m : ℕ), IsUnramInv ϖ σ q → IsUnramInv ϖ' σ' q' → 2 * m ≤ n → ∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  intro K _ _ g σ σ' hg hint ϖ ϖ' q q' n m hU hU' hm a y
  constructor
  · exact cosetT_fwd g hg hint ϖ ϖ' q q' n m hU hU' hm a y
  · intro h
    have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := fun x => by
      apply g.injective
      rw [RingEquiv.apply_symm_apply, hg, RingEquiv.apply_symm_apply]
    have hint' : ∀ x, x ∈ intL K ↔ g.symm x ∈ intL K := fun x => by
      rw [hint (g.symm x), RingEquiv.apply_symm_apply]
    have h2 := cosetT_fwd g.symm hg' hint' ϖ' ϖ q' q n m hU' hU hm a (guMap g hg n y) h
    have hyy : guMap g.symm hg' n (guMap g hg n y) = y := by
      apply Subtype.ext
      apply Units.ext
      rw [guMap_val, guMap_val]
      ext i j
      simp
    rwa [hyy] at h2

end CosetTransport3
end GlobalTheory.SatInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryTorusUnipotentCosetTransportIffStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTorus_unipotent_coset_transport_iff : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q q' n m : ℕ), IsUnramInv ϖ σ q → IsUnramInv ϖ' σ' q' → 2 * m ≤ n → ∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  first | exact @GlobalTheory.SatInd.cosetT_iff | exact GlobalTheory.SatInd.cosetT_iff | (intros; apply GlobalTheory.SatInd.cosetT_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingCoeffFieldAndNumbe
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingCoeffFieldAndNumbe
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section
namespace GlobalTheory.HeckeLocN

theorem exists_finExt_big (D : D7) (pl : PlSide D) (big : D.what₂.places.Pl → Finset ℂ) (w : D.what₂.places.Pl) :
    ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), (∀ x, (plEmb pl).emb w x ∈ F0.1) ∧
      ∀ z ∈ big w, (pl.ι w).symm z ∈ F0.1 := by
  classical
  let c := (plEmb pl).emb w
  let S : Finset (Loc.Om (D.what₂.places.resChar w)) := (big w).image (fun z => (pl.ι w).symm z)
  have h1 := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range c
  have h2 : FiniteDimensional ℚ_[D.what₂.places.resChar w]
      (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w)))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c) ⊔
      IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))),
      IntermediateField.finiteDimensional_sup _ _⟩, fun x => ?_, fun z hz => ?_⟩
  · exact (le_sup_left (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · exact (le_sup_right (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.HeckeLocN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicFiniteExtContainingCoeffFieldAndNumbeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicFiniteExt_containing_coeffField_and_numbers : ∀ (D : D7) (pl : PlSide D) (big : D.what₂.places.Pl → Finset ℂ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), (∀ x, (plEmb pl).emb w x ∈ F0.1) ∧ ∀ z ∈ big w, (pl.ι w).symm z ∈ F0.1 := by
  first | exact @GlobalTheory.HeckeLocN.exists_finExt_big | exact GlobalTheory.HeckeLocN.exists_finExt_big | (intros; apply GlobalTheory.HeckeLocN.exists_finExt_big <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterValuesIntegralUnitsAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterValuesIntegralUnitsAtPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem psiInt_of_embW : ∀ (D : D7) (C : NChoice D) (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)), (∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w) ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w)))) → PsiInt X ψ0 := by
  intro D C X ψ0 h j w g
  have hint : ∀ g, ∃ y : OcC X j w, algebraMap (OcC X j w) (FractionRing (OcC X j w)) y =
      ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) := by
    intro g
    have h0 : 0 ≤ D.what₂.places.val w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
      (C.embW_w w _).2 ⟨_, (h w g).symm⟩
    exact (ecC_w X j w _).1 h0
  obtain ⟨a, ha⟩ := hint g
  obtain ⟨b, hb⟩ := hint g⁻¹
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))
    rw [map_mul, ha, hb, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one, map_one]
  exact ⟨Units.mkOfMulEqOne a b hab, ha⟩

end GlobalTheory.HeckeLocN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistCharacterValuesIntegralUnitsAtPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCharacterValues_integral_units_at_place : ∀ (D : D7) (C : NChoice D) (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)), (∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w) ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w)))) → PsiInt X ψ0 := by
  first | exact @GlobalTheory.HeckeLocN.psiInt_of_embW | exact GlobalTheory.HeckeLocN.psiInt_of_embW | (intros; apply GlobalTheory.HeckeLocN.psiInt_of_embW <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorIntegralOnLatticeAtTwistedPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorIntegralOnLatticeAtTwistedPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_preimage_comb {K L V W : Type} [Field K] [Field L] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    (σ : K →+* L) (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (S : Finset W) (hS : ∀ y ∈ S, y ∈ Set.range f)
    (c : W → K) (x : V) (hx : f x = ∑ g ∈ S, σ (c g) • g) :
    ∃ F : Finset V, (↑F ⊆ {x : V | f x ∈ S}) ∧ x = ∑ y ∈ F, c (f y) • y := by
  classical
  refine ⟨S.preimage f hf.injOn, fun y hy => by simpa using hy, hf ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  simp only [LinearMap.map_smulₛₗ]
  exact (Finset.sum_preimage f S hf.injOn (fun g => σ (c g) • g) (fun g hg hn => absurd (hS g hg) hn)).symm

theorem heckeIntTw_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → HeckeIntTw (base M C hR X hS) := by
  intro D M C hR X hS tup hI hsp j w h1 h2 hw v k hg x hx
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨s, ϖ, hc, hu⟩ := hsp v hg.1
  obtain ⟨c, hc0, he⟩ := hI.int w ⟨j', by omega⟩ v k s ϖ hw hg hc hu _ hx
  have h3 := hLC_spec (mt0 M) C.Q hR (j' + 1) w v k h1 h2 hg s ϖ hc hu x
  have h4 := (M (D.what₂.muTw w) (j' + 1) h1 h2).real_inj (h3.trans he)
  obtain ⟨F, hF, hsum⟩ := exists_preimage_comb D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) (j' + 1))
    (LatticeFinitenessFree.jMt_injective _ _) _ (D.what₂.MtLat_sub _ _) c _ h4
  exact ⟨F, fun y => c (D.what₂.jMt (D.what₂.muTw w) (j' + 1) y), hF, fun y _ => hc0 _, hsum⟩

end GlobalTheory.HeckeLocN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorIntegralOnLatticeAtTwistedPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_integral_on_lattice_at_twisted_places : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → HeckeIntTw (base M C hR X hS) := by
  first | exact @GlobalTheory.HeckeLocN.heckeIntTw_base | exact GlobalTheory.HeckeLocN.heckeIntTw_base | (intros; apply GlobalTheory.HeckeLocN.heckeIntTw_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimePlacesIsSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimePlacesIsSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
open scoped Pointwise

namespace GlobalTheory.TypePrimeSplit

theorem exists_intCast_of_card {K : Type} [CommRing K] {p : ℕ} (hp : p.Prime) (h : Nat.card K = p) (x : K) :
    ∃ n : ℤ, x = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.1 (h ▸ hp.one_lt)
  obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card (G := K) h (g := 1) (g' := x) one_ne_zero
  exact ⟨n, by simpa using hn.symm⟩

theorem isSplitPl_of_card {R : Ranks} (H : Host R) (v : PlE H) {p : ℕ} (hp : p.Prime)
    (h : Nat.card (𝓞 H.E ⧸ v.asIdeal) = p) : IsSplitPl H v := by
  by_contra hn
  have key : ∀ x ∈ v.asIdeal, (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x ∈ v.asIdeal := by
    intro x hx
    by_contra hy'
    refine hn ⟨x, hx, fun z hz => ?_⟩
    have : z = (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x := RingOfIntegers.ext hz
    rwa [this]
  apply H.der.unramEF v.asIdeal v.isPrime v.ne_bot
  intro x
  show (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x ∈ v.asIdeal
  obtain ⟨n, hx⟩ := exists_intCast_of_card hp h (Ideal.Quotient.mk v.asIdeal x)
  have ha : x - n ∈ v.asIdeal := Ideal.Quotient.eq.1 (by rw [hx, map_intCast])
  have h3 := key _ ha
  have hf : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • (n : 𝓞 H.E) = n :=
    map_intCast (MulSemiringAction.toRingHom _ (𝓞 H.E) (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H)) n
  rw [smul_sub, hf] at h3
  have h4 : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x = ((PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - n) - (x - n) := by ring
  rw [h4]
  exact sub_mem h3 ha

theorem typePrime_split :
    ∀ (D : D7) (k : Fin 2) (v : PlE D.host), v ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host v :=
  fun D k v hv => isSplitPl_of_card D.host v (D.host.g_prime k)
    (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hv)

end GlobalTheory.TypePrimeSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimePlacesIsSplitPlaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrime_places_isSplitPlace : ∀ (D : D7) (k : Fin 2) (v : PlE D.host), v ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host v := by
  first | exact @GlobalTheory.TypePrimeSplit.typePrime_split | exact GlobalTheory.TypePrimeSplit.typePrime_split | (intros; apply GlobalTheory.TypePrimeSplit.typePrime_split <;> assumption)
end
end
