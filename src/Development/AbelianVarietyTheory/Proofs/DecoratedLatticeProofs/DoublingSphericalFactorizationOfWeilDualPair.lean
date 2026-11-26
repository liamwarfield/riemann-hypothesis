module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueSphericalDoublingSectionUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelLeviDeterminantIntegralSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelLeviDeterminantIntegralSelfDualLattice
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.AInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_mem_intLoc_of_mapsTo {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L]
    (v : HeightOneSpectrum (𝓞 F)) (X : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hX : ∀ x ∈ latLoc F L v, X *ᵥ x ∈ latLoc F L v) : X.det ∈ intLoc F E v := by
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  set b := Formalism.UG.bc (compFin F E v) a with hb
  set N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := (b⁻¹).1 * X * b.1 with hN
  have hent : ∀ i j, N i j ∈ intLoc F E v := by
    intro i j
    have h1 : b.1 *ᵥ (Pi.single j 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F L v :=
      (ha v (Pi.single j 1)).1 fun l => by
        by_cases e : l = j
        · subst e; simp
        · simp [e]
    have h2 := hX _ h1
    have hbN : b.1 * N = X * b.1 := by
      rw [hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have h3 : b.1 *ᵥ (N *ᵥ Pi.single j 1) ∈ latLoc F L v := by
      rwa [Matrix.mulVec_mulVec, hbN, ← Matrix.mulVec_mulVec]
    have h4 := (ha v _).2 h3 i
    simpa using h4
  have hdet : N.det = X.det := by
    rw [hN, Matrix.det_mul, Matrix.det_mul, mul_comm ((b⁻¹).1.det * X.det), ← mul_assoc, ← Matrix.det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  let N' : Matrix (Fin n) (Fin n) (intLoc F E v) := fun i j => ⟨N i j, hent i j⟩
  have hmap : N'.map (intLoc F E v).subtype = N := by ext i j; rfl
  have hd := RingHom.map_det (intLoc F E v).subtype N'
  rw [← hdet, ← hmap, ← RingHom.mapMatrix_apply, ← hd]
  exact (N'.det).2

theorem aH_mem_intLoc_of_lattice (σ : E →ₐ[F] E) {n : ℕ} (Q : Matrix (Fin (n + n)) (Fin (n + n)) E)
    (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F))
    (p : siegelH (Fv F v) σ Q) (hp : (p : GLoc σ Q v) ∈ GlobalTheory.Doubling.KFin σ Q L v) :
    ((aH _ σ Q p : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v := by
  have hk : KeepsDiag finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1 :=
    (mem_siegelOf (e := finSumFinEquiv) (mat := GlobalTheory.AdelicU.matHom (Fv F v) σ Q)).1 p.2
  refine det_mem_intLoc_of_mapsTo L v (leviMat finSumFinEquiv (GlobalTheory.AdelicU.matHom (Fv F v) σ Q p).1) fun x hx => ?_
  have h1 : pairVec finSumFinEquiv x x ∈ latLoc F (sumLat finSumFinEquiv L L) v := by
    rw [latLoc_sumLat]; exact (pairVec_mem_sumLat _).2 ⟨hx, hx⟩
  have h2 := (mem_stabLoc.1 hp _).1 h1
  rw [hk.mulVec_diag, latLoc_sumLat, pairVec_mem_sumLat] at h2
  exact h2.1

theorem aH_mem_intLoc : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram), (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → ((aH _ D.sp.cm.sig (dblSp A).gram p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
  intro D A L hL v p hp
  haveI := GlobalTheory.AdIsom.selfDual_isFullLattice hL
  exact aH_mem_intLoc_of_lattice D.sp.cm.sig (n := A.rank) (dblSp A).gram L v p hp

end GlobalTheory.Core.Rk.AInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelLeviDeterminantIntegralSelfDualLatticeStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (v : FinPl D) (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram), (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → ((aH _ D.sp.cm.sig (dblSp A).gram p : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
  first | exact @GlobalTheory.Core.Rk.AInt.aH_mem_intLoc | exact GlobalTheory.Core.Rk.AInt.aH_mem_intLoc | (intros; apply GlobalTheory.Core.Rk.AInt.aH_mem_intLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueSphericalDoublingSectionUnramified
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Core.Rk.SphSec

section Gen

variable {G : Type} [Group G] (P K : Subgroup G) (f : P →* ℂ)

theorem gen_wd (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p p' : P) (k k' : G) (hk : k ∈ K) (hk' : k' ∈ K)
    (e : (p : G) * k = p' * k') : f p = f p' := by
  have h1 : ((p'⁻¹ * p : P) : G) = k' * k⁻¹ := by
    have : (p : G) = p' * (k' * k⁻¹) := by rw [← mul_assoc, ← e, mul_inv_cancel_right]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, this, inv_mul_cancel_left]
  have h2 := hK _ (h1 ▸ mul_mem hk' (inv_mem hk))
  calc f p = f (p' * (p'⁻¹ * p)) := by rw [mul_inv_cancel_left]
    _ = f p' := by rw [map_mul, h2, mul_one]

variable (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k)

noncomputable def genFun (g : G) : ℂ := f (hI g).choose

variable {P K f hI}

theorem genFun_mul (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) {k : G} (hk : k ∈ K) :
    genFun P K f hI (p * k) = f p := by
  obtain ⟨k', hk', e⟩ := (hI (p * k)).choose_spec
  exact gen_wd P K f hK _ _ _ _ hk' hk e.symm

theorem genFun_right (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (g : G) {k : G} (hk : k ∈ K) :
    genFun P K f hI (g * k) = genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, mul_assoc]
  exact genFun_mul hK _ (mul_mem hk₀ hk)

theorem genFun_left (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (p : P) (g : G) :
    genFun P K f hI (p * g) = f p * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  conv_lhs => rw [e, ← mul_assoc]
  rw [← Subgroup.coe_mul, genFun_mul hK _ hk₀, map_mul]
  rfl

theorem genFun_one (hK : ∀ p : P, (p : G) ∈ K → f p = 1) : genFun P K f hI 1 = 1 := by
  have := genFun_mul (hI := hI) hK 1 (one_mem K)
  rwa [Subgroup.coe_one, mul_one, map_one] at this

theorem genFun_unique (Ψ : G → ℂ) (hΨ : ∀ (p : P) g, Ψ (p * g) = f p * Ψ g) (hΨK : ∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g)
    (g : G) : Ψ g = Ψ 1 * genFun P K f hI g := by
  obtain ⟨k₀, hk₀, e⟩ := (hI g).choose_spec
  have := hΨ (hI g).choose 1
  rw [mul_one] at this
  rw [genFun, mul_comm]
  conv_lhs => rw [e]
  rw [hΨK _ hk₀, this]

theorem continuous_genFun [TopologicalSpace G] [IsTopologicalGroup G] (hK : ∀ p : P, (p : G) ∈ K → f p = 1)
    (ho : IsOpen (K : Set G)) : Continuous (genFun P K f hI) := by
  refine continuous_iff_continuousAt.2 fun g => (continuousAt_const (y := genFun P K f hI g)).congr ?_
  filter_upwards [(ho.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])] with h hh
  have := genFun_right (hI := hI) hK g (k := g⁻¹ * h) hh
  rwa [mul_inv_cancel_left, eq_comm] at this

theorem gen_exists [TopologicalSpace G] [IsTopologicalGroup G] (P K : Subgroup G) (f : P →* ℂ)
    (hI : ∀ g : G, ∃ p : P, ∃ k ∈ K, g = p * k) (hK : ∀ p : P, (p : G) ∈ K → f p = 1) (ho : IsOpen (K : Set G)) :
    ∃ φ : G → ℂ, (∀ (p : P) g, φ (p * g) = f p * φ g) ∧ Continuous φ ∧ (∀ g, ∀ k ∈ K, φ (g * k) = φ g) ∧ φ 1 = 1 ∧
      ∀ Ψ : G → ℂ, (∀ (p : P) g, Ψ (p * g) = f p * Ψ g) → (∀ k ∈ K, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g :=
  ⟨genFun P K f hI, genFun_left hK, continuous_genFun hK ho, fun g _ hk => genFun_right hK g hk, genFun_one hK,
    fun Ψ hΨ hΨK g => genFun_unique Ψ hΨ hΨK g⟩

end Gen


set_option maxHeartbeats 1000000 in
theorem exists_isSphSecAt_unique : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ v : FinPl D, (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → ∀ s : ℂ, ∃ φ, IsSphSecAt A L v μ s φ ∧ ∀ Ψ : Gv (dblSp A) v → ℂ, (∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) g, Ψ (p * g) = charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) * npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g) → (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g := by
  intro D A L hL μ hμ v hunr s
  haveI : Submodule.IsFullLattice D.host.E L :=
    Formalism.IndefR.Fin.PDA.selfDual_isFullLattice A L hL
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KFin D.sp.cm.sig (dblSp A).gram L v) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v
    · exact GlobalTheory.T.hasIwasawaDecomposition_doubled_split_place D A L hL v hs
    · exact GlobalTheory.T.iwasawa_doubled_hermitian_space_nonsplit_place D A L hL v hs
  let N : ℝ≥0 →* ℂ := ⟨⟨fun r => npow r (s + (A.rank : ℂ) / 2), one_npow _⟩, fun r r' => GlobalTheory.Doubling.npow_mul r r' _⟩
  let f : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram →* ℂ :=
    (Circle.coeHom.comp ((charAt μ v).comp (aH _ D.sp.cm.sig (dblSp A).gram))) *
      (N.comp ((absEv D.host.F D.host.E v).comp (aH _ D.sp.cm.sig (dblSp A).gram)))
  have hf : ∀ p, f p = (charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) : ℂ) *
      npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) := fun p => rfl
  have hK : ∀ p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram,
      (p : Gv (dblSp A) v) ∈ KFin D.sp.cm.sig (dblSp A).gram L v → f p = 1 := by
    intro p hp
    have h1 := GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice D A L hL v p hp
    have h2 : (((aH _ D.sp.cm.sig (dblSp A).gram p)⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) :
        Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v := by
      rw [← map_inv]
      exact GlobalTheory.T.siegelLeviDeterminant_integral_selfDual_lattice D A L hL v p⁻¹ (inv_mem hp)
    rw [hf, GlobalTheory.T.ideleCharacter_eq_one_integral_units_unramified_adelic D μ v _ h1 h2 hunr,
      abs_aH_eq_one (continuous_absEv v) (isCompact_KFin v) p hp, one_npow, Circle.coe_one, one_mul]
  clear_value f
  obtain ⟨φ, hl, hc, hr, h1, hu⟩ := gen_exists (G := Gv (dblSp A) v) _ _ f hI hK (isOpen_KFin v)
  refine ⟨φ, ⟨mem_degPSH.2 ⟨fun p g => by rw [hl, hf], hc, IsKFinite.of_invariant fun g k hk => hr g k hk⟩,
    fun k hk g => hr g k hk, h1⟩, fun Ψ hΨ hΨK g => hu Ψ (fun p g => by rw [hΨ, hf]) hΨK g⟩

end GlobalTheory.Core.Rk.SphSec

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueSphericalDoublingSectionUnramifiedStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_spherical_doubling_section_unramified : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ v : FinPl D, (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → ∀ s : ℂ, ∃ φ, IsSphSecAt A L v μ s φ ∧ ∀ Ψ : Gv (dblSp A) v → ℂ, (∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) g, Ψ (p * g) = charAt μ v (aH _ D.sp.cm.sig (dblSp A).gram p) * npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g) → (∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram L v, ∀ g, Ψ (g * k) = Ψ g) → ∀ g, Ψ g = Ψ 1 * φ g := by
  first | exact @GlobalTheory.Core.Rk.SphSec.exists_isSphSecAt_unique | exact GlobalTheory.Core.Rk.SphSec.exists_isSphSecAt_unique | (intros; apply GlobalTheory.Core.Rk.SphSec.exists_isSphSecAt_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPair
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem unrAt_inv_of_unrAt {D : D7} {χ : (AE D)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : GlobalTheory.LFun.UnrAt χ w) : GlobalTheory.LFun.UnrAt χ⁻¹ w := by
  intro x hx
  have := h x hx
  simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.inv_apply, map_inv] at this ⊢
  rw [this, inv_one]

theorem isHeckeChar_inv_sph {D : D7} {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ := by
  refine ⟨?_, fun x => ?_⟩
  · have : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
    rw [this]; exact h.1.inv
  · rw [MonoidHom.inv_apply, h.2 x, inv_one]


set_option maxHeartbeats 1000000 in
theorem sphFactor_of_weilRepresentationUnitaryPair (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair) (D : D7) : SphFactor D := by
  intro ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hv s
  obtain ⟨omh, homh⟩ := GlobalTheory.T.exists_weilDatum_hermitianSpaceDoubled hW D ψ A B χA χB om hP.weil
  have hTC := GlobalTheory.T.doublingMap_thetaIdentity_any_weilData D ψ A B χA χB om omh hP.weil homh
  have hCC := GlobalTheory.T.siegelWeilSection_doubling_eq_matrixCoefficient D ψ A B χA χB om omh hP.weil hTC ν 𝓕 hP.covol
  have hδ := (hTC Φ₁ Φ₂ hΦ₁ hΦ₂).1
  have hco := (hCC Φ₁ Φ₂ hΦ₁ hΦ₂).2
  have hlaw := GlobalTheory.T.siegelWeilSection_degeneratePrincipalSeries_law hW D ψ A B χB omh homh ν 𝓕 hP.covol _ hδ
  have hvac := GlobalTheory.T.doubledTheta_vector_fixed_unramified_stabilizer D ψ A B χB omh homh LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hv
  haveI : Submodule.IsLattice D.host.E LA := hU.sdA.1
  haveI : Submodule.IsFullLattice D.host.E LA := GlobalTheory.ProjXCols.selfDual_isFullLattice A LA hU.sdA
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (KAd D.sp.cm.sig (dblSp A).gram LA a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A LA a hU.sdA hP.maj
  haveI := t2Space_adeleRing' (F := D.host.F)
  have hK : IsCompact (KAd D.sp.cm.sig (dblSp A).gram LA a : Set (GA D (dblSp A))) := isCompact_KAd (isCMExt_host D)
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : GA D (dblSp A) → ℂ, Ψ = fun g => swSec A B omh ν 𝓕 (delta A B Φ₁ Φ₂) g *
      npow (hgtAd D.sp.cm.sig (dblSp A).gram LA a g) (s - sZero A B) := ⟨_, rfl⟩
  have hw : ∀ g : GA D A, wcoef om ν 𝓕 Φ₁ Φ₂ g * npow (hgtL A LA a g) (s - sZero A B) = Ψ (io A (g, 1)) := by
    intro g
    simp only [hΨdef, wcoef, hgtL, hco g]
  have hΨlaw : ∀ (p : siegelH _ D.sp.cm.sig (dblSp A).gram) (g : GA D (dblSp A)),
      Ψ ((p : GA D (dblSp A)) * g) = (χB⁻¹ (aH _ D.sp.cm.sig (dblSp A).gram p) : Circle) *
        npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) * Ψ g := by
    intro p g
    simp only [hΨdef]
    have hleft : hgtAd D.sp.cm.sig (dblSp A).gram LA a ((p : GA D (dblSp A)) * g) =
        absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p) * hgtAd D.sp.cm.sig (dblSp A).gram LA a g :=
      hI.hgtH_left continuous_absE hK p g
    have hr : npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) =
        npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (sZero A B + (A.rank : ℂ) / 2) *
          npow (absE D.host.F D.host.E (aH _ D.sp.cm.sig (dblSp A).gram p)) (s - sZero A B) := by
      rw [← npow_add (hom_pos (absE D.host.F D.host.E) (aH _ D.sp.cm.sig (dblSp A).gram p))]
      congr 1; ring
    rw [hlaw p g, hleft, Doubling.npow_mul, hr]
    ring
  have hΨright : ∀ g, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v,
      Ψ (g * emb D.sp.cm.sig (dblSp A).gram v k) = Ψ g := by
    intro g k hk
    simp only [hΨdef]
    have hright : hgtAd D.sp.cm.sig (dblSp A).gram LA a (g * emb D.sp.cm.sig (dblSp A).gram v k) =
        hgtAd D.sp.cm.sig (dblSp A).gram LA a g := hI.hgtH_right continuous_absE hK g (emb_mem_KAd hk)
    rw [hright]
    congr 1
    simp only [swSec]
    rw [show ((g * emb D.sp.cm.sig (dblSp A).gram v k, (1 : GA D B))) =
      (g, 1) * (emb D.sp.cm.sig (dblSp A).gram v k, 1) by simp, map_mul, Module.End.mul_apply, hvac k hk]
  have hunr : ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt χB⁻¹ w := by
    intro w hw'
    refine unrAt_inv_of_unrAt (hU.unr w ?_)
    intro hmem
    exact hv (by simpa [GlobalTheory.LFun.above, hw'] using hmem)
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.exists_unique_spherical_doubling_section_unramified D A LA hU.sdA χB⁻¹ (isHeckeChar_inv_sph homh.hecT) v hunr s
  have huniq := hφ.2
  refine ⟨φ, hφ.1, fun x hx y => ?_⟩
  have hx' : proj D.sp.cm.sig (dblSp A).gram v (io A (x, 1)) = 1 := by
    rw [io, proj_ioH, hx, map_one, ioH_one]
  have hl : ∀ (p : siegelH (Fv D.host.F v) D.sp.cm.sig (dblSp A).gram) (g : Gv (dblSp A) v),
      Ψ (emb D.sp.cm.sig (dblSp A).gram v (p * g) * io A (x, 1)) =
        charAt χB⁻¹ v (aH _ D.sp.cm.sig (dblSp A).gram p) *
          npow (absEv D.host.F D.host.E v (aH _ D.sp.cm.sig (dblSp A).gram p)) (s + (A.rank : ℂ) / 2) *
          Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1)) := by
    intro p g
    rw [map_mul, mul_assoc, ← coe_embP, hΨlaw, aH_embP, absE_ideleAt]
    rfl
  have hr : ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, ∀ g : Gv (dblSp A) v,
      Ψ (emb D.sp.cm.sig (dblSp A).gram v (g * k) * io A (x, 1)) =
        Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1)) := by
    intro k hk g
    rw [map_mul, mul_assoc, (commute_emb D.sp.cm.sig (dblSp A).gram k hx').eq, ← mul_assoc, hΨright _ k hk]
  have key := huniq (fun g => Ψ (emb D.sp.cm.sig (dblSp A).gram v g * io A (x, 1))) hl hr (ioAt A v y)
  simp only [map_one, one_mul] at key
  rw [hw, hw, ← key, ioAt, emb_ioH, io, ← map_mul, Prod.mk_mul_mk, map_one, one_mul,
    (commute_emb D.sp.cm.sig A.gram y hx).eq]

end GlobalTheory.Core.Rk.IP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalFactorizationOfWeilDualPairStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doublingSphericalFactorization_of_weilDualPair : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, SphFactor D := by
  first | exact @GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair | exact GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair | (intros; apply GlobalTheory.Core.Rk.IP.sphFactor_of_weilRepresentationUnitaryPair <;> assumption)
end
