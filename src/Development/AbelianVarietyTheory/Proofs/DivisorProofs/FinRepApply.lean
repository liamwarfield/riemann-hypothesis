module

public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspMult

section Abstract

variable {H S X : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]

def homInto (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Submodule ℂ (S →ₗ[ℂ] X) where
  carrier := {f | (∀ s, f s ∈ C) ∧ ∀ g s, f (σ g s) = ρ g (f s)}
  add_mem' := by
    intro f f' hf hf'
    exact ⟨fun s => C.add_mem (hf.1 s) (hf'.1 s), fun g s => by simp [hf.2 g s, hf'.2 g s]⟩
  zero_mem' := ⟨fun _ => C.zero_mem, fun g s => by simp⟩
  smul_mem' := by
    intro a f hf
    exact ⟨fun s => C.smul_mem a (hf.1 s), fun g s => by simp [hf.2 g s]⟩

def killed (ρ : Representation ℂ H X) (I : Set (MonoidAlgebra ℂ H)) : Submodule ℂ X :=
  ⨅ x ∈ I, LinearMap.ker (ρ.asAlgebraHom x)

theorem mem_killed {ρ : Representation ℂ H X} {I : Set (MonoidAlgebra ℂ H)} {v : X} :
    v ∈ killed ρ I ↔ ∀ x ∈ I, ρ.asAlgebraHom x v = 0 := by
  simp [killed]

def irrSum [TopologicalSpace H] (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Submodule ℂ X :=
  ⨆ (U : Subrepresentation ρ) (_ : U.toSubmodule ≤ C ∧ U.toRepresentation.IsIrreducible ∧
    GlobalTheory.PRep.IsAdmissible U.toRepresentation), U.toSubmodule

def IsDecomp [TopologicalSpace H] (ρ : Representation ℂ H X) (C : Submodule ℂ X) : Prop :=
  ∀ x ∈ C, IsOpen {g : H | ρ g x = x} → x ∈ irrSum ρ C

end Abstract

variable {D : D7}

def finRep {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) : Representation ℂ (GfC V) (MMap M) where
  toFun g := postOn M (LinearMap.funLeft ℂ ℂ fun x => x * (g : GA D V))
  map_one' := by
    ext T v x
    simp [postOn_apply, LinearMap.funLeft]
  map_mul' a b := by
    ext T v x
    simp [postOn_apply, LinearMap.funLeft, mul_assoc]

theorem finRep_apply {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (g : GfC V) (T : MMap M) (v : M.Vec) (x : GA D V) :
    finRep M g T v x = T v (x * (g : GA D V)) := rfl

abbrev allMaps (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) : Submodule ℂ (MMap M) := Mult θ M ∅ (fun _ => 1)

def cuspMult (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel V S) {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Cardinal :=
  Module.rank ℂ (homInto σ (finRep M) (allMaps θ M))


variable (D) in
def CuspDecomp : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsDecomp (finRep M) (allMaps θ M)

structure IsFinIso (V V' : HSp D) (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) (Pg : Finset (Pl D.host.E))
    (j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)) (Φ : GfC V ≃ₜ* GfC V') : Prop where
  isom : HMul.hMul (HMul.hMul (Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) j)
      (V'.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)))) j =
    V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  conj : ∀ g : GfC V, HMul.hMul (finE V' (Φ g : GA D V')).val j = HMul.hMul j (finE V (g : GA D V)).val
  frame : ∃ (h : V.rank = V'.rank) (u : GL (Fin V'.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)),
    HMul.hMul j β.val = (β' * intGL D.host.F D.host.E V'.rank u).val.submatrix id (Fin.cast h) ∧
      ∀ PP ∈ Pg, Formalism.UG.bc (resS D.host.F PP) u = 1

abbrev princDat (n r t : ℕ) (hr : r ≤ n) (Pg : Finset (Pl D.host.E)) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) :
    LevDat D.host.E ℂ n :=
  datY n r t 0 hr Pg ∅ (LevelP.triv Pg r ℂ) χ (fun _ => 1) Frm.B

section Equations

variable (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G]
  (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ)

def eqSet (P : LevelP L.Pg L.r ℂ) {Pl0 : Type} (ok : Set Pl0) (pl : Pl0 → Pl D.host.E) (q : Pl0 → ℕ) (Sg : Pl0 → ℂ[X]) :
    Set (MonoidAlgebra ℂ (GfC V)) :=
  {x | ∃ k : GfC V, (k : GA D V) ∈ levG V β (withP L P) ∧
      x = MonoidAlgebra.single k 1 - MonoidAlgebra.single 1 (levChi V β (withP L P) k)} ∪
  {x | ∃ κ : G → GfC V, (∀ g, IsLevelLift V β L (eG g) (κ g)) ∧
      x = ∑ g, MonoidAlgebra.single (κ g) (c g) - MonoidAlgebra.single 1 1} ∪
  {x | ∃ P0 ∈ ok, ∃ k ≤ V.rank, ∃ (α : GfC V) (R : Finset (GfC V)), IsHeckeAt V (pl P0) k α ∧
      Bridge.IsDC ((levG V β (flag1L L)).subgroupOf (GfC V)) α⁻¹ R ∧
      x = ∑ γ ∈ R, MonoidAlgebra.single γ 1 -
        MonoidAlgebra.single 1 ((Sg P0).coeff k / ((-1) ^ k * (q P0 : ℂ) ^ (k * (k - 1) / 2)))}

def IsGoodRep {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W) : Prop :=
  ∃ v : W, v ≠ 0 ∧ (∀ k : GfC V, (k : GA D V) ∈ levG V β (flag1L L) → σ k v = v) ∧
    ∃ κ : G → GfC V, (∀ g, IsLevelLift V β L (eG g) (κ g)) ∧ ∑ g, c g • σ (κ g) v = v

end Equations

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def MultEq (R : RealDat D A Ks) : Prop :=
  ∀ (i : Fin D.R.m) (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (j : Matrix (Fin (Wc D i).rank) (Fin (Yc D 0).rank) (EAf D))
    (Φ : GfC (Yc D 0) ≃ₜ* GfC (Wc D i)), IsFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) R.Pg j Φ →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), σ.IsIrreducible →
      GlobalTheory.PRep.IsAdmissible σ →
      IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ →
      cuspMult R.θ M₀ σ = cuspMult R.θ (R.MW i (sg0 D A)) (σ.comp Φ.symm.toMulEquiv.toMonoidHom)

end GlobalTheory.CuspMult

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedIdem

open Formalism.L2.Col

variable {D : D7}

theorem sigR_mem_intAE {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig y ∈ intAE D := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    exact AddSubgroup.subset_closure ⟨a, ha, cO _ x, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

theorem finPart_cA (z : Formalism.L2.Theta.AE D) :
    finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem cA_cA (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem finPart_conj_mem {e : Formalism.L2.Theta.AE D} {x : D.host.E}
    (h : finPart D (e * incA D x) ∈ intAE D) : finPart D (cA D e * incA D (star x)) ∈ intAE D := by
  have := sigR_mem_intAE h
  rwa [← finPart_cA, RingHom.map_mul, cA_incA] at this

theorem isIdemAt_conj {e : Formalism.L2.Theta.AE D} {P Q : HeightOneSpectrum (𝓞 D.host.E)} (he : IsIdemAt e Q)
    (h : ∀ x, x ∈ P.asIdeal ↔ cO _ x ∈ Q.asIdeal) : IsIdemAt (cA D e) P := by
  obtain ⟨⟨h1, h2, v, ε, h3, h4⟩, h5⟩ := he
  refine ⟨⟨by rw [← RingHom.map_mul, h1], by rw [cA_cA, mul_comm, h2], v, ε, h3, by rw [cA_cA, add_comm, h4]⟩,
    fun x h0 => ?_⟩
  have h0' : cO _ x ≠ 0 := by
    intro h1
    apply h0
    rw [← cO_cO x, h1, map_zero]
  rw [h, h5 _ h0']
  refine not_congr ⟨fun hm => ?_, fun hm => ?_⟩
  · have := finPart_conj_mem hm
    rw [star_inv₀] at this
    have h6 : star ((cO _ x : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := star_star (x : D.host.E)
    rwa [h6] at this
  · have := finPart_conj_mem hm
    rw [star_inv₀, cA_cA] at this
    exact this

theorem exists_isIdemAt : ∀ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)),
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal → ∃ e : Formalism.L2.Theta.AE D, IsIdemAt e P := by
  intro D P hP
  have hex : ∃ a ∈ P.asIdeal, cO _ a ∉ P.asIdeal := by
    by_contra hn
    push Not at hn
    apply hP
    ext x
    rw [mem_conjIdeal]
    exact ⟨fun hx => by simpa only [cO_cO] using hn _ hx, hn x⟩
  obtain ⟨a, ha, ha'⟩ := hex
  let v : HeightOneSpectrum (𝓞 D.host.F) := P.under (𝓞 D.host.F)
  have hv : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal := rfl
  obtain ⟨e, he⟩ := GlobalTheory.MovedSplit.exists_splitAt D v ⟨P.asIdeal, P.isPrime, hv, a, ha, cO _ a, rfl, ha'⟩
  obtain ⟨Q, hQ, hQv⟩ := GlobalTheory.IdemPrime.exists_isIdemAt D v e he
  have hsub : (P.asIdeal : Set (𝓞 D.host.E)) ⊆ Q.asIdeal ∪ (Q.asIdeal.comap (cO _) : Ideal (𝓞 D.host.E)) := by
    intro x hx
    obtain ⟨n, hn, -⟩ := GlobalTheory.MovedSplit.exists_int D (x * cO _ x) (by
      show star ((x : D.host.E) * star (x : D.host.E)) = (x : D.host.E) * star (x : D.host.E)
      rw [star_mul', star_star, mul_comm])
    have h1 : n ∈ v.asIdeal := by
      rw [← hv, Ideal.mem_comap, hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [← hQv, Ideal.mem_comap, hn] at h1
    exact Q.isPrime.mem_or_mem h1
  rcases Ideal.subset_union.1 hsub with h | h
  · have : P = Q := HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top h)
    exact ⟨e, this ▸ hQ⟩
  · have := Q.isPrime
    have h2 := P.isMaximal.eq_of_le (Ideal.comap_ne_top (cO _) Q.isPrime.ne_top) h
    exact ⟨_, isIdemAt_conj hQ fun x => by rw [h2, Ideal.mem_comap]⟩

end GlobalTheory.MovedIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct Topology ComplexOrder

namespace GlobalTheory.ThetaIntegrand

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_princ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (T : Finset (Pl E))
    (h1 : ∀ i j, (β⁻¹ * x * β).1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h2 : ∀ i j, (β⁻¹ * x * β)⁻¹.1 i j ∈ Formalism.L2.Herm.intAf F E)
    (h3 : ∀ PP ∈ T, ∀ i j, ∃ z ∈ Formalism.L2.Herm.intAf F E,
      (β⁻¹ * x * β).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j = (Ideal.absNorm PP.asIdeal : ℕ) * z) :
    x ∈ St β ∧ ∀ PP ∈ T, redFn β PP x = 1 := by
  have hx : x = β * (β⁻¹ * x * β) * β⁻¹ := by group
  generalize β⁻¹ * x * β = m at h1 h2 h3 hx
  have hi : Function.Injective fun A : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E) =>
      A.map (Formalism.L2.Herm.intAf F E).subtype := Matrix.map_injective Subtype.val_injective
  let y : GL (Fin n) (Formalism.L2.Herm.intAf F E) :=
    ⟨Matrix.of fun i j => ⟨_, h1 i j⟩, Matrix.of fun i j => ⟨_, h2 i j⟩,
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.mul_inv),
      hi (by
        simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
        exact m.inv_mul)⟩
  have hy : frGL β y = x := by
    have : intGL F E n y = m := Units.ext rfl
    rw [hx, ← this]
    rfl
  refine ⟨⟨y, hy⟩, fun PP hP => ?_⟩
  rw [← hy, redFn_frGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  obtain ⟨z, hz, e⟩ := h3 PP hP i j
  have e1 : y.1 i j = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j +
      (Ideal.absNorm PP.asIdeal : ℕ) * ⟨z, hz⟩ := by
    apply Subtype.ext
    have : (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) :
        E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) _) i j := by
      simp only [Matrix.one_apply]; split_ifs <;> rfl
    rw [Subring.coe_add, Subring.coe_mul, Subring.coe_natCast, this, ← e, add_sub_cancel]
    rfl
  have e2 : ((Ideal.absNorm PP.asIdeal : ℕ) : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.absNorm_mem _)
  change resS F PP (y.1 i j) = (1 : Matrix (Fin n) (Fin n) (kP PP)) i j
  rw [e1, map_add (f := _), map_mul, map_natCast, e2, zero_mul, add_zero]
  simp only [Matrix.one_apply]; split_ifs <;> simp

theorem eventually_princ_mat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Af F)) (T : Finset (Pl E)) {X : Type} [TopologicalSpace X] {x₀ : X}
    {φ : X → GL (Fin n) (Af F ⊗[F] E)} (hf : Continuous φ) (h₀ : φ x₀ = 1) :
    ∀ᶠ κ in 𝓝 x₀, Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ) ∈ St β ∧
      ∀ PP ∈ T, redFn β PP (Formalism.UG.bc (GlobalTheory.Mass.swapTens F E (Af F) : _ →+* _) (φ κ)) = 1 := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho := (GlobalTheory.Mass.intTens_open_compact F E).1
  set s := GlobalTheory.Mass.swapTens F E (Af F)
  let β' : GL (Fin n) (Af F ⊗[F] E) := Formalism.UG.bc (s.symm : _ →+* _) β
  have hβ : Formalism.UG.bc (s : _ →+* _) β' = β := Units.ext (Matrix.ext fun i j => s.apply_symm_apply _)
  let m : X → GL (Fin n) (Af F ⊗[F] E) := fun κ => β'⁻¹ * φ κ * β'
  have hm : Continuous m := (continuous_const.mul hf).mul continuous_const
  have hm1 : m x₀ = 1 := by simp only [m, h₀, mul_one, inv_mul_cancel]
  have hs : ∀ κ, β⁻¹ * Formalism.UG.bc (s : _ →+* _) (φ κ) * β = Formalism.UG.bc (s : _ →+* _) (m κ) := fun κ => by
    simp only [m, map_mul, map_inv, hβ]
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j ∈
      GlobalTheory.Mass.intTens F E := fun i j => by
    simp only [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ).1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_val.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀).1 i j ∈ _ by rw [hm1]; exact hone i j)
  have e2 : ∀ᶠ κ in 𝓝 x₀, ∀ i j, (m κ)⁻¹.1 i j ∈ GlobalTheory.Mass.intTens F E := by
    simp only [Filter.eventually_all]
    intro i j
    exact (ho.preimage ((Units.continuous_coe_inv.comp hm).matrix_elem i j)).mem_nhds
      (show (m x₀)⁻¹.1 i j ∈ _ by rw [hm1, inv_one]; exact hone i j)
  have e3 : ∀ᶠ κ in 𝓝 x₀, ∀ PP ∈ T, ∀ i j,
      algebraMap F _ ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j) ∈ GlobalTheory.Mass.intTens F E := by
    rw [Filter.eventually_all_finset]
    simp only [Filter.eventually_all]
    intro PP _ i j
    have hc : Continuous fun κ => algebraMap F (Af F ⊗[F] E) ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j) :=
      continuous_const.mul (((Units.continuous_val.comp hm).matrix_elem i j).sub continuous_const)
    refine (ho.preimage hc).mem_nhds ?_
    rw [Set.mem_preimage, hm1, Units.val_one, sub_self, mul_zero]
    exact (GlobalTheory.Mass.intTens F E).zero_mem
  filter_upwards [e1, e2, e3] with κ h1 h2 h3
  refine mem_princ β _ T ?_ ?_ ?_
  · rw [hs]; exact h1
  · rw [hs, ← map_inv]; exact h2
  · intro PP hP i j
    refine ⟨_, h3 PP hP i j, ?_⟩
    have hN : ((Ideal.absNorm PP.asIdeal : ℕ) : F) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h0 => PP.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have e : (m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j =
        (Ideal.absNorm PP.asIdeal : ℕ) * (algebraMap F _ ((Ideal.absNorm PP.asIdeal : ℕ) : F)⁻¹ *
        ((m κ).1 i j - (1 : Matrix (Fin n) (Fin n) _) i j)) := by
      rw [← mul_assoc, ← map_natCast (algebraMap F (Af F ⊗[F] E)), ← map_mul,
        mul_inv_cancel₀ hN, map_one, one_mul]
    have := congrArg s e
    rw [map_mul, map_natCast, map_sub] at this
    rw [hs]
    refine Eq.trans ?_ this
    congr 1
    simp only [Matrix.one_apply]; split_ifs <;> simp

variable {D : D7}

theorem eventually_princ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (T : Finset (Pl D.host.E)) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), finE V κ ∈ UA D.sp.cm V.gram ∧ finE V κ ∈ St β ∧ ∀ PP ∈ T, redFn β PP (finE V κ) = 1 := by
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig V.gram
  have hf : Continuous (finHom V) :=
    (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  filter_upwards [eventually_princ_mat β T hf (map_one _)] with κ h
  refine ⟨?_, h⟩
  have := (GlobalTheory.Mass.swapPts (Af D.host.F) D.sp.cm.sig V.gram (π κ)).2
  rwa [GlobalTheory.Mass.coe_swapPts, hπ κ] at this

theorem levFn_eq_one {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n)
    (hg : ∀ PP ∈ L.Pg, redFn β PP x = 1) (hq : ∀ PP ∈ L.Q, redFn β PP x = 1) : levFn β L x = 1 := by
  have h1 : rTup β L x = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 x) = 1
    rw [hg PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hP
    rw [hq PP hP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hg PP hP, dBlk, blockDiagonalExtendByOnePrimeField_one, map_one]

section Generic

variable {G H W : Type} [Group G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : G →* H) (Γ : Subgroup G)
  (ρ : G →* Module.End ℂ W) {J : Subgroup H} {χ : J →* ℂˣ} {f : H → W}

theorem form_invariant (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    ρ (γ * g)⁻¹ (f (π (γ * g))) = ρ g⁻¹ (f (π g)) := by
  have h := hf ⟨γ, hγ⟩ (π g) 1
  rw [map_one, Units.val_one, one_smul, OneMemClass.coe_one, mul_one] at h
  have h' : f (π (γ * g)) = ρ γ (f (π g)) := by rw [map_mul]; exact h
  rw [h', ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem form_continuous [TopologicalSpace G] [IsTopologicalGroup G] (hρ : ∀ x, Continuous fun g => ρ g x)
    (hJ : ∀ᶠ κ in 𝓝 (1 : G), ∃ h : π κ ∈ J, χ ⟨_, h⟩ = 1)
    (hf : f ∈ Bridge.AdForms (π.comp Γ.subtype) (ρ.comp Γ.subtype) J χ) : Continuous fun g => ρ g⁻¹ (f (π g)) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have h0 : Continuous fun h : G => ρ h⁻¹ (f (π g)) := (hρ _).comp continuous_inv
  refine h0.continuousAt.congr ?_
  have ht : Filter.Tendsto (fun h : G => g⁻¹ * h) (𝓝 g) (𝓝 1) := by
    simpa using (continuous_const_mul g⁻¹).tendsto g
  filter_upwards [ht.eventually hJ] with h hh
  obtain ⟨hk, h5⟩ := hh
  have h4 := hf 1 (π g) ⟨_, hk⟩
  rw [h5, map_one, map_one, Units.val_one, one_smul, one_mul, ← map_mul, mul_inv_cancel_left] at h4
  rw [h4]
  rfl

end Generic

theorem eventually_level (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    ∀ᶠ κ in 𝓝 (1 : GA D V), ∃ h : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J, (levEnv V β L).χ ⟨_, h⟩ = 1 := by
  classical
  filter_upwards [eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  have hk : finE V κ ∈ lev D.sp.cm V.gram β (flag1L L) :=
    Kg_le_lev (D := flag1L L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩
  exact ⟨hk, levFn_eq_one β (finE V κ) (flag1L L) (fun PP hP => h3 PP (Finset.mem_union_left _ hP))
    fun PP hP => h3 PP (Finset.mem_union_right _ hP)⟩

theorem ext_invariant {V : HSp D} (c : CoefA V) {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ} {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ J χ) : ∀ γ ∈ GQ V, ∀ g, c.ext f (γ * g) = c.ext f g :=
  fun _ hγ g => form_invariant (finHom V).rangeRestrict (GQ V) c.ρ hf hγ g

theorem ext_continuous {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) {f : Bridge.Gf V → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) : Continuous (c.ext f) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  haveI : IsTopologicalGroup (GA D V) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  exact form_continuous (finHom V).rangeRestrict (GQ V) c.ρ hc.2.2.1 (eventually_level V β L) hf

theorem integrableOn_form {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om) (hs : S.SigOK)
    (hp : S.IsPosDef) (c : CoefA S) (hc : c.Is) (β : GL (Fin S.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ S.rank)
    {f : Bridge.Gf S → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF S) c.coef.ρ (levEnv S β L).J (levEnv S β L).χ)
    (pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)) (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    (io : c.W →ₗ[ℂ] PolF D T.rank S.rank) {K : Subgroup (GL (Fin S.rank) (Lev.EAf D))} {μ : Measure (GA D S)}
    {𝓕 : Set (GA D S)} (hμ : IsMeasDef S K μ 𝓕) (g : GA D T) :
    IntegrableOn (fun h => thetaKO om h g (pt (io (c.ext f h)))) 𝓕 μ := by
  have hpos : ∀ τ, (gramAt D S τ).PosDef := fun τ => by
    have := hs (tauE D τ)
    rw [hp] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  exact GlobalTheory.DefiniteQuotient.integrableOn_theta D ψ hom.std S T χS χT om hom hpos c.W (pt ∘ₗ io)
    (fun w => hpt _) _ (ext_continuous c hc β L hf) (ext_invariant c hf) μ 𝓕 hμ.1.1 hμ.2 g

end GlobalTheory.ThetaIntegrand

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTPull

open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

theorem push_comp (h : IsGrpPullback A' A f φ) {α : A' ⟶ A'} {β : A ⟶ A} (hab : α.left ≫ φ = φ ≫ β.left)
    (T : Over S') (x : T ⟶ A') : pushHom h T (x ≫ α) = pushHom h T x ≫ β :=
  Over.OverMorphism.ext (by
    show (x.left ≫ α.left) ≫ φ = (x.left ≫ φ) ≫ β.left
    rw [Category.assoc, hab, Category.assoc])

theorem isTanScal_iff (h : IsGrpPullback A' A f φ) {O : Type} [Ring O] (a : OActN O A) (a' : OActN O A')
    (hact : ∀ c, (a'.act c).left ≫ φ = φ ≫ (a.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ A') ≃* (epsPtR (x ≫ f) ⟶ A)) (he : ∀ v, (e v).left = v.left ≫ φ) (b : O) (c : R')
    (v : epsPtR x ⟶ A') : IsTanScal a' x b c v ↔ IsTanScal a (x ≫ f) b c (e v) := by
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ spMap (algebraMap R' (DualNumber R')) = spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hR : ∀ (u w : epsPtR x ⟶ A'), u.left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ w.left ↔
      (e u).left = spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ (e w).left := fun u w => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap ((TrivSqZeroExt.map (c • (LinearMap.id : R' →ₗ[R'] R'))).toRingHom) ≫ ·) (Over.w w)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · have E : e (v ≫ a'.act b) = e v ≫ a.act b := Over.OverMorphism.ext (by
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
    have H := hR (v ≫ a'.act b) v
    rw [E] at H
    exact H

end GlobalTheory.HTPull

namespace GlobalTheory.HTPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem kernel_pullback (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂)) (e : ℕ)
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x ^ e = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine GlobalTheory.SiegelPull.push_injective h T ((map_pow _ _ _).trans ((hn _ (pushHom h T x) ?_).trans (map_one _).symm))
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

end GlobalTheory.HTPull

namespace GlobalTheory.HTPull

open GlobalTheory.SiegelPull ReciprocityTheory.ChartRestriction.G.Pdiv

theorem exists_objMap_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : Obj b N s), ∃ o' : Obj b N (f ≫ s), Nonempty (ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  let A' := (Over.pullback f).obj o.A
  let φ := PullbackComparison.pφ f o.A
  let φ₂ := PullbackComparison.pφ₂ f o.A
  have pb : IsGrpPullback A' o.A f φ := PullbackComparison.isGrpPullback f o.A
  have sq : IsSquare φ φ₂ := PullbackComparison.isSquare f o.A
  have hab : IsAbelianScheme A' :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (Limits.pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (Limits.pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (Limits.pullback.snd _ _); infer_instance }
  obtain ⟨act', ⟨hhom, hone, hmul, hadd⟩, hact'⟩ := ActPull.exists_act_pull S S' f o.A A' φ pb D.Oᵐᵒᵖ
    (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a b => by simpa using o.act.mul b.unop a.unop) (fun a b => by simpa using o.act.add a.unop b.unop)
  let actN : OActN D.O A' :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => hhom _
      one := by simpa using hone
      mul := fun c d => by rw [MulOpposite.op_mul]; exact hmul _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact hadd _ _ }
  have hact : ∀ c, (actN.act c).left ≫ φ = φ ≫ (o.act.act c).left := fun c => hact' (MulOpposite.op c)
  let P' : LB (G2 A').left := o.P.pull φ₂
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂
  have iso : LBIso P' (o.P.pull φ₂) := PullbackComparison.gen_refl _ hP'
  have dg := SiegelPull.diag_iso sq iso
  have sqL : ∀ (x' y' : G2 A' ⟶ A') (x y : G2 o.A ⟶ o.A), x'.left ≫ φ = φ₂ ≫ x.left → y'.left ≫ φ = φ₂ ≫ y.left →
      (lift x' y').left ≫ φ₂ = φ₂ ≫ (lift x y).left := fun x' y' x y hx hy =>
    (Category.id_comp _).symm.trans (SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (G2 o.A).hom)) (T' := G2 A') (𝟙 _) x' y'
      (Z := G2 o.A) φ₂ x y (by rw [Category.id_comp]; exact hx) (by rw [Category.id_comp]; exact hy))
  obtain ⟨t₁, ht₁⟩ := o.rig₁
  obtain ⟨t₂, ht₂⟩ := o.rig₂
  obtain ⟨eK, heK, hK⟩ := o.kerP
  let o' : Obj b N (f ≫ s) :=
    { A := A'
      ab := hab
      act := actN
      P := P'
      isLB := hP'
      rig₁ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_one_id f o.A)) t₁ ht₁
      rig₂ := gen_chartPull (chartPullLinComb o.P _ _ _ _ φ (fun _ => PullbackComparison.lift_id_one f o.A)) t₂ ht₂
      symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P _ _ rfl)
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => PullbackComparison.lift_swap f o.A)) o.symm
      ample := (pol_pull S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab pb dg).2.1 o.ample
      kerP := ⟨eK, heK, fun T x hx => kernel_pullback pb sq o.isLB hP' iso eK hK T x hx⟩
      rosati := fun c => LBIso.chartPull
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.1, Category.assoc])
          (by rw [sq.2])))
        (chartPullLinComb o.P _ _ _ _ φ₂ (fun _ => sqL _ _ _ _ (by rw [sq.1]) (by
          rw [Over.comp_left, Over.comp_left, Category.assoc, hact, ← Category.assoc, ← sq.2, Category.assoc])))
        (o.rosati c)
      lie := fun R' _ β x hx v hv => by
        obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv pb (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
          (Category.assoc _ _ _).symm
        obtain ⟨w, hw, hvw⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hx]) (e v)
          ((isTanScal_iff pb o.act actN hact x e he _ _ v).1 hv)
        refine ⟨fun i => e.symm (w i), fun i c => (isTanScal_iff pb o.act actN hact x e he _ _ _).2
          (by rw [e.apply_symm_apply]; exact hw i c), e.injective ?_⟩
        rw [hvw, map_list_prod, List.map_ofFn]
        simp [Function.comp_def]
      lieRank := fun k _ _ x β hx i => (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) S S' o.A A' f φ (o.act.toF D) (actN.toF D) pb
        (fun c => hact _) k x (β.comp (b.t i)) D.m).2 (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hx]) i)
      eta := fun y => SiegelPull.secPull pb (o.eta y)
      eta_add := fun y z => SiegelPull.push_injective pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', o.eta_add, MonObj.comp_mul])
      eta_lin := fun c y => SiegelPull.push_injective pb _ (by
        rw [push_comp pb (hact c), push_secPull', push_secPull', o.eta_lin, Category.assoc])
      eta_ker := fun y => SiegelPull.push_injective pb _ (by
        rw [push_secPull', o.eta_ker, map_one, MonObj.comp_one])
      geom := fun k _ _ x β hx => by
        obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hx])
        let e : (Over.mk x ⟶ A') ≃* (Over.mk (x ≫ f) ⟶ o.A) := MulEquiv.ofBijective (pushHom pb (Over.mk x))
          ⟨SiegelPull.push_injective pb _, SiegelPull.push_surjective pb _⟩
        have ea : ∀ c g, e (g ≫ actN.act c) = e g ≫ o.act.act c := fun c g => push_comp pb (hact c) _ g
        have ex : ∀ z, z.left = (e.symm z).left ≫ φ := fun z =>
          (congrArg (fun q => q.left) (e.apply_symm_apply z)).symm
        refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := fun n y => e.symm (I.ev n y)
                  add := fun n y z => by rw [I.add, map_mul]
                  lin := fun n c y => e.injective (by rw [ea, e.apply_symm_apply, e.apply_symm_apply, I.lin])
                  ker := fun n hn hp y => by rw [map_eq_one_iff _ e.symm.injective]; exact I.ker n hn hp y
                  onto := fun n hn hp q => by
                    rw [← map_eq_one_iff e e.injective, map_pow, I.onto n hn hp (e q)]
                    exact exists_congr fun y => e.symm_apply_eq.symm
                  tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp]
                  isom := fun n hn hp y z => (weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _)
                    (pull_isLB hP' _) pb dg (Over.mk x) n _ _ (I.ev n y) (I.ev n z) _ (ex _) (ex _)).2
                    (I.isom n hn hp y z) }, fun y => ?_⟩
        show toUnit _ ≫ SiegelPull.secPull pb (o.eta y) = e.symm (I.ev N y)
        rw [eq_comm, e.symm_apply_eq, ← hI y]
        exact (SiegelPull.push_secPull pb (o.eta y) (Over.mk x)).symm }
  exact ⟨o', ⟨{ φ := φ, φ₂ := φ₂, cart := pb, sq := sq, act := hact, pol := iso, eta := fun y => SiegelPull.secPull_left pb _ }⟩⟩

end GlobalTheory.HTPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdeles
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open Filter Topology Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeTensorRead

theorem continuous_of_map_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    (g : FiniteAdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 E) E)
    (hg : ∀ a : FiniteAdeleRing (𝓞 F) F, (∀ v, a v ∈ v.adicCompletionIntegers F) → ∀ v, g a v ∈ v.adicCompletionIntegers E) :
    Continuous g := by
  refine continuous_of_continuousAt_zero g.toAddMonoidHom ?_
  intro U hU
  have hU0 : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 E) E) := by simpa using hU
  have hC := GlobalTheory.AdeleCocompact.isCompact_integral E
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (0 : FiniteAdeleRing (𝓞 E) E)) (P := fun x y => x * y ∈ U)
    (fun y _ => (continuous_mul.tendsto' ((0 : FiniteAdeleRing (𝓞 E) E), y) 0 (zero_mul y)) hU0)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele E).eventually h1).exists
  have hn0 : ((n.factorial : ℕ) : F) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  let m : FiniteAdeleRing (𝓞 F) F := algebraMap F _ ((n.factorial : ℕ) : F)⁻¹
  have hm : ((n.factorial : ℕ) : FiniteAdeleRing (𝓞 F) F) * m = 1 := by
    rw [← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul, mul_inv_cancel₀ hn0, map_one]
  have hO : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have h2 : (fun a => m * a) ⁻¹' {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} ∈ 𝓝 0 :=
    (hO.preimage (continuous_const.mul continuous_id)).mem_nhds (by
      intro v
      change (m * 0) v ∈ _
      rw [mul_zero]
      exact zero_mem _)
  refine Filter.mem_map.2 (mem_of_superset h2 fun a ha => ?_)
  have h3 := hn _ (hg _ ha)
  rw [← map_natCast g, ← map_mul, ← mul_assoc, hm, one_mul] at h3
  exact h3

theorem continuous_finite_equiv (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) :
    Continuous ι ∧ Continuous ι.symm := by
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.E
  obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  haveI : LocallyCompactSpace (Af D.host.F ⊗[D.host.F] D.host.E) := e0.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Af D.host.F ⊗[D.host.F] D.host.E) := e0.secondCountableTopology
  have hc : Continuous ι := by
    refine IsModuleTopology.continuous_of_ringHom (R := Af D.host.F) ι.toRingHom ?_
    refine continuous_of_map_integral _ fun a ha P => ?_
    exact (hint (a ⊗ₜ[D.host.F] (1 : D.host.E))).1 (AddSubgroup.subset_closure ⟨a, ha, 1, rfl⟩) P
  have ho : IsOpenMap ι :=
    AddMonoidHom.isOpenMap_of_sigmaCompact ι.toAddEquiv.toAddMonoidHom ι.surjective hc
  exact ⟨hc, (ι.toEquiv.toHomeomorphOfContinuousOpen hc ho).symm.continuous⟩

theorem exists_infinite_equiv (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) :
    ∃ j : (Ainf F ⊗[F] E) ≃+* InfiniteAdeleRing E, Continuous j ∧ Continuous j.symm ∧
      ∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x := by
  haveI := h.1
  haveI := h.2.1
  choose θ h1 h2 using fun w : InfinitePlace E => GlobalTheory.InfAdeleCM.exists_hom (F := F) w.embedding
  obtain ⟨e, he, hc, hc', -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv F E σ (InfinitePlace E) (fun w => w.embedding) θ h
    (by
      unfold GlobalTheory.Mem.Vol.IsCMFam
      simp only [InfinitePlace.mk_embedding]
      exact Function.bijective_id) (fun w => ⟨h1 w, h2 w⟩)
  let p : InfiniteAdeleRing E ≃+* (InfinitePlace E → ℂ) :=
    RingEquiv.piCongrRight fun w => InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  have hp : Continuous p := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  have hp' : Continuous p.symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp
      (continuous_apply w)
  refine ⟨e.trans p.symm, hp'.comp hc, hc'.comp hp, fun x => ?_⟩
  rw [RingEquiv.trans_apply, RingEquiv.symm_apply_eq]
  funext w
  rw [he, h1]
  change w.embedding x = InfinitePlace.Completion.extensionEmbedding w (algebraMap E (InfiniteAdeleRing E) x w)
  simpa using (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)).symm

theorem isPlIdem_parts (D : D7)
    (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (hint : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1)
    {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (he : IsPlIdem D e P) :
    infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ Q, Q ≠ P → ι (finPart D e) Q = 0 := by
  obtain ⟨hee, ⟨v, ε, ⟨α, rfl, -, -⟩, hor⟩, hx⟩ := he
  have hε1 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 :=
    TensorProduct.zero_tmul _ _
  have hinf : infPart D e = 0 := by
    rcases hor with ⟨h1, h2⟩ | h
    · have : e = e * (e + cA D e) := by rw [mul_add, hee, h1, add_zero]
      rw [this, h2, RingHom.map_mul, hε1, mul_zero]
    · rw [h, hε1]
  obtain ⟨f, hf⟩ : ∃ f, f = ι (finPart D e) := ⟨_, rfl⟩
  have hff : f * f = f := by rw [hf, ← map_mul, ← RingHom.map_mul, hee]
  have hf01 : ∀ R, f R ≠ 0 → f R = 1 := by
    intro R hR
    have : f R * f R = f R * 1 := by rw [← GlobalTheory.PlaceIdem.mul_ap, hff, mul_one]
    exact mul_left_cancel₀ hR this
  have key : ∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ ∃ R, f R ≠ 0 ∧ x ∈ R.asIdeal) := by
    intro x hx0
    have h1 : finPart D (incA D ((x : D.host.E)⁻¹)) = (1 : Af D.host.F) ⊗ₜ[D.host.F] ((x : D.host.E)⁻¹) := rfl
    rw [hx x hx0, hint, RingHom.map_mul, map_mul, ← hf, h1, hι, not_forall]
    refine exists_congr fun R => ?_
    rw [GlobalTheory.PlaceIdem.mul_ap]
    by_cases hR : f R = 0
    · simp [hR]
    · rw [hf01 R hR, one_mul, GlobalTheory.PlaceIdem.val_inv_le_one R hx0]
      simp
  have h0 : ∀ Q, Q ≠ P → f Q = 0 := by
    intro Q hQ
    by_contra hne
    refine hQ (HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top fun x hxQ => ?_))
    by_cases hx0 : x = 0
    · rw [hx0]; exact zero_mem _
    · exact (key x hx0).2 ⟨Q, hne, hxQ⟩
  rw [← hf]
  refine ⟨hinf, ?_, h0⟩
  obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
  obtain ⟨R, hR, -⟩ := (key x hx0).1 hxP
  by_cases hRP : R = P
  · subst hRP
    exact hf01 _ hR
  · exact absurd (h0 R hRP) hR

theorem map_loc {R S : Type} [CommRing R] [CommRing S] (q : R →+* S) (e a : R) :
    q (1 + e * (a - 1)) = 1 + q e * (q a - 1) := by
  simp

theorem loc_eq_finSingle {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (f a : FiniteAdeleRing (𝓞 E) E) (k : E) (ha : a = algebraMap E _ k) (h1 : f P = 1) (h0 : ∀ Q, Q ≠ P → f Q = 0) :
    1 + f * (a - 1) = Neutral.B1.finiteSingle E P (algebraMap E _ k) := by
  subst ha
  refine GlobalTheory.PlaceIdem.adele_ext fun Q => ?_
  classical
  change 1 + f Q * (algebraMap E (Q.adicCompletion E) k - 1) =
    Function.update (fun w : HeightOneSpectrum (𝓞 E) => (1 : w.adicCompletion E)) P (algebraMap E _ k) Q
  by_cases hQ : Q = P
  · subst hQ
    rw [h1, Function.update_self]
    ring
  · rw [h0 Q hQ, Function.update_of_ne hQ]
    ring

theorem exists_adele_tensor_equiv (D : D7) :
    ∃ Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Φ ∧ Continuous Φ.symm ∧
      (∀ x : D.host.E, Φ (incA D x) = algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) x) ∧
      ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
        Φ (locE D e (k : D.host.E)) = ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨ι, hι, hint, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨hιc, hιc'⟩ := continuous_finite_equiv D ι hint
  obtain ⟨j, hjc, hjc', hj⟩ := exists_infinite_equiv D.host.F D.host.E D.sp.cm.sig
    ⟨D.sp.cm.totReal, D.sp.cm.cmUnram.1, D.sp.cm.deg2, D.sp.cm.cmUnram.2.1⟩
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  let Φ : AE D ≃+* AdeleRing (𝓞 D.host.E) D.host.E := s.trans (j.prodCongr ι)
  have hΦ : ∀ z, Φ z = (j (infPart D z), ι (finPart D z)) := fun z =>
    Prod.ext (congrArg j (hs z).1) (congrArg ι (hs z).2)
  refine ⟨Φ, (hjc.prodMap hιc).comp hsc, hsc'.comp (hjc'.prodMap hιc'), fun x => ?_, fun P e he k => ?_⟩
  · rw [hΦ]
    exact Prod.ext (hj x) (hι x)
  · obtain ⟨h1, h2, h3⟩ := isPlIdem_parts D ι hι hint he
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · have h5 : j (infPart D e) = 0 := by rw [h1]; exact j.map_zero
      exact (map_loc (j.toRingHom.comp (infPart D)) e _).trans (by
        change 1 + j (infPart D e) * _ = 1
        rw [h5, zero_mul, add_zero])
    · have h4 : ι (finPart D (incA D (k : D.host.E))) = algebraMap D.host.E _ (k : D.host.E) := hι k
      refine (map_loc (ι.toRingHom.comp (finPart D)) e _).trans ?_
      exact loc_eq_finSingle P _ _ _ h4 h2 h3

theorem exists_hchar_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c →
    ∃ χ : Formalism.L2.Host.HChar D.host.E, ChrEq c χ := by
  intro D c hc
  obtain ⟨Φ, -, hΦ, h1, h2⟩ := exists_adele_tensor_equiv D
  let u : Ideles D.host.E →* (AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦ
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  refine ⟨⟨Circle.toUnits.comp (c.comp u), ht.comp (hc.1.comp hu), fun k => ?_⟩, hc, fun P e he k x hx => ?_⟩
  · have : u (diagUnits D.host.E k) = Units.map (incA D).toMonoidHom k :=
      Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    change Circle.toUnits (c (u _)) = 1
    rw [this, hc.2, map_one]
  · have : x = u (localIdele D.host.E P (atFin P k)) :=
      Units.ext (Φ.eq_symm_apply.2 (by rw [hx, h2 P e he k]))
    rw [this]
    rfl

end GlobalTheory.HeckeTensorRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdelesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeCharacter_of_unitary_tensorIdeles : ∀ (D : D7) (c : (AE D)ˣ →* Circle), IsHeckeChar D c → ∃ χ : Formalism.L2.Host.HChar D.host.E, ChrEq c χ := by
  first | exact @GlobalTheory.HeckeTensorRead.exists_hchar_chrEq | exact GlobalTheory.HeckeTensorRead.exists_hchar_chrEq | (intros; apply GlobalTheory.HeckeTensorRead.exists_hchar_chrEq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnThetaDefinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilParts

theorem integrableOn_theta_definite : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : (GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))), IsWeilDatumO ψ S T χS χT om → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ g, F (γ * g) = F g) → ∀ (μ : Measure (GA D S)) (𝓕 : Set (GA D S)), μ.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 μ → ∀ h, IntegrableOn (fun g => thetaKO om g h (L (F g))) 𝓕 μ :=
  GlobalTheory.DefiniteQuotient.integrableOn_theta

end GlobalTheory.WeilParts
end
