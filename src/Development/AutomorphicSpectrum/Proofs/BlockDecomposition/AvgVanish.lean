module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinear
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealCompression
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

section Abstract

variable {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup Z] [Module ℂ Z]

def AvgVanish (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ) (f : cIndSpace H σ) (p : G) : Prop :=
  ∃ (L : Subgroup G) (hL : L ≤ U), IsCompact (L : Set G) ∧ ∃ g : cIndSpace H σ,
    f - g ∈ twKer (cInd H σ) L (θ.comp (Subgroup.inclusion hL)) ∧
    (∀ l : L, cInd H σ (l : G) g = ((θ (Subgroup.inclusion hL l) : ℂˣ) : ℂ) • g) ∧
    ∀ u ∈ U, (g : smoothPart (ind H σ)).1.1 (p * u) = 0

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def piPerm (i t : ℕ) : Equiv.Perm (Fin ((i + 1) + t + 1)) :=
  (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)).trans ((ePG i (t + 1)).symm.trans (eGP (i + 1) t))

section
variable (k)

def wGL (i t : ℕ) : GL (Fin ((i + 1) + t + 1)) k where
  val := Equiv.Perm.permMatrix k (piPerm i t)⁻¹
  inv := Equiv.Perm.permMatrix k (piPerm i t)
  val_inv := by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]

def wEl (i t : ℕ) : Mir k ((i + 1) + t + 1) := levi k _ (wGL k i t)

def sEmb (n : ℕ) : Mir k n →* Mir k (n + 1) := (levi k (n + 1)).comp (Mir k n).subtype

def dEmb (i t : ℕ) (d : Fin (t + 1) → k) : Mir k ((i + 1) + t + 1) :=
  ⟨unip k ((i + 1) + (t + 1)) (Multiplicative.ofAdd (Fin.append (0 : Fin (i + 1) → k) d)), MirU_le_Mir k _ ⟨_, rfl⟩⟩

def Cl (i t : ℕ) : Set (Mir k ((i + 1) + t + 1)) :=
  {p | ∀ c : Fin (i + 1), (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
      (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0}

def castM {a b : ℕ} (h : a = b) : Mir k a ≃* Mir k b := h ▸ MulEquiv.refl _
end

section Fibre

variable {i t : ℕ} (τ : MRep k (i + 1)) (σ : GRep k (t + 1))

abbrev sigX : Representation ℂ (HPG k (i + 1) (t + 1)) (τ.V ⊗[ℂ] σ.V) :=
  (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k (i + 1) (t + 1))

abbrev XS : Submodule ℂ (smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))) := cIndSpace (HPG k (i + 1) (t + 1)) (sigX τ σ)

abbrev evX {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (p : Mir k ((i + 1) + (t + 1))) : τ.V ⊗[ℂ] σ.V :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.1 p

abbrev sigC : Representation ℂ (MirabolicParabolic k (i + 1) t) ((psiN τ).V ⊗[ℂ] σ.V) :=
  (extTensor ((psiN τ).tw (((t + 1 : ℕ) : ℝ) / 2)).ρ (mtw (gres σ) (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (gpProj k (i + 1) t)

abbrev sigO (ψ : AddChar k Circle) : Representation ℂ (HPG k i (t + 1)) ((phiN ψ τ).V ⊗[ℂ] σ.V) :=
  (extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ).comp (pgProj k i (t + 1))

def qC : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (psiN τ).V ⊗[ℂ] σ.V :=
  LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) 1).mkQ

def qO (ψ : AddChar k Circle) : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
  LinearMap.rTensor σ.V (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ

variable (k) in
def muD (t : ℕ) : @MeasureTheory.Measure (Fin t → k) (borel _) :=
  letI : MeasurableSpace (Fin t → k) := borel _
  haveI : BorelSpace (Fin t → k) := ⟨rfl⟩
  MeasureTheory.Measure.addHaar

def intC (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) :
    τ.V ⊗[ℂ] σ.V :=
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
    (fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * y))

def intO {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (y : Mir k ((i + 1) + t + 1)) : τ.V ⊗[ℂ] σ.V :=
  @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) (fun d => evX f (dEmb k i t d * y))

def eC (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k ((i + 1) + t)) :
    (psiN τ).V ⊗[ℂ] σ.V :=
  ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m))

def eO (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (m : Mir k (i + (t + 1))) :
    (phiN ψ τ).V ⊗[ℂ] σ.V :=
  ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) •
    qO τ σ ψ (intO f (wEl k i t * sEmb k _ (castM k (by omega) m)))

end Fibre

end GlobalTheory.CompanionTheory.BZPhiPG

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.RealCount

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

variable {n : ℕ}

def m0Z (lam : Fin n → ℤ) : Fin n → ℤ := fun a => 2 * lam a + ((n : ℤ) - 1) - 2 * ((a : ℕ) : ℤ)

def wtR (μ : Fin n → ℤ) : Fin n → ℝ := fun a => (μ a : ℝ)

def DomLE (ν m : Fin n → ℝ) : Prop :=
  (∀ k : ℕ, ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), ν a ≤ ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < k), m a) ∧
    ∑ a, ν a = ∑ a, m a

def wtDual (E : KMod n) (μ : Fin n → ℤ) : Submodule ℂ (E.V →L[ℂ] ℂ) where
  carrier := {ξ | ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z →
    ξ ∘L E.ρ k⁻¹ = (∏ a, z a ^ μ a) • ξ}
  add_mem' {x y} hx hy k z hk := by
    rw [ContinuousLinearMap.add_comp, hx k z hk, hy k z hk, smul_add]
  zero_mem' k z _ := by simp
  smul_mem' c x hx k z hk := by
    rw [ContinuousLinearMap.smul_comp, hx k z hk, smul_comm]

def IsCliff {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ a b d e, c a b * c d e + c d e * c a b = if a = e ∧ b = d then (2 : Matrix ι ι ℂ) else 0) ∧
    ∀ a b, (c a b)ᴴ = c b a

def spinM {ι : Type} [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) : Matrix ι ι ℂ :=
  (1 / 2 : ℂ) • ∑ e, c a e * c e b - if a = b then ((n : ℂ) / 2) • (1 : Matrix ι ι ℂ) else 0

def yF {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Kf : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ) (a b : Fin n) :
    Module.End ℂ (ι → V) where
  toFun x := fun i => Kf a b (x i) + ∑ j, spinM c a b i j • x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, map_add (f := _), smul_add, Finset.sum_add_distrib]
    abel
  map_smul' s x := by
    funext i
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, smul_add, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

end GlobalTheory.CompanionTheory.RealCount
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

section Group

variable (k : Type) [Field k]

abbrev Qp (i t : ℕ) : Subgroup (GL (Fin (i + t)) k) := parab k (two (stdSum (rfl : i + t = i + t)))

def qBlocks (i t : ℕ) : Qp k i t →* GL (Fin i) k × GL (Fin t) k :=
  MonoidHom.prod
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) false).comp (leviProj k (two (stdSum rfl))))
    ((Pi.evalMonoidHom (fun x => GL (Two (Fin i) (Fin t) x) k) true).comp (leviProj k (two (stdSum rfl))))

def uM (n : ℕ) (y : Fin n → k) : Mir k n :=
  ⟨unip k n (Multiplicative.ofAdd y), MirU_le_Mir k n ⟨_, rfl⟩⟩

def topV (i t : ℕ) (x : Fin i → k) : Fin (i + t) → k := Fin.append x 0

def midV (i t : ℕ) (v : Fin t → k) : Fin (i + t) → k := Fin.append 0 v

theorem uM_add (n : ℕ) (a b : Fin n → k) : uM k n (a + b) = uM k n a * uM k n b := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd (a + b)) = unip k n (Multiplicative.ofAdd a) * unip k n (Multiplicative.ofAdd b)
  rw [ofAdd_add, map_mul]

theorem uM_zero (n : ℕ) : uM k n 0 = 1 := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd 0) = 1
  rw [ofAdd_zero, map_one]

theorem uM_mem (n : ℕ) (y : Fin n → k) : uM k n y ∈ MirUin k n := ⟨_, rfl⟩

theorem exists_uM_of_mem (n : ℕ) {u : Mir k n} (hu : u ∈ MirUin k n) : ∃ y, u = uM k n y := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  exact ⟨v.toAdd, Subtype.ext hv.symm⟩

theorem levi_mul_uM (n : ℕ) (g : GL (Fin n) k) (y : Fin n → k) :
    levi k n g * uM k n y = uM k n ((g : Matrix (Fin n) (Fin n) k).mulVec y) * levi k n g := by
  apply Subtype.ext
  exact glEmb_mul_unip' k n g (Multiplicative.ofAdd y)

theorem topV_add_midV (i t : ℕ) (x : Fin i → k) (v : Fin t → k) :
    topV k i t x + midV k i t v = Fin.append x v := by
  funext j
  induction j using Fin.addCases <;> simp [topV, midV]

theorem exists_top_mid (i t : ℕ) (y : Fin (i + t) → k) : ∃ x v, y = topV k i t x + midV k i t v := by
  refine ⟨fun j => y (Fin.castAdd t j), fun j => y (Fin.natAdd i j), ?_⟩
  rw [topV_add_midV]
  funext j
  induction j using Fin.addCases <;> simp

end Group

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def qRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (Qp k i t) (Jacquet τ (MirUin k i) ⊗[ℂ] W) :=
  GlobalTheory.SmGL.twist ((extTensor (psiMinus k τ) σ).comp (qBlocks k i t))
    ((detChar (Fin t) (absPow k (1 : ℂ))).comp ((MonoidHom.snd _ _).comp (qBlocks k i t)))

abbrev hRep (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) :
    Representation ℂ (HPG k i t) (V ⊗[ℂ] W) :=
  (extTensor τ σ).comp (pgProj k i t)

def clT (τ : Representation ℂ (Mir k i) V) (W : Type) [AddCommGroup W] [Module ℂ W] :
    V ⊗[ℂ] W →ₗ[ℂ] Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  LinearMap.rTensor W (twKer τ (MirUin k i) 1).mkQ

def evL {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W} (p : Mir k (i + t)) :
    cIndSpace (HPG k i t) (hRep τ σ) →ₗ[ℂ] V ⊗[ℂ] W :=
  (LinearMap.proj p) ∘ₗ (indSpace (HPG k i t) (hRep τ σ)).subtype ∘ₗ (smoothPart (ind (HPG k i t) (hRep τ σ))).subtype ∘ₗ
    (cIndSpace (HPG k i t) (hRep τ σ)).subtype

def fibV {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) (v : Fin t → k) : V ⊗[ℂ] W :=
  f.1.1.1 (uM k (i + t) (midV k i t v) * levi k (i + t) g)

def fibInt {τ : Representation ℂ (Mir k i) V} {σ : Representation ℂ (GL (Fin t) k) W}
    [MeasurableSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k))
    (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k) : Jacquet τ (MirUin k i) ⊗[ℂ] W :=
  clT τ W (smInt μ (fibV f g))

end Rep

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemTwKerPolyBall
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem polyBall_mono (n : ℕ) {s₁ s₂ : kˣ} (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    polyBall n s₁ ≤ polyBall n s₂ :=
  fun x hx i => show valuation k (x.toAdd i) ≤ valuation k (s₂ : k) from
    le_trans (show valuation k (x.toAdd i) ≤ valuation k (s₁ : k) from hx i) h

theorem exists_mem_polyBall {n : ℕ} (x : Multiplicative (Fin n → k)) :
    ∃ s : kˣ, x ∈ polyBall n s := by
  obtain ⟨M, hM⟩ := Finite.exists_le (fun i : Fin n => valuation k (x.toAdd i))
  obtain ⟨y, hy⟩ := valuation_surjective (max M 1)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact absurd (hy.symm ▸ le_max_right M 1 : (1 : ValueGroupWithZero k) ≤ 0) (by simp)
  refine ⟨Units.mk0 y hy0, fun i => ?_⟩
  show valuation k (x.toAdd i) ≤ valuation k y
  rw [hy]
  exact le_trans (hM i) (le_max_left _ _)

theorem twKer_polyBall_mono (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) {s₁ s₂ : kˣ}
    (h : valuation k (s₁ : k) ≤ valuation k (s₂ : k)) :
    twKer ρ (polyBall n s₁) (resChr ψ a (polyBall n s₁)) ≤
      twKer ρ (polyBall n s₂) (resChr ψ a (polyBall n s₂)) := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨⟨x, hx⟩, v, rfl⟩
  exact Submodule.subset_span ⟨⟨x, polyBall_mono n h hx⟩, v, rfl⟩

theorem exists_mem_twKer_polyBall (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (Multiplicative (Fin n → k)) V) (a : Fin n → k) (v : V)
    (hv : v ∈ twKer ρ ⊤ (resChr ψ a ⊤)) :
    ∃ s : kˣ, v ∈ twKer ρ (polyBall n s) (resChr ψ a (polyBall n s)) := by
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨x, -⟩, u, rfl⟩ := hw
    obtain ⟨s, hs⟩ := exists_mem_polyBall x
    exact ⟨s, Submodule.subset_span ⟨⟨x, hs⟩, u, rfl⟩⟩
  | zero => exact ⟨1, Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨s₁, h₁⟩ := hx
    obtain ⟨s₂, h₂⟩ := hy
    rcases le_total (valuation k (s₁ : k)) (valuation k (s₂ : k)) with h | h
    · exact ⟨s₂, Submodule.add_mem _ (twKer_polyBall_mono ψ ρ a h h₁) h₂⟩
    · exact ⟨s₁, Submodule.add_mem _ h₁ (twKer_polyBall_mono ψ ρ a h h₂)⟩
  | smul c x _ hx =>
    obtain ⟨s, hs⟩ := hx
    exact ⟨s, Submodule.smul_mem _ c hs⟩

end GlobalTheory.CompanionTheory.MirFourier
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRepsSumEqZero
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier ValuativeRel
open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem coe_polyBall_eq (n : ℕ) (t : kˣ) :
    (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) =
      Multiplicative.ofAdd '' FourierPi.box (Fin n) t := by
  ext x
  constructor
  · intro hx
    exact ⟨x.toAdd, fun i _ => hx i, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact fun i => hy i trivial

theorem isCompact_polyBall (n : ℕ) (t : kˣ) :
    IsCompact (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) := by
  rw [coe_polyBall_eq]
  exact (FourierPi.isCompact_box t).image (continuous_ofAdd)

theorem isOpen_polyBall (n : ℕ) (t : kˣ) :
    IsOpen (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) := by
  have h : (polyBall (k := k) n t : Set (Multiplicative (Fin n → k))) =
      Multiplicative.toAdd ⁻¹' FourierPi.box (Fin n) t := by
    ext x
    exact ⟨fun hx i _ => hx i, fun hx i => hx i trivial⟩
  rw [h]
  exact (FourierPi.isOpen_box t).preimage continuous_toAdd

theorem dotProduct_mem_cball {n : ℕ} {a b c : kˣ} (h : valuation k (a : k) * valuation k (b : k) ≤ valuation k (c : k))
    {u x : Fin n → k} (hu : ∀ i, u i ∈ cball a) (hx : ∀ i, x i ∈ cball b) : u ⬝ᵥ x ∈ cball c := by
  refine Finset.sum_induction _ (· ∈ cball c) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
  show valuation k (u i * x i) ≤ valuation k (c : k)
  rw [map_mul]
  exact (mul_le_mul' (hu i) (hx i)).trans h

theorem exists_reps_sum_eq_zero :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ∀ (n : ℕ) (t s : kˣ),
      ∃ R : Finset (Fin n → k), R.Nonempty ∧ (∀ a ∈ R, Multiplicative.ofAdd a ∈ polyBall n t) ∧
        ∀ x : polyBall (k := k) n s, (x : Multiplicative (Fin n → k)) ∉ ann ψ n t →
          ∑ a ∈ R, (((resChr ψ a (polyBall n s) x)⁻¹ : ℂˣ) : ℂ) = 0 := by
  intro k _ _ _ _ ψ hψ n t s
  classical
  obtain ⟨c, hc⟩ := exists_cball_addChar_eq_one ψ hψ
  obtain ⟨t', ht1, ht2⟩ : ∃ t' : kˣ, valuation k (t' : k) ≤ valuation k (t : k) ∧
      valuation k (t' : k) ≤ valuation k ((c * s⁻¹ : kˣ) : k) := by
    rcases le_total (valuation k (t : k)) (valuation k ((c * s⁻¹ : kˣ) : k)) with h | h
    · exact ⟨t, le_rfl, h⟩
    · exact ⟨c * s⁻¹, h, le_rfl⟩
  have hts : valuation k (t' : k) * valuation k (s : k) ≤ valuation k (c : k) := by
    have hs0 : valuation k (s : k) ≠ 0 := by simp
    calc valuation k (t' : k) * valuation k (s : k)
        ≤ valuation k ((c * s⁻¹ : kˣ) : k) * valuation k (s : k) := mul_le_mul_left ht2 _
      _ = valuation k (c : k) := by
        rw [← map_mul]
        simp
  let H : Subgroup (Multiplicative (Fin n → k)) := polyBall n t
  let N : Subgroup H := (polyBall n t').subgroupOf H
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp (isCompact_polyBall n t)
  have hNopen : IsOpen (N : Set H) := (isOpen_polyBall n t').preimage continuous_subtype_val
  haveI : Finite (H ⧸ N) := Subgroup.quotient_finite_of_isOpen _ hNopen
  letI : Fintype (H ⧸ N) := Fintype.ofFinite _
  haveI : N.Normal := ⟨fun a ha b => by
    rw [mul_comm b a, mul_inv_cancel_right]; exact ha⟩
  let rep : H ⧸ N → Fin n → k := fun q => ((q.out : H) : Multiplicative (Fin n → k)).toAdd
  have hinj : Function.Injective rep := fun p q h =>
    Quotient.out_injective (Subtype.ext (Multiplicative.toAdd.injective h))
  refine ⟨Finset.univ.image rep, ?_, ?_, ?_⟩
  · exact ⟨rep 1, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  · intro a ha
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ha
    exact (q.out : H).2
  · intro x hx
    rw [Finset.sum_image (fun a _ b _ h => hinj h)]
    obtain ⟨l₀, hl₀, hne⟩ : ∃ a ∈ polyBall (k := k) n t, ψ (a.toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) ≠ 1 := by
      by_contra h
      push Not at h
      exact hx h
    let y : H → Circle := fun b => (ψ ((b : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd))⁻¹
    let f : H → ℂ := fun b => (y b : ℂ)
    have hmul : ∀ b b' : H, f (b * b') = f b * f b' := by
      intro b b'
      simp only [f, y, ← Circle.coe_mul]
      congr 1
      rw [Subgroup.coe_mul, toAdd_mul, add_dotProduct, AddChar.map_add_eq_mul, mul_inv]
    have hN : ∀ b, ∀ u ∈ N, f (b * u) = f b := by
      intro b u hu
      have h1 : ψ ((u : Multiplicative (Fin n → k)).toAdd ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd) = 1 :=
        hc _ (dotProduct_mem_cball hts (Subgroup.mem_subgroupOf.1 hu) x.2)
      have h2 : f u = 1 := by simp [f, y, h1]
      rw [hmul, h2, mul_one]
    let l : H := ⟨l₀, hl₀⟩
    have hl : f l ≠ 1 := by
      intro h
      apply hne
      have h3 : y l = 1 := Circle.ext (by simpa [f] using h)
      simpa [y, l] using h3
    have hsum := GlobalTheory.CompanionTheory.TwistedAverage.sum_out_mul_right N f hN l
    simp only [hmul] at hsum
    rw [← Finset.sum_mul] at hsum
    have hS : ∑ q : H ⧸ N, f q.out = 0 := by
      have h4 : (∑ q : H ⧸ N, f q.out) * (f l - 1) = 0 := by
        rw [mul_sub, hsum, mul_one, sub_self]
      exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 hl)
    rw [← hS]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (((Circle.toUnits (ψ (rep q ⬝ᵥ (x : Multiplicative (Fin n → k)).toAdd)))⁻¹ : ℂˣ) : ℂ) = f q.out
    simp [f, y, rep]

end GlobalTheory.CompanionTheory.MirFourier

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupport
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.TwAvgInd

open GlobalTheory.CompanionTheory.TwistedAverage

theorem exists_finite_average {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {L : Subgroup G} (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L))
    (x : V) :
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → L) (c : ℂ),
      x - c • ∑ i, twOrbit ρ L θ x (r i) ∈ twKer ρ L θ ∧
      ∀ l : L, ρ (l : G) (c • ∑ i, twOrbit ρ L θ x (r i)) =
        (θ l : ℂ) • (c • ∑ i, twOrbit ρ L θ x (r i)) := by
  classical
  haveI := finiteIndex_stabKer hρ hL θ hθ x
  haveI : Finite (L ⧸ stabKer ρ L θ x) := Subgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (L ⧸ stabKer ρ L θ x)
  have hn : ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hF : ∀ a b : L, (QuotientGroup.mk a : L ⧸ stabKer ρ L θ x) = QuotientGroup.mk b →
      twOrbit ρ L θ x a = twOrbit ρ L θ x b := by
    intro a b h
    have hm : a⁻¹ * b ∈ stabKer ρ L θ x := QuotientGroup.eq.1 h
    have := twOrbit_mul_right ρ L θ x a _ hm
    rw [mul_inv_cancel_left] at this
    exact this.symm
  refine ⟨L ⧸ stabKer ρ L θ x, inferInstance, Quotient.out,
    ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹, ?_, ?_⟩
  · have e : x - ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ •
          ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) =
        ((Fintype.card (L ⧸ stabKer ρ L θ x) : ℕ) : ℂ)⁻¹ •
          ∑ q : L ⧸ stabKer ρ L θ x, (x - twOrbit ρ L θ x (Quotient.out q)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    have e2 : x - twOrbit ρ L θ x (Quotient.out q) =
        (-(((θ (Quotient.out q))⁻¹ : ℂˣ) : ℂ)) •
          (ρ ((Quotient.out q : L) : G) x - (θ (Quotient.out q) : ℂ) • x) := by
      rw [twOrbit, smul_sub, smul_smul, neg_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        neg_smul, neg_smul, one_smul]
      abel
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, rfl⟩)
  · intro l
    have h1 : ∀ t : L, ρ (l : G) (twOrbit ρ L θ x t) = (θ l : ℂ) • twOrbit ρ L θ x (l * t) := by
      intro t
      have h0 : θ l * (θ (l * t))⁻¹ = (θ t)⁻¹ := by
        rw [map_mul, mul_inv, mul_inv_cancel_left]
      simp only [twOrbit, map_smul, smul_smul]
      rw [← Units.val_mul, h0, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    have h2 : ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) =
        ∑ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (Quotient.out q) := by
      let e : Equiv.Perm (L ⧸ stabKer ρ L θ x) := MulAction.toPerm l
      have h3 : ∀ q : L ⧸ stabKer ρ L θ x, twOrbit ρ L θ x (l * Quotient.out q) =
          twOrbit ρ L θ x (Quotient.out (e q)) := by
        intro q
        refine hF _ _ ?_
        rw [QuotientGroup.out_eq']
        conv_rhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [Finset.sum_congr rfl fun q _ => h3 q]
      exact Equiv.sum_comp e (fun q => twOrbit ρ L θ x (Quotient.out q))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum, Finset.sum_congr rfl fun q _ => h1 _, ← Finset.smul_sum, h2,
      smul_comm]

def evalAt {G W : Type} [AddCommGroup W] [Module ℂ W] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W)
    (g : G) : smoothPart (ind P τ) →ₗ[ℂ] W :=
  (LinearMap.proj g) ∘ₗ (indSpace P τ).subtype ∘ₗ (smoothPart (ind P τ)).subtype

theorem exists_twisted_average_smInd {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W)
    (L : Subgroup G) (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L))
    (f : smoothPart (ind P τ)) :
    ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧
      (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧
      ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  obtain ⟨ι, _, r, c, h1, h2⟩ :=
    exists_finite_average (smInd P τ) (GlobalTheory.CompanionTheory.BZFun.isSmooth_smInd P τ) hL θ hθ f
  refine ⟨_, h1, ?_, ?_⟩
  · intro g hg
    by_contra hcon
    push_neg at hcon
    apply hg
    have hz : ∀ i, evalAt P τ g (twOrbit (smInd P τ) L θ f (r i)) = 0 := by
      intro i
      have : evalAt P τ g (smInd P τ ((r i : L) : G) f) = 0 := hcon _ (r i).2
      simp only [twOrbit, map_smul, this, smul_zero]
    have : evalAt P τ g (c • ∑ i, twOrbit (smInd P τ) L θ f (r i)) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz i, smul_zero]
    exact this
  · intro l g
    have h3 := congrArg (evalAt P τ g) (h2 l)
    rw [map_smul] at h3
    exact h3

end GlobalTheory.CompanionTheory.TwAvgInd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjectionToTwistedEigenfunctionSupportStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projection_to_twisted_eigenfunction_support : ∀ {G : Type} {W : Type} [AddCommGroup W] [Module ℂ W] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (P : Subgroup G) (τ : Representation ℂ P W) (L : Subgroup G), IsCompact (L : Set G) → ∀ θ : L →* ℂˣ, IsOpen (θ.ker : Set L) → ∀ f : smoothPart (ind P τ), ∃ f' : smoothPart (ind P τ), f - f' ∈ twKer (smInd P τ) L θ ∧ (∀ g, f'.1.1 g ≠ 0 → ∃ l ∈ L, f.1.1 (g * l) ≠ 0) ∧ ∀ (l : L) (g : G), f'.1.1 (g * l) = (θ l : ℂ) • f'.1.1 g := by
  first | exact @GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | exact GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd | (intros; apply GlobalTheory.CompanionTheory.TwAvgInd.exists_twisted_average_smInd <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjection
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjection
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

theorem exists_perm_of_reps {G : Type} [Group G] (J H : Subgroup G) {r : ℕ} (x : Fin r → G)
    (hx : ∀ i, x i ∈ J) (hu : ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) {j : G} (hj : j ∈ J) :
    ∃ σ : Equiv.Perm (Fin r), ∀ i, (x (σ i))⁻¹ * (j * x i) ∈ H := by
  have h : ∀ i, ∃ k, (x k)⁻¹ * (j * x i) ∈ H := fun i => (hu _ (J.mul_mem hj (hx i))).exists
  choose f hf using h
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := hf a
    have hb := hf b
    rw [← hab] at hb
    have hm : (x a)⁻¹ * x b ∈ H := by
      have h2 := H.mul_mem (H.inv_mem ha) hb
      have e : ((x (f a))⁻¹ * (j * x a))⁻¹ * ((x (f a))⁻¹ * (j * x b)) = (x a)⁻¹ * x b := by group
      rwa [e] at h2
    have h1 : (x b)⁻¹ * x b ∈ H := by simp [H.one_mem]
    exact (hu (x b) (hx b)).unique hm h1
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hinj), hf⟩

theorem exists_average : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∃ E : V →ₗ[ℂ] V, (∀ v, E v ∈ fixed π J) ∧ (∀ v ∈ fixed π J, E v = v) ∧ (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l ∘ₗ E = l) ∧ (∀ x ∈ J, E ∘ₗ π x = E) ∧ ∀ (u : V) (H : Subgroup G), H ≤ J → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) → E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  intro G _ _ _ J hJ V _ _ π hπ
  have hsub : ∀ v, v - GlobalTheory.LocGL.idem hπ hJ v ∈ twKer π J 1 := fun v => by
    rw [← GlobalTheory.LocGL.idem_eq_zero_iff hπ hJ, map_sub,
      GlobalTheory.LocGL.idem_of_mem hπ hJ (GlobalTheory.LocGL.idem_mem hπ hJ v), sub_self]
  refine ⟨GlobalTheory.LocGL.idem hπ hJ, GlobalTheory.LocGL.idem_mem hπ hJ, fun v hv => GlobalTheory.LocGL.idem_of_mem hπ hJ hv,
    ?_, ?_, ?_⟩
  · intro l hl
    have hk : twKer π J 1 ≤ LinearMap.ker l := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨n, v, rfl⟩
      have h1 : l (π (n : G) v) = l v := LinearMap.congr_fun (hl n n.2) v
      simp [h1]
    refine LinearMap.ext fun v => ?_
    have h2 := hk (hsub v)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h2
    exact h2.symm
  · intro x hx
    exact LinearMap.ext fun v => GlobalTheory.LocGL.idem_apply_mem hπ hJ hx v
  · intro u H _ hu r x hr hxJ hex
    have hrc : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr.ne'
    have hfix : ((r : ℂ)⁻¹ • ∑ i, π (x i) u) ∈ fixed π J := GlobalTheory.Parabolic.mem_fixed.2 fun j hj => by
      obtain ⟨σ, hσ⟩ := exists_perm_of_reps J H x hxJ hex hj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum]
      congr 1
      refine Fintype.sum_equiv σ _ _ fun i => ?_
      have e : j * x i = x (σ i) * ((x (σ i))⁻¹ * (j * x i)) := by group
      rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, hu _ (hσ i)]
    have h3 : GlobalTheory.LocGL.idem hπ hJ ((r : ℂ)⁻¹ • ∑ i, π (x i) u) = GlobalTheory.LocGL.idem hπ hJ u := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_smul, map_sum, Finset.sum_congr rfl fun i _ => GlobalTheory.LocGL.idem_apply_mem hπ hJ (hxJ i) u,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hrc, one_smul]
    rw [← h3, GlobalTheory.LocGL.idem_of_mem hπ hJ hfix]

end GlobalTheory.CompanionTheory.CompactAvg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjectionStatement
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_fixed_vector_projection : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∃ E : V →ₗ[ℂ] V, (∀ v, E v ∈ fixed π J) ∧ (∀ v ∈ fixed π J, E v = v) ∧ (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l ∘ₗ E = l) ∧ (∀ x ∈ J, E ∘ₗ π x = E) ∧ ∀ (u : V) (H : Subgroup G), H ≤ J → (∀ h ∈ H, π h u = u) → ∀ (r : ℕ) (x : Fin r → G), 0 < r → (∀ i, x i ∈ J) → (∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H) → E u = ((r : ℂ)⁻¹) • ∑ i, π (x i) u := by
  first | exact @GlobalTheory.CompanionTheory.CompactAvg.exists_average | exact GlobalTheory.CompanionTheory.CompactAvg.exists_average | (intros; apply GlobalTheory.CompanionTheory.CompactAvg.exists_average <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  intro ψ hψ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  have hopen : IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
    rw [GlobalTheory.T.mirabolic_character_eq k ψ n]
    exact GlobalTheory.T.theta_open_mirabolic k ψ hψ (n + 1) _
  exact GlobalTheory.T.twisted_jacquet_exact_smooth τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k (n + 1)) (mirChar k ψ n) hopen
    (GlobalTheory.T.mirabolic_filtration_exhaustive k (n + 1)) f g hf hg hfg

end GlobalTheory.CompanionTheory.BZMir
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExactStatement
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_phi_minus_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ExPhiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exPhiMinus | exact GlobalTheory.CompanionTheory.BZMir.exPhiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMir.exPhiMinus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMir

theorem exPsiMinus : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.BZMir.Fun.ExPsiMinus k := by
  intro k _ _ _ _ n V₁ V₂ V₃ _ _ _ _ _ _ τ₁ τ₂ τ₃ h₁ h₂ h₃ f g hf hg hfg
  refine GlobalTheory.T.twisted_jacquet_exact_smooth τ₁ τ₂ τ₃ h₁ h₂ h₃ (MirUin k n) 1 ?_ (GlobalTheory.T.mirabolic_filtration_exhaustive k n) f g hf hg hfg
  have hker : ((1 : MirUin k n →* ℂˣ).ker : Set (MirUin k n)) = Set.univ := by
    ext x
    simp
  rw [hker]
  exact isOpen_univ

end GlobalTheory.CompanionTheory.BZMir
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExactStatement
open GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_psi_minus_exact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.BZMir.Fun.ExPsiMinus k := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exPsiMinus | exact GlobalTheory.CompanionTheory.BZMir.exPsiMinus | (intros; apply GlobalTheory.CompanionTheory.BZMir.exPsiMinus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetReps
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetReps
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CosetReps

theorem exists_fin_coset_reps (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (J H A : Subgroup G) (hJ : IsCompact (J : Set G)) (hH : IsOpen (H : Set G))
    (_hHJ : H ≤ J) (_hAJ : A ≤ J) (hcov : ∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ H) :
    ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ A) ∧
      ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H := by
  classical
  obtain ⟨t, ht⟩ := hJ.elim_finite_subcover
    (fun a : A => (fun y : G => (a : G)⁻¹ * y) ⁻¹' (H : Set G))
    (fun a => hH.preimage (continuous_const.mul continuous_id))
    (fun y hy => by
      obtain ⟨a, ha, hay⟩ := hcov y hy
      exact Set.mem_iUnion.2 ⟨⟨a, ha⟩, hay⟩)
  let T : Finset (G ⧸ H) := t.image (fun a : A => ((a : G) : G ⧸ H))
  have rep : ∀ q : T, ∃ a : A, ((a : G) : G ⧸ H) = q := by
    rintro ⟨q, hq⟩
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨a, rfl⟩
  choose f hf using rep
  have key : ∀ y ∈ J, ((y : G) : G ⧸ H) ∈ T := by
    intro y hy
    obtain ⟨a, hat, hay⟩ := Set.mem_iUnion₂.1 (ht hy)
    exact Finset.mem_image.2 ⟨a, hat, QuotientGroup.eq.2 hay⟩
  let e : T ≃ Fin T.card := T.equivFin
  have main : ∀ y ∈ J, ∃! i, ((f (e.symm i) : A) : G)⁻¹ * y ∈ H := by
    intro y hy
    refine ⟨e ⟨_, key y hy⟩, ?_, ?_⟩
    · refine QuotientGroup.eq.1 ?_
      rw [Equiv.symm_apply_apply, hf]
    · intro i hi
      have h1 : (((f (e.symm i) : A) : G) : G ⧸ H) = ((y : G) : G ⧸ H) := QuotientGroup.eq.2 hi
      rw [hf] at h1
      rw [← Equiv.symm_apply_eq]
      exact Subtype.ext h1
  obtain ⟨i₀, -⟩ := main 1 J.one_mem
  exact ⟨T.card, i₀.pos, fun i => ((f (e.symm i) : A) : G), fun i => (f (e.symm i)).2, main⟩

end GlobalTheory.CompanionTheory.CosetReps
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactGroupFiniteCosetRepsStatement
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_group_finite_coset_reps : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J H A : Subgroup G), IsCompact (J : Set G) → IsOpen (H : Set G) → H ≤ J → A ≤ J → (∀ y ∈ J, ∃ a ∈ A, a⁻¹ * y ∈ H) → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → G, (∀ i, x i ∈ A) ∧ ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ H := by
  first | exact @GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps | exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps | (intros; apply GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationOperations
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct
open GlobalTheory.WeilDeligne LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.RelOpsLeaf

section Linear

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']

theorem eq_det_smul_one (hV : finrank ℂ V = 1) (f : Module.End ℂ V) :
    f = LinearMap.det f • (1 : Module.End ℂ V) := by
  have hm := LinearMap.charpoly_monic f
  have hd : f.charpoly.natDegree = 1 := by rw [LinearMap.charpoly_natDegree, hV]
  have h1 := hm.eq_X_add_C hd
  have h2 := LinearMap.aeval_self_charpoly f
  obtain ⟨t, ht⟩ : ∃ t : ℂ, f = t • (1 : Module.End ℂ V) := by
    refine ⟨-f.charpoly.coeff 0, ?_⟩
    rw [h1, map_add (f := _), aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at h2
    rw [neg_smul, eq_neg_iff_add_eq_zero]
    exact h2
  subst ht
  rw [LinearMap.det_smul, hV, pow_one]
  simp

theorem charpoly_smul_eq_scaleRoots (f : Module.End ℂ V) {t : ℂ} (ht : t ≠ 0) :
    (t • f).charpoly = f.charpoly.scaleRoots t := by
  refine Polynomial.funext fun z => ?_
  have h0 : t * (z / t) = z := by field_simp
  have h1 := scaleRoots_eval₂_mul (p := f.charpoly) (RingHom.id ℂ) (z / t) t
  simp only [RingHom.id_apply, h0, eval₂_id] at h1
  rw [h1, LinearMap.eval_charpoly, LinearMap.eval_charpoly, LinearMap.charpoly_natDegree,
    ← LinearMap.det_smul]
  congr 1
  rw [smul_sub, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_smul, h0]

theorem charpoly_map_one (hV' : finrank ℂ V' = 1) (f : Module.End ℂ V) :
    (TensorProduct.map f (1 : Module.End ℂ V')).charpoly = f.charpoly := by
  let e : V' ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by rw [hV', finrank_self])
  let F : (V ⊗[ℂ] V') ≃ₗ[ℂ] V :=
    (TensorProduct.congr (LinearEquiv.refl ℂ V) e).trans (TensorProduct.rid ℂ V)
  have key : ∀ u, F (TensorProduct.map f (1 : Module.End ℂ V') u) = f (F u) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [F]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← LinearEquiv.charpoly_conj F]
  congr 1
  refine LinearMap.ext fun v => ?_
  obtain ⟨u, rfl⟩ := F.surjective v
  simp [LinearEquiv.conj_apply, key]

end Linear

theorem pow_of_mul_eq_pow {p q : ℂ[X]} {m n : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m) (hqd : q.natDegree = n) (h : p * q = (X - 1) ^ (m + n)) :
    p = (X - 1) ^ m ∧ q = (X - 1) ^ n := by
  have e : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [e] at h ⊢
  have key : ∀ {r : ℂ[X]}, r.Monic → r ∣ (X - C 1) ^ (m + n) → r = (X - C 1) ^ r.natDegree := by
    intro r hr hd
    obtain ⟨i, -, hi⟩ := (dvd_prime_pow (prime_X_sub_C (1 : ℂ)) _).1 hd
    have h1 := eq_of_monic_of_associated hr ((monic_X_sub_C (1 : ℂ)).pow i) hi
    have h2 : r.natDegree = i := by rw [h1, natDegree_pow, natDegree_X_sub_C, mul_one]
    rw [h2]
    exact h1
  subst hpd hqd
  exact ⟨key hp (Dvd.intro _ h), key hq (Dvd.intro_left _ h)⟩

section Rel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_char_of_lpDim_eq_one (c : WD h) (hc : c.lpDim = 1) :
    ∃ χ : ↥(Weil h) →* ℂˣ, ∀ (x : WD h) (g : ↥(Weil h)),
      (x.lpChar c).charPol g = (x.charPol g).scaleRoots (χ g : ℂ) := by
  induction c using WD.ind with
  | hP m b =>
    rw [WD.lpDim_mk] at hc
    let f : ↥(Weil h) →* ℂ := (LinearMap.det : Module.End ℂ (Fin m → ℂ) →* ℂ).comp b.ρ
    refine ⟨f.toHomUnits, fun x g => ?_⟩
    induction x using WD.ind with
    | hP n a =>
      have hb : b.ρ g = ((f.toHomUnits g : ℂˣ) : ℂ) • (1 : Module.End ℂ (Fin m → ℂ)) := by
        rw [MonoidHom.coe_toHomUnits]
        exact eq_det_smul_one hc (b.ρ g)
      rw [WD.lpChar_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tensor_ρ, hb,
        TensorProduct.map_smul_right, charpoly_smul_eq_scaleRoots _ (Units.ne_zero _),
        charpoly_map_one hc]

end Rel

end GlobalTheory.CompanionTheory.RelOpsLeaf
end
end
