module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrdSubConjEqNeg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecompositionGroupLocalGaloisIso

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
noncomputable section
open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier
namespace GlobalTheory.CompanionTheory.MirLevi
variable {k : Type} [Field k]

def uv (n : ℕ) (v : Fin n → k) : Mir k n := unipIn k n (Multiplicative.ofAdd v)


variable (k) in
def LH (n : ℕ) : Subgroup (Mir k n) := (levi k n).range


variable (k) in
def lv (n : ℕ) : GL (Fin n) k →* LH k n := (levi k n).rangeRestrict

def colv {n : ℕ} (g : Mir k n) : Fin n → k :=
  fun i => ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)

def mvec {n : ℕ} (g : Mir k n) : Fin n → k :=
  (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec (colv g)

theorem mirProj_levi (n : ℕ) (m : GL (Fin n) k) : mirabolicProjection k n (levi k n m) = m := by
  apply Units.ext
  ext i j
  show GlobalTheory.BZMir.glEmbMat k n (m : Matrix (Fin n) (Fin n) k) (Fin.castSucc i) (Fin.castSucc j) = _
  simp [GlobalTheory.BZMir.glEmbMat]

theorem mirProj_uv (n : ℕ) (v : Fin n → k) : mirabolicProjection k n (uv n v) = 1 := by
  apply Units.ext
  ext i j
  show (1 + GlobalTheory.BZMir.colMat k n v) (Fin.castSucc i) (Fin.castSucc j) = (1 : Matrix (Fin n) (Fin n) k) i j
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem coe_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    (((levi k n m * uv n v : Mir k n) : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      glEmbMat k n (m : Matrix (Fin n) (Fin n) k) + colMat k n ((m : Matrix (Fin n) (Fin n) k).mulVec v) := by
  show GlobalTheory.BZMir.glEmbMat k n (m : Matrix (Fin n) (Fin n) k) * (1 + GlobalTheory.BZMir.colMat k n v) = _
  rw [mul_add, mul_one, GlobalTheory.BZMir.glEmbMat_mul_colMat]

theorem colv_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    colv (levi k n m * uv n v) = (m : Matrix (Fin n) (Fin n) k).mulVec v := by
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv]
  rw [GlobalTheory.CompanionTheory.MirLevi.coe_levi_mul_uv]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat]

theorem mvec_levi_mul_uv (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    mvec (levi k n m * uv n v) = v := by
  unfold GlobalTheory.CompanionTheory.MirLevi.mvec
  rw [GlobalTheory.CompanionTheory.MirLevi.colv_levi_mul_uv, map_mul, GlobalTheory.CompanionTheory.MirLevi.mirProj_levi,
    GlobalTheory.CompanionTheory.MirLevi.mirProj_uv, mul_one, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem decomp {n : ℕ} (g : Mir k n) : g = levi k n (mirabolicProjection k n g) * uv n (mvec g) := by
  have hA : ((GlobalTheory.BZMir.mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec
      (GlobalTheory.CompanionTheory.MirLevi.mvec g) = GlobalTheory.CompanionTheory.MirLevi.colv g := by
    unfold GlobalTheory.CompanionTheory.MirLevi.mvec
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hP : ∀ i j, ((GlobalTheory.BZMir.mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) :=
    fun _ _ => rfl
  have hlast := (GlobalTheory.BZMir.mem_Mir_iff k (g : GL (Fin (n + 1)) k)).1 g.2
  apply Subtype.ext
  apply Units.ext
  rw [GlobalTheory.CompanionTheory.MirLevi.coe_levi_mul_uv, hA]
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [congrFun hlast j]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast]
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.BZMir.eLast, Pi.single_apply,
        Fin.castSucc_ne_last]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, GlobalTheory.CompanionTheory.MirLevi.colv]
    · simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, hP, Fin.castSucc_ne_last]

theorem mvec_uv (n : ℕ) (v : Fin n → k) : mvec (uv n v) = v := by
  have h := GlobalTheory.CompanionTheory.MirLevi.mvec_levi_mul_uv n (1 : GL (Fin n) k) v
  rwa [map_one, one_mul] at h

theorem mvec_levi_mul (n : ℕ) (m : GL (Fin n) k) (g : Mir k n) : mvec (levi k n m * g) = mvec g := by
  conv_lhs => rw [GlobalTheory.CompanionTheory.MirLevi.decomp g, ← mul_assoc, ← map_mul]
  rw [GlobalTheory.CompanionTheory.MirLevi.mvec_levi_mul_uv]

theorem uv_add (n : ℕ) (v w : Fin n → k) : uv n (v + w) = uv n v * uv n w := by
  simp only [GlobalTheory.CompanionTheory.MirLevi.uv, ofAdd_add, map_mul]

theorem uv_zero (n : ℕ) : uv n (0 : Fin n → k) = 1 := by
  simp [GlobalTheory.CompanionTheory.MirLevi.uv]

theorem uv_mul_levi (n : ℕ) (m : GL (Fin n) k) (v : Fin n → k) :
    uv n v * levi k n m = levi k n m * uv n (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) := by
  apply Subtype.ext
  have h := GlobalTheory.BZMir.glEmb_mul_unip' k n m
    (Multiplicative.ofAdd (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v))
  rw [toAdd_ofAdd, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at h
  exact h.symm

section Rep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E] (ρ : Representation ℂ (LH k n) E)

def restr : cIndSpace (LH k n) ρ →ₗ[ℂ] (Fin n → k) → E where
  toFun f v := f.1.1.1 (uv n v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restr_injective : Function.Injective (restr ρ) := by
  intro f f' h
  have key : ∀ (F : GlobalTheory.PRep.cIndSpace (GlobalTheory.CompanionTheory.MirLevi.LH k n) ρ)
      (x : GlobalTheory.CompanionTheory.MirLevi.LH k n) (g : GlobalTheory.BZMir.Mir k n),
      F.1.1.1 ((x : GlobalTheory.BZMir.Mir k n) * g) = ρ x (F.1.1.1 g) := by
    intro F x g
    first
    | exact F.1.1.2 x g
    | exact F.1.2 x g
    | exact F.2 x g
    | simpa using F.1.1.2 x g
  have hv : ∀ v, f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v) = f'.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v) :=
    fun v => congrFun h v
  have hall : ∀ g, f.1.1.1 g = f'.1.1.1 g := by
    intro g
    have e : GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n g) =
        ((GlobalTheory.CompanionTheory.MirLevi.lv k n (GlobalTheory.BZMir.mirabolicProjection k n g) :
          GlobalTheory.CompanionTheory.MirLevi.LH k n) : GlobalTheory.BZMir.Mir k n) := rfl
    rw [GlobalTheory.CompanionTheory.MirLevi.decomp g, e, key f, key f', hv]
  first
  | exact Subtype.ext (Subtype.ext (Subtype.ext (funext hall)))
  | exact Subtype.ext (Subtype.ext (Subtype.ext (by ext g; exact hall g)))

theorem restr_uv (a : Fin n → k) (f : cIndSpace (LH k n) ρ) (v : Fin n → k) :
    restr ρ (cInd (LH k n) ρ (uv n a) f) v = restr ρ f (v + a) := by
  show f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v * GlobalTheory.CompanionTheory.MirLevi.uv n a) = _
  exact congrArg (fun g => f.1.1.1 g) (GlobalTheory.CompanionTheory.MirLevi.uv_add n v a).symm

theorem restr_levi (m : GL (Fin n) k) (f : cIndSpace (LH k n) ρ) (v : Fin n → k) :
    restr ρ (cInd (LH k n) ρ (levi k n m) f) v =
      ρ (lv k n m) (restr ρ f (((m⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v)) := by
  have key : ∀ (x : GlobalTheory.CompanionTheory.MirLevi.LH k n) (g : GlobalTheory.BZMir.Mir k n),
      f.1.1.1 ((x : GlobalTheory.BZMir.Mir k n) * g) = ρ x (f.1.1.1 g) := by
    intro x g
    first
    | exact f.1.1.2 x g
    | exact f.1.2 x g
    | exact f.2 x g
    | simpa using f.1.1.2 x g
  have e : GlobalTheory.BZMir.levi k n m =
      ((GlobalTheory.CompanionTheory.MirLevi.lv k n m : GlobalTheory.CompanionTheory.MirLevi.LH k n) : GlobalTheory.BZMir.Mir k n) := rfl
  show f.1.1.1 (GlobalTheory.CompanionTheory.MirLevi.uv n v * GlobalTheory.BZMir.levi k n m) = _
  rw [GlobalTheory.CompanionTheory.MirLevi.uv_mul_levi, e, key]
  rfl

end Rep

end GlobalTheory.CompanionTheory.MirLevi
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureData
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.Grp

section Alg

variable {k : Type} [Field k]

theorem mirProj_eq_one_of_mem {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) : mirabolicProjection k n u = 1 := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 hu : ((u : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Units.ext
  ext a b
  show ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _
  rw [← hv]
  simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one' {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) : u ∈ MirUin k n := by
  have hb : ∀ a b : Fin n, ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = if a = b then 1 else 0 := by
    intro a b
    have := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) a b) hu
    exact (this : ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.castSucc b) = _).trans (by simp [Matrix.one_apply])
  have hl := (mem_Mir_iff k (u : GL (Fin (n + 1)) k)).1 u.2
  refine Subgroup.mem_subgroupOf.2 ⟨Multiplicative.ofAdd fun a => ((u : GL (Fin (n + 1)) k) : Matrix _ _ k) (Fin.castSucc a) (Fin.last n), ?_⟩
  apply Units.ext
  ext a b
  have hlb := congrFun hl b
  induction a using Fin.lastCases with
  | last =>
    rw [hlb]
    induction b using Fin.lastCases <;> simp [unip, colMat, Matrix.one_apply, eLast, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]
  | cast a =>
    induction b using Fin.lastCases with
    | last => simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast b =>
      rw [hb]
      simp [unip, colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mirUin_normal (n : ℕ) : (MirUin k n).Normal := by
  refine ⟨fun u hu g => mem_of_mirProj_eq_one' _ ?_⟩
  rw [map_mul, map_mul, mirProj_eq_one_of_mem u hu, mul_one, map_inv, mul_inv_cancel]

theorem mirUin_comm {n : ℕ} {a b : Mir k n} (ha : a ∈ MirUin k n) (hb : b ∈ MirUin k n) : a * b = b * a := by
  obtain ⟨v, hv⟩ := (Subgroup.mem_subgroupOf.1 ha : ((a : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 hb : ((b : Mir k n) : GL (Fin (n + 1)) k) ∈ MirU k n)
  apply Subtype.ext
  show (a : GL (Fin (n + 1)) k) * (b : GL (Fin (n + 1)) k) = (b : GL (Fin (n + 1)) k) * (a : GL (Fin (n + 1)) k)
  rw [← hv, ← hw, ← map_mul, mul_comm, map_mul]

def prodSub {n : ℕ} (L₁ L₂ : Subgroup (Mir k n)) (h₁ : L₁ ≤ MirUin k n) (h₂ : L₂ ≤ MirUin k n) : Subgroup (Mir k n) where
  carrier := (L₁ : Set (Mir k n)) * (L₂ : Set (Mir k n))
  one_mem' := ⟨1, L₁.one_mem, 1, L₂.one_mem, one_mul 1⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨c, hc, d, hd, rfl⟩
    refine ⟨a * c, L₁.mul_mem ha hc, b * d, L₂.mul_mem hb hd, ?_⟩
    show a * c * (b * d) = a * b * (c * d)
    rw [mul_assoc a c, ← mul_assoc c b, mirUin_comm (h₁ hc) (h₂ hb)]
    simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    refine ⟨a⁻¹, L₁.inv_mem ha, b⁻¹, L₂.inv_mem hb, ?_⟩
    show a⁻¹ * b⁻¹ = (a * b)⁻¹
    rw [_root_.mul_inv_rev]
    exact mirUin_comm (MirUin k n |>.inv_mem (h₁ ha)) (MirUin k n |>.inv_mem (h₂ hb))

theorem hpg_entry {i t : ℕ} (g : Mir k ((i + 1) + t + 1)) (hg : g ∈ HPG k (i + 1) (t + 1))
    (l : Fin ((i + 1) + t + 2)) (hl : i < l.val) (hl2 : l.val ≠ (i + 1) + t + 1) (c : Fin (i + 1)) :
    ((g : GL (Fin ((i + 1) + t + 2)) k) : Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) l
      (Fin.castLE (by omega) c) = 0 := by
  have hp : (g : GL (Fin ((i + 1) + (t + 1) + 1)) k) ∈ GlobalTheory.SmGL.parab k (ePG (i + 1) (t + 1)) := hg
  have hlt := l.isLt
  have h0 := mem_parab_iff.1 hp true false (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1)) (Fin.castSucc c : Fin (i + 1 + 1)) (by decide)
  have e1 : ePG (i + 1) (t + 1) ⟨true, (⟨l.val - (i + 1), by omega⟩ : Fin (t + 1))⟩ = l := by
    apply Fin.ext
    simp [ePG, two]
    omega
  have e2 : ePG (i + 1) (t + 1) ⟨false, (Fin.castSucc c : Fin (i + 1 + 1))⟩ = Fin.castLE (by omega) c := by
    apply Fin.ext
    simp [ePG, two]
  rw [e1, e2] at h0
  exact h0

theorem Cl_left {i t : ℕ} (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + t + 1))
    (hx : x ∈ Cl k i t) : h * x ∈ Cl k i t := by
  intro c
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases h1 : l.val ≤ i
  · have := hx ⟨l.val, by omega⟩
    have e : Fin.castLE (by omega) (⟨l.val, by omega⟩ : Fin (i + 1)) = l := Fin.ext rfl
    rw [e] at this
    rw [this, zero_mul]
  · by_cases h2 : l.val = (i + 1) + t + 1
    · have e : l = Fin.last _ := Fin.ext h2
      have hm := (mem_Mir_iff k ((h⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (h⁻¹).2
      have hc := congrFun hm (Fin.castLE (by omega) c)
      rw [e, hc]
      have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
        intro e'
        have := congrArg Fin.val e'
        simp at this
        omega
      simp [eLast, Pi.single_apply, this]
    · rw [hpg_entry _ ((HPG k (i + 1) (t + 1)).inv_mem hh) l (by omega) h2 c, mul_zero]

theorem Cl_right {i t : ℕ} (x : Mir k ((i + 1) + t + 1)) (hx : x ∈ Cl k i t) (u : Mir k ((i + 1) + t + 1))
    (hu : u ∈ MirUin k ((i + 1) + t + 1)) : x * u ∈ Cl k i t := by
  intro c
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 ((MirUin k ((i + 1) + t + 1)).inv_mem hu) :
    ((u⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) ∈ MirU k ((i + 1) + t + 1))
  rw [_root_.mul_inv_rev]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [← hw]
  have hv : ((unip k ((i + 1) + t + 1) w : GL (Fin ((i + 1) + t + 2)) k) :
      Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) = 1 + colMat k _ w.toAdd := rfl
  rw [hv, add_mul, one_mul, Matrix.add_apply, hx c, zero_add, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  by_cases hl : l = Fin.last _
  · have hm := (mem_Mir_iff k ((x⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k)).1 (x⁻¹).2
    have hc := congrFun hm (Fin.castLE (by omega) c)
    rw [hl, hc]
    have : Fin.castLE (by omega) c ≠ Fin.last ((i + 1) + t + 1) := by
      intro e'
      have := congrArg Fin.val e'
      simp at this
      omega
    simp [eLast, Pi.single_apply, this]
  · simp [colMat, hl]

end Alg

section Top

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mirChar_ker_open (ψ : AddChar k Circle) (hψ : Continuous ψ) (n : ℕ) :
    IsOpen ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) := by
  have he : ((mirChar k ψ n).ker : Set (MirUin k (n + 1))) =
      (fun u : MirUin k (n + 1) => GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n)) ⁻¹' {x : k | ψ x = 1} := by
    ext u
    obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
    have hl : GlobalTheory.CompanionTheory.BZFun.lastCol k u (Fin.last n) = w.toAdd (Fin.last n) := by
      simp only [GlobalTheory.CompanionTheory.BZFun.lastCol, ← hw]
      exact unip_apply_castSucc_last k (n + 1) w _
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_setOf_eq, hl,
      mirChar_eq k ψ n u w hw.symm]
    constructor
    · intro h
      apply Circle.ext
      simpa using congrArg Units.val h
    · intro h
      rw [h, map_one]
  rw [he]
  exact (GlobalTheory.CompanionTheory.BZFun.isOpen_addChar_eq_one k ψ hψ).preimage
    ((continuous_apply _).comp (GlobalTheory.CompanionTheory.BZFun.continuous_lastCol k (n + 1)))

theorem isClosed_Cl (i t : ℕ) : IsClosed (Cl k i t) := by
  have hc : Continuous fun p : Mir k ((i + 1) + t + 1) =>
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  have he : Cl k i t = ⋂ c : Fin (i + 1), {p : Mir k ((i + 1) + t + 1) |
      (((p⁻¹ : Mir k ((i + 1) + t + 1)) : GL (Fin ((i + 1) + t + 2)) k) :
        Matrix (Fin ((i + 1) + t + 2)) (Fin ((i + 1) + t + 2)) k)
        (Fin.castSucc (Fin.last ((i + 1) + t))) (Fin.castLE (by omega) c) = 0} := by
    ext p
    simp [Cl]
  rw [he]
  exact isClosed_iInter fun c => isClosed_eq (hc.matrix_elem _ _) continuous_const

end Top

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ),
  (MirUin k ((i + 1) + t + 1)).Normal ∧ IsOpen ((mirChar k ψ ((i + 1) + t)).ker : Set (MirUin k ((i + 1) + t + 1))) ∧
    IsClosed (Cl k i t) ∧ (∀ h ∈ HPG k (i + 1) (t + 1), ∀ x ∈ Cl k i t, h * x ∈ Cl k i t) ∧
    (∀ x ∈ Cl k i t, ∀ u ∈ MirUin k ((i + 1) + t + 1), x * u ∈ Cl k i t) ∧
    ∀ L₁ L₂ : Subgroup (Mir k ((i + 1) + t + 1)), L₁ ≤ MirUin k ((i + 1) + t + 1) → L₂ ≤ MirUin k ((i + 1) + t + 1) →
      IsCompact (L₁ : Set (Mir k ((i + 1) + t + 1))) → IsCompact (L₂ : Set (Mir k ((i + 1) + t + 1))) →
      ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L ≤ MirUin k ((i + 1) + t + 1) ∧ IsCompact (L : Set (Mir k ((i + 1) + t + 1))) ∧
        L₁ ≤ L ∧ L₂ ≤ L := by
  intro k _ _ _ _ ψ hψ i t
  refine ⟨mirUin_normal _, mirChar_ker_open ψ hψ _, isClosed_Cl i t, fun h hh x hx => Cl_left h hh x hx,
    fun x hx u hu => Cl_right x hx u hu, fun L₁ L₂ h₁ h₂ c₁ c₂ => ⟨prodSub L₁ L₂ h₁ h₂, ?_, ?_, ?_, ?_⟩⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (MirUin k _).mul_mem (h₁ ha) (h₂ hb)
  · exact (c₁.mul c₂ : IsCompact ((L₁ : Set (Mir k ((i + 1) + t + 1))) * (L₂ : Set (Mir k ((i + 1) + t + 1)))))
  · intro a ha
    exact ⟨a, ha, 1, L₂.one_mem, mul_one a⟩
  · intro b hb
    exact ⟨1, L₁.one_mem, b, hb, one_mul b⟩

end GlobalTheory.CompanionTheory.BZPhiPG.Grp

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCellStructureDataStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_cell_structure_data : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ),
  (MirUin k ((i + 1) + t + 1)).Normal ∧ IsOpen ((mirChar k ψ ((i + 1) + t)).ker : Set (MirUin k ((i + 1) + t + 1))) ∧
    IsClosed (Cl k i t) ∧ (∀ h ∈ HPG k (i + 1) (t + 1), ∀ x ∈ Cl k i t, h * x ∈ Cl k i t) ∧
    (∀ x ∈ Cl k i t, ∀ u ∈ MirUin k ((i + 1) + t + 1), x * u ∈ Cl k i t) ∧
    ∀ L₁ L₂ : Subgroup (Mir k ((i + 1) + t + 1)), L₁ ≤ MirUin k ((i + 1) + t + 1) → L₂ ≤ MirUin k ((i + 1) + t + 1) →
      IsCompact (L₁ : Set (Mir k ((i + 1) + t + 1))) → IsCompact (L₂ : Set (Mir k ((i + 1) + t + 1))) →
      ∃ L : Subgroup (Mir k ((i + 1) + t + 1)), L ≤ MirUin k ((i + 1) + t + 1) ∧ IsCompact (L : Set (Mir k ((i + 1) + t + 1))) ∧
        L₁ ≤ L ∧ L₂ ≤ L := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Grp.main | exact GlobalTheory.CompanionTheory.BZPhiPG.Grp.main | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Grp.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

def fibM (X Z : Type) [TopologicalSpace X] [AddCommGroup Z] [Module ℂ Z] : Submodule ℂ (X → Z) where
  carrier := {φ | IsLocallyConstant φ ∧ HasCompactSupport φ}
  add_mem' ha hb := ⟨ha.1.add hb.1, ha.2.add hb.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c φ hφ := ⟨hφ.1.comp (fun z => c • z), hφ.2.comp_left (g := fun z => c • z) (smul_zero c)⟩

section Cols

variable {k : Type}

def topP (i t : ℕ) (y : Fin (i + t) → k) : Fin i → k := fun j => y (Fin.castAdd t j)

def middlePart (i t : ℕ) (y : Fin (i + t) → k) : Fin t → k := fun j => y (Fin.natAdd i j)

theorem middlePart_add [Add k] (i t : ℕ) (a b : Fin (i + t) → k) : middlePart i t (a + b) = middlePart i t a + middlePart i t b := rfl

theorem continuous_topP [TopologicalSpace k] (i t : ℕ) : Continuous (topP (k := k) i t) :=
  continuous_pi fun _ => continuous_apply _

theorem continuous_midP [TopologicalSpace k] (i t : ℕ) : Continuous (middlePart (k := k) i t) :=
  continuous_pi fun _ => continuous_apply _

end Cols

section Act

variable {k Z : Type} [AddCommGroup k] [TopologicalSpace k] [IsTopologicalAddGroup k] [AddCommGroup Z] [Module ℂ Z]

def fibAct {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) :
    Representation ℂ (Multiplicative (Fin (i + t) → k)) (fibM (Fin t → k) Z) where
  toFun y :=
    { toFun := fun φ => ⟨fun v => ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)), by
        have hh : Continuous fun v : Fin t → k => v + middlePart i t y.toAdd := continuous_id.add continuous_const
        have hl : IsLocallyConstant fun v : Fin t → k => φ.1 (v + middlePart i t y.toAdd) := φ.2.1.comp_continuous hh
        have hc : HasCompactSupport fun v : Fin t → k => φ.1 (v + middlePart i t y.toAdd) :=
          φ.2.2.comp_homeomorph (Homeomorph.addRight (middlePart i t y.toAdd))
        exact ⟨hl.comp _, hc.comp_left (map_zero _)⟩⟩
      map_add' := fun a b => by
        apply Subtype.ext
        funext v
        exact map_add _ _ _
      map_smul' := fun c a => by
        apply Subtype.ext
        funext v
        exact map_smul _ _ _ }
  map_one' := by
    ext φ v
    show ρ₀ (Multiplicative.ofAdd (topP i t 0)) (φ.1 (v + middlePart i t 0)) = φ.1 v
    have h1 : Multiplicative.ofAdd (topP (k := k) i t 0) = 1 := rfl
    have h2 : middlePart (k := k) i t 0 = 0 := rfl
    rw [h1, h2, map_one, add_zero]
    rfl
  map_mul' a b := by
    ext φ v
    show ρ₀ (Multiplicative.ofAdd (topP i t (a.toAdd + b.toAdd))) (φ.1 (v + middlePart i t (a.toAdd + b.toAdd))) =
      ρ₀ (Multiplicative.ofAdd (topP i t a.toAdd)) (ρ₀ (Multiplicative.ofAdd (topP i t b.toAdd)) (φ.1 (v + middlePart i t a.toAdd + middlePart i t b.toAdd)))
    have h1 : Multiplicative.ofAdd (topP i t (a.toAdd + b.toAdd)) =
        Multiplicative.ofAdd (topP i t a.toAdd) * Multiplicative.ofAdd (topP i t b.toAdd) := rfl
    rw [h1, map_mul, middlePart_add, add_assoc]
    rfl

theorem fibAct_apply {i : ℕ} (t : ℕ) (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z)
    (y : Multiplicative (Fin (i + t) → k)) (φ : fibM (Fin t → k) Z) (v : Fin t → k) :
    (fibAct t ρ₀ y φ).1 v = ρ₀ (Multiplicative.ofAdd (topP i t y.toAdd)) (φ.1 (v + middlePart i t y.toAdd)) := rfl

end Act

section Field

variable {k : Type} [Field k]

def uMh (k : Type) [Field k] (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n where
  toFun y := uM k n y.toAdd
  map_one' := uM_zero k n
  map_mul' a b := uM_add k n a.toAdd b.toAdd

def mulH {n : ℕ} (κ : GL (Fin n) k) : Multiplicative (Fin n → k) →* Multiplicative (Fin n → k) where
  toFun y := Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec y.toAdd)
  map_one' := by
    show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec 0) = 1
    rw [Matrix.mulVec_zero]
    rfl
  map_mul' a b := by
    show Multiplicative.ofAdd ((κ : Matrix (Fin n) (Fin n) k).mulVec (a.toAdd + b.toAdd)) = _
    rw [Matrix.mulVec_add]
    rfl

def topRep {i : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k i) V)
    (W : Type) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ (Multiplicative (Fin i → k)) (V ⊗[ℂ] W) where
  toFun x := LinearMap.rTensor W (τ (uM k i x.toAdd))
  map_one' := by
    show LinearMap.rTensor W (τ (uM k i 0)) = 1
    rw [uM_zero, map_one]
    exact LinearMap.rTensor_id _ _
  map_mul' a b := by
    show LinearMap.rTensor W (τ (uM k i (a.toAdd + b.toAdd))) = _
    rw [uM_add, map_mul]
    exact LinearMap.rTensor_mul _ _ _

end Field

section Lat

variable {k : Type} [Field k] [ValuativeRel k]

def Lc (n : ℕ) (c : k) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {y | ∀ j, c * y.toAdd j ∈ 𝒪[k]}
  mul_mem' := by
    intro a b ha hb j
    have : c * (a * b).toAdd j = c * a.toAdd j + c * b.toAdd j := mul_add _ _ _
    rw [this]
    exact add_mem (ha j) (hb j)
  one_mem' := by
    intro j
    have : c * (1 : Multiplicative (Fin n → k)).toAdd j = 0 := mul_zero _
    rw [this]
    exact zero_mem _
  inv_mem' := by
    intro a ha j
    have : c * (a⁻¹).toAdd j = - (c * a.toAdd j) := by
      show c * (- a.toAdd j) = _
      ring
    rw [this]
    exact neg_mem (ha j)

theorem mem_Lc {n : ℕ} {c : k} {y : Multiplicative (Fin n → k)} : y ∈ Lc n c ↔ ∀ j, c * y.toAdd j ∈ 𝒪[k] := Iff.rfl

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_Lc (n : ℕ) (c : k) : IsOpen (Lc n c : Set (Multiplicative (Fin n → k))) := by
  have hset : (Lc n c : Set (Multiplicative (Fin n → k))) =
      ⋂ j, (fun y : Multiplicative (Fin n → k) => c * y.toAdd j) ⁻¹' (𝒪[k] : Set k) := by
    ext y
    simp only [SetLike.mem_coe, mem_Lc, Set.mem_iInter, Set.mem_preimage]
  rw [hset]
  have hO : IsOpen (𝒪[k] : Set k) := by exact Valuation.isOpen_integer
  exact isOpen_iInter_of_finite fun j =>
    hO.preimage (continuous_const.mul ((continuous_apply j).comp continuous_toAdd))

theorem isCompact_Lc (n : ℕ) {c : k} (hc : c ≠ 0) : IsCompact (Lc n c : Set (Multiplicative (Fin n → k))) := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n => {x : k | valuation k x ≤ 1}) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k 1
  have hf : Continuous fun x : Fin n → k => Multiplicative.ofAdd (c⁻¹ • x) :=
    continuous_ofAdd.comp (continuous_const_smul _)
  convert hK.image hf using 1
  ext y
  constructor
  · intro hy
    refine ⟨c • y.toAdd, fun j _ => ?_, ?_⟩
    · have h := mem_Lc.1 hy j
      rw [Valuation.mem_integer_iff] at h
      simpa using h
    · simp [smul_smul, hc]
  · rintro ⟨x, hx, rfl⟩
    refine mem_Lc.2 fun j => ?_
    rw [Valuation.mem_integer_iff]
    simpa [smul_smul, hc] using hx j trivial

end Lat

section Coset

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Z : Type} [AddCommGroup Z] [Module ℂ Z]

def cosetSet (t : ℕ) (c : k) (a : Fin t → k) : Set (Fin t → k) :=
  {v | Multiplicative.ofAdd (v - a) ∈ Lc t c}

theorem isClopen_cosetSet (t : ℕ) (c : k) (a : Fin t → k) : IsClopen (cosetSet t c a) := by
  have hcont : Continuous fun v : Fin t → k => Multiplicative.ofAdd (v - a) :=
    continuous_ofAdd.comp (continuous_id.sub continuous_const)
  have h1 : IsOpen (Lc t c : Set (Multiplicative (Fin t → k))) := isOpen_Lc t c
  exact ⟨(Subgroup.isClosed_of_isOpen _ h1).preimage hcont, h1.preimage hcont⟩

theorem isCompact_cosetSet (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) : IsCompact (cosetSet t c a) := by
  have h := (isCompact_Lc t hc).image (f := fun y : Multiplicative (Fin t → k) => y.toAdd + a)
    ((continuous_toAdd).add continuous_const)
  convert h using 1
  ext v
  constructor
  · intro hv
    exact ⟨Multiplicative.ofAdd (v - a), hv, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    show Multiplicative.ofAdd (y.toAdd + a - a) ∈ Lc t c
    simpa using hy

def cosetFn (t : ℕ) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z : Z) : fibM (Fin t → k) Z :=
  ⟨(cosetSet t c a).indicator fun _ => z, by
      classical
      rw [IsLocallyConstant.iff_exists_open]
      intro x
      by_cases hx : x ∈ cosetSet t c a
      · exact ⟨_, (isClopen_cosetSet t c a).2, hx, fun y hy => by
          rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
      · exact ⟨_, (isClopen_cosetSet t c a).1.isOpen_compl, hx, fun y hy => by
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩,
    by
      haveI : T2Space k := inferInstance
      exact HasCompactSupport.intro (isCompact_cosetSet t hc a) fun x hx => Set.indicator_of_notMem hx _⟩

end Coset

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairIrreducibleUnlinked
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem terms_eq_first (Γ : Segment k) {u v : IrrGL (k := k)} (hu : Γ.first = u)
    (hΓ : Γ.carrier ⊆ {u} ∪ {v}) (hv : v ≠ u.nu 1) :
    ∀ a : ℕ, a < Γ.len → Γ.first.nu a = u := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [Nat.cast_zero, IrrGL.nu_zero, hu]
  | succ n ih =>
    intro hn
    have h1 : Γ.first.nu ((n + 1 : ℕ) : ℂ) = u.nu 1 := by
      rw [← ih (by omega), IrrGL.nu_nu, Nat.cast_succ]
    have hmem : Γ.first.nu ((n + 1 : ℕ) : ℂ) ∈ Γ.carrier := Segment.mem_carrier.2 ⟨n + 1, hn, rfl⟩
    rcases (Set.mem_union _ _ _).1 (hΓ hmem) with h | h
    · exact Set.mem_singleton_iff.1 h
    · exact absurd ((Set.mem_singleton_iff.1 h).symm.trans h1) hv

theorem not_linked_single {x y : IrrGL (k := k)} (hx : x.IsCusp) (hy : y.IsCusp) (h1 : y ≠ x.nu 1) (h2 : x ≠ y.nu 1) :
    ¬ (Segment.single x hx).Linked (Segment.single y hy) := by
  rintro ⟨⟨Γ, hΓ⟩, hxy, -⟩
  simp only [Segment.carrier_single] at hΓ hxy
  have hne : x ≠ y := fun h => hxy (by subst h; exact subset_rfl)
  have key : ∀ u v : IrrGL (k := k), Γ.first = u → Γ.carrier ⊆ {u} ∪ {v} → v ≠ u.nu 1 → v ∈ Γ.carrier → v = u := by
    intro u v hu hsub hv hvmem
    obtain ⟨a, ha, hav⟩ := Segment.mem_carrier.1 hvmem
    rw [← hav]
    exact terms_eq_first Γ hu hsub hv a ha
  have hfirst : Γ.first ∈ Γ.carrier :=
    Segment.mem_carrier.2 ⟨0, Γ.len_pos, by rw [Nat.cast_zero, IrrGL.nu_zero]⟩
  rw [hΓ] at hfirst
  rcases (Set.mem_union _ _ _).1 hfirst with h | h
  · refine hne (key x y (Set.mem_singleton_iff.1 h) hΓ.subset h1 ?_).symm
    rw [hΓ]
    exact Set.mem_union_right _ (Set.mem_singleton y)
  · refine hne (key y x (Set.mem_singleton_iff.1 h) ?_ h2 ?_)
    · intro z hz
      rw [hΓ] at hz
      rcases (Set.mem_union _ _ _).1 hz with hz | hz
      · exact Set.mem_union_right _ hz
      · exact Set.mem_union_left _ hz
    · rw [hΓ]
      exact Set.mem_union_left _ (Set.mem_singleton x)

end GlobalTheory.CompanionTheory.BZPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramified
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.UnrCM

theorem algebraMap_int_ringOfIntegers_surjective (F : Type) [Field F] [NumberField F]
    (h : Module.finrank ℚ F = 1) : Function.Surjective (algebraMap ℤ (𝓞 F)) := by
  intro x
  obtain ⟨q, hq⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2 (x : F)
  have hx : IsIntegral ℤ (x : F) := x.isIntegral_coe
  have hint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff).1 (hq.symm ▸ hx)
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  simpa using hq

theorem finrank_maximalRealSubfield_of_subsingleton (E : Type) [Field E] [NumberField E] [IsCMField E]
    [Subsingleton (InfinitePlace E)] : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
  have h1 : Fintype.card (InfinitePlace E) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 inferInstance) Fintype.card_pos
  have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  have h4 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have h5 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h5
  omega

theorem nontrivial_infinitePlace_of_forall_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hU : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Nontrivial (InfinitePlace E) := by
  by_contra hn
  haveI : Subsingleton (InfinitePlace E) := not_nontrivial_iff_subsingleton.1 hn
  have hF := finrank_maximalRealSubfield_of_subsingleton E
  have hE : Module.finrank ℚ E ≠ 1 := by
    have h5 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, hF] at h5
    omega
  obtain ⟨P, hP, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := E) (𝒪 := 𝓞 E) hE
  have hbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hw := hU ⟨P, hP.isPrime, hbot⟩
  apply hram
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P) := hw
  haveI : Algebra.FormallyUnramified ℤ (𝓞 (maximalRealSubfield E)) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ _)
      (algebraMap_int_ringOfIntegers_surjective _ hF)
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P)

theorem nontrivial_infinitePlace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) :=
  fun E _ _ _ hU => nontrivial_infinitePlace_of_forall_isUnramifiedAt E hU

end GlobalTheory.CompanionTheory.UnrCM
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramifiedStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_infinite_place_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) := by
  first | exact @GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | exact GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace | (intros; apply GlobalTheory.CompanionTheory.UnrCM.nontrivial_infinitePlace <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulMemBall
noncomputable section

open Matrix GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.BZPhiPG.Onto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' := add_mem_cball
  neg_mem' := neg_mem_cball

theorem mul_mem_ball {s : kˣ} (hs : valuation k (s : k) ≤ 1) {x y : k} (hx : x ∈ cball s)
    (hy : y ∈ cball s) : x * y ∈ cball s := by
  show valuation k (x * y) ≤ valuation k (s : k)
  rw [map_mul]
  calc valuation k x * valuation k y ≤ valuation k (s : k) * 1 :=
        mul_le_mul' hx (le_trans hy hs)
    _ = valuation k (s : k) := mul_one _

def NearOne (s : kˣ) {m : ℕ} (A : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ a b, A a b - (1 : Matrix (Fin m) (Fin m) k) a b ∈ cball s

theorem NearOne.mul {s : kˣ} (hs : valuation k (s : k) ≤ 1) {m : ℕ}
    {A B : Matrix (Fin m) (Fin m) k} (hA : NearOne s A) (hB : NearOne s B) : NearOne s (A * B) := by
  intro a b
  have e : (A * B) a b - (1 : Matrix (Fin m) (Fin m) k) a b =
      ((A - 1) * (B - 1)) a b + (A a b - (1 : Matrix (Fin m) (Fin m) k) a b) +
        (B a b - (1 : Matrix (Fin m) (Fin m) k) a b) := by
    have : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
    exact congrFun (congrFun this a) b
  rw [e]
  refine add_mem_cball (add_mem_cball ?_ (hA a b)) (hB a b)
  rw [Matrix.mul_apply]
  exact (ballSub s).sum_mem fun l _ => mul_mem_ball hs (hA a l) (hB l b)


variable (k) in
def congGL (s : kˣ) (hs : valuation k (s : k) ≤ 1) (m : ℕ) : Subgroup (GL (Fin m) k) where
  carrier := {g | NearOne s (g : Matrix (Fin m) (Fin m) k) ∧
    NearOne s ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)}
  one_mem' := by
    constructor <;> intro a b <;> simp [cball]
  mul_mem' := by
    rintro g h ⟨g1, g2⟩ ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact g1.mul hs h1
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact h2.mul hs g2
  inv_mem' := by
    rintro g ⟨g1, g2⟩
    exact ⟨g2, by simpa using g1⟩


variable (k) in
def congM (s : kˣ) (hs : valuation k (s : k) ≤ 1) (n : ℕ) : Subgroup (Mir k n) :=
  (congGL k s hs (n + 1)).comap (Mir k n).subtype

end GlobalTheory.CompanionTheory.BZPhiPG.Onto

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.DecGal

theorem exists_algHom_mulEquiv_dec : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∃ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (e : (AlgebraicClosure (v.adicCompletion F) ≃ₐ[v.adicCompletion F] AlgebraicClosure (v.adicCompletion F)) ≃* Dec (F := F) A), Continuous e ∧ Continuous e.symm ∧ ∀ σ x, ι (((e σ : Dec (F := F) A) : G F Ω) x) = σ (ι x) := by
  intro F Ω _ _ _ _ _ A v h
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v h
  obtain ⟨θ, hθ, hθ', hl⟩ := GlobalTheory.LocDec.decomposition_mulEquiv_galLoc F Ω A v h ι hι
  refine ⟨ι, θ.symm, hθ', hθ, fun σ x => ?_⟩
  have := hl (θ.symm σ) x
  rw [MulEquiv.apply_symm_apply] at this
  exact this.symm

end GlobalTheory.CompanionTheory.DecGal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDual
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDual
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.CompactAvg

theorem invariant_forms_separate_fixed :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G),
      IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J,
      (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  intro G _ _ _ J hJ V _ _ π hπ u hu hl
  obtain ⟨E, -, hfix, -, hinv, -⟩ := GlobalTheory.T.compact_fixed_vector_projection G J hJ V π hπ
  by_contra hne
  have hex : ∃ l0 : Module.Dual ℂ V, l0 u ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ u).1 hall)
  obtain ⟨l0, hl0⟩ := hex
  have hzero : (l0 ∘ₗ E) u = 0 := by
    refine hl (l0 ∘ₗ E) fun x hx => ?_
    rw [LinearMap.comp_assoc, hinv x hx]
  apply hl0
  simpa [hfix u hu] using hzero

end GlobalTheory.CompanionTheory.CompactAvg
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedVectorZeroOfDualStatement
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_vector_zero_of_dual : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (J : Subgroup G), IsCompact (J : Set G) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ u ∈ fixed π J, (∀ l : Module.Dual ℂ V, (∀ x ∈ J, l ∘ₗ π x = l) → l u = 0) → u = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed | exact GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed | (intros; apply GlobalTheory.CompanionTheory.CompactAvg.invariant_forms_separate_fixed <;> assumption)
end
end
