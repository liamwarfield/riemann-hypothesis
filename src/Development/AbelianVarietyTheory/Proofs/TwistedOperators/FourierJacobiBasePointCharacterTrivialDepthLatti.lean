module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEOffS0ColumnPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEOffS0ColumnPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.OffPl

variable {D : D7}

theorem latO_maps_at {S T : HSp D} {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) {P Q : GlobalTheory.FinPl.Pl D → Prop}
    {u : WO S T} (hu : u ∈ latO S T (LS : Set _) (LT : Set _) P) {y : Fin S.rank → AE D} (hy : y ∈ latV S LS Q) :
    u *ᵥ y ∈ latA T LT Q := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
      rw [Set.mem_singleton_iff] at hc
      subst hc
      rw [GlobalTheory.FinPl.LatMem.gen_mulVec]
      obtain ⟨b, hb⟩ := (hS.2 x).1 hx s hs
      refine AddSubgroup.subset_closure ⟨α * β, GlobalTheory.FinPl.LatMem.intAf_mul' hαi hβi,
        fun v hv => by rw [map_mul, hβ v hv, mul_zero], b • a, ?_, t, ht, ?_⟩
      · exact Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) b ha
      · funext i
        congr 1
        rw [Algebra.smul_def]
        show _ = (b : D.host.E) * a * t i
        rw [hb]
        ring
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
    | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
  | zero => rw [Matrix.zero_mulVec]; exact zero_mem _
  | add w w' _ _ hw hw' => rw [Matrix.add_mulVec]; exact add_mem hw hw'
  | neg w _ hw => rw [Matrix.neg_mulVec]; exact neg_mem hw

end GlobalTheory.CharXFB.OffPl

namespace GlobalTheory.CharXFB.OffPl
variable {D : D7}

theorem scaled_auxiliary_vector_mem_lattice_completion {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (q : Fin c)
    (v : GlobalTheory.FinPl.Pl D) {t : AE D} (ht : t ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v) :
    t • ratV (fun k => d.a k q) ∈ latV B (d.lat Λ 𝔟) (· = v) := by
  induction ht using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, hαi, fun w hw' => hα w hw', 1, rfl, fun k => a * d.a k q, ?_, ?_⟩
    · refine ⟨0, Λ.zero_mem, Pi.single q a, fun p => ?_, ?_⟩
      · by_cases hp : p = q
        · subst hp; simpa using ha
        · rw [Pi.single_eq_of_ne hp]; exact (𝔟 p).zero_mem
      · funext k
        simp [Matrix.mulVec_single, mul_comm]
    · funext k
      simp only [Pi.smul_apply, smul_eq_mul, ratV, one_mul]
      show _ * (1 ⊗ₜ[D.host.F] d.a k q) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

theorem hA_eq_pr (T : HSp D) (y w : Fin T.rank → AE D) : hA T y w = GlobalTheory.LineDual.pr T w y := by
  simp only [hA, GlobalTheory.LineDual.pr, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem hA_smul_left (T : HSp D) (r : AE D) (y w : Fin T.rank → AE D) : hA T (r • y) w = r * hA T y w := by
  simp only [hA, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hA_smul_right (T : HSp D) (r : AE D) (y w : Fin T.rank → AE D) : hA T y (r • w) = cA D r * hA T y w := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem hA_mem_intAt {T : HSp D} {M : Lat T} (hM : IsSelfDualC T M) {v : GlobalTheory.FinPl.Pl D} {y w : Fin T.rank → AE D}
    (hy : y ∈ latV T M (· = v)) (hw : w ∈ latV T M (· = v)) : hA T y w ∈ intAt D (· = v) := by
  rw [hA_eq_pr]
  exact GlobalTheory.LineDual.pr_mem_intAt hM hw hy

end GlobalTheory.CharXFB.OffPl

namespace GlobalTheory.CharXFB.OffPl
variable {D : D7}
open GlobalTheory.SeeSaw (idV FI conjFI)

theorem conjFI_AA_inv (D : D7) : conjFI D ((D.host.AA : FI D)⁻¹) = (D.host.AAbar : FI D)⁻¹ := by
  rw [map_inv₀, GlobalTheory.SeeSaw.conjFI_AA]

theorem pair_mem_idV (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ΛS : Lat S} {ΛT : Lat T}
    (sdS : IsSelfDualC S ΛS) (sdT : IsSelfDualC T ΛT) {u : WO S T}
    (hu : u ∈ latO S T (ΛS : Set _) (ΛT : Set _) fun _ => True) {v : GlobalTheory.FinPl.Pl D} {yS : Fin S.rank → AE D}
    {yT : Fin T.rank → AE D} {𝔟S 𝔟T : FI D} (h𝔟S : 𝔟S ≠ 0) (h𝔟T : 𝔟T ≠ 0)
    (hyS : ∀ t ∈ idV 𝔟S v, t • yS ∈ latV S ΛS (· = v)) (hyT : ∀ r ∈ idV 𝔟T v, r • yT ∈ latV T ΛT (· = v)) :
    GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈
      idV (1 * 𝔟T⁻¹ * ((D.host.AAbar : FI D)⁻¹)⁻¹ * (conjFI D 𝔟S)⁻¹) v := by
  obtain ⟨h1, h2, -, -, -, -, h7⟩ := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hAb : (D.host.AAbar : FI D) ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]
    exact (map_ne_zero (conjFI D)).2 (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.1
  have hX : GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have key : ∀ r ∈ idV 𝔟T v, ∀ s ∈ idV (D.host.AA : FI D)⁻¹ v, ∀ t ∈ idV 𝔟S v,
      r * (cA D s * (cA D t * hA T yT (u *ᵥ yS))) ∈ intAt D (· = v) := by
    intro r hr s hs t ht
    have e2 : u *ᵥ (t • yS) ∈ latA T ΛT (· = v) := latO_maps_at sdS hu (hyS t ht)
    have e3 : s • (u *ᵥ (t • yS)) ∈ latV T ΛT (· = v) := ((h7 T ΛT _).1 e2).2 s hs
    have e4 := hA_mem_intAt sdT (hyT r hr) e3
    rwa [hA_smul_left, hA_smul_right, Matrix.mulVec_smul, hA_smul_right] at e4
  have step1 : ∀ s ∈ idV (D.host.AA : FI D)⁻¹ v, ∀ t ∈ idV 𝔟S v,
      cA D s * (cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS))) ∈ idV (1 * 𝔟T⁻¹) v := by
    intro s hs t ht
    have hmem := Ideal.mul_mem_left _ (cA D s) (Ideal.mul_mem_left _ (cA D t) hX)
    refine (h2 𝔟T 1 h𝔟T one_ne_zero _ hmem).1 fun r hr => ?_
    have hr' := (GlobalTheory.FinPlLoc.mem_idAt_iff _ r).1 (GlobalTheory.LineDual.idV_mem_idAt hr)
    have e : cA D s * (cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS))) * r =
        r * (cA D s * (cA D t * hA T yT (u *ᵥ yS))) := by
      calc _ = cA D s * (cA D t * hA T yT (u *ᵥ yS)) * (GlobalTheory.FinPlLoc.idem D (· = v) * r) := by ring
        _ = _ := by rw [hr']; ring
    rw [e]
    exact (h1 _).2 (key r hr s hs t ht)
  have step2 : ∀ t ∈ idV 𝔟S v,
      cA D t * (GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS)) ∈ idV (1 * 𝔟T⁻¹ * ((D.host.AAbar : FI D)⁻¹)⁻¹) v := by
    intro t ht
    have hmem := Ideal.mul_mem_left _ (cA D t) hX
    refine (h2 _ _ (inv_ne_zero hAb) (mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)) _ hmem).1 fun a ha => ?_
    have hs : cA D a ∈ idV (D.host.AA : FI D)⁻¹ v := by
      rw [GlobalTheory.SeeSaw.idV_cA_iff D v, GlobalTheory.SeeSaw.cA_cA, conjFI_AA_inv]; exact ha
    have := step1 (cA D a) hs t ht
    rw [GlobalTheory.SeeSaw.cA_cA] at this
    rw [mul_comm _ a]; exact this
  have hcS : conjFI D 𝔟S ≠ 0 := (map_ne_zero (conjFI D)).2 h𝔟S
  refine (h2 _ _ hcS (mul_ne_zero (mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)) (inv_ne_zero (inv_ne_zero hAb))) _ hX).1
    fun a ha => ?_
  have ht : cA D a ∈ idV 𝔟S v := by
    rw [GlobalTheory.SeeSaw.idV_cA_iff D v, GlobalTheory.SeeSaw.cA_cA]; exact ha
  have := step2 (cA D a) ht
  rw [GlobalTheory.SeeSaw.cA_cA] at this
  rw [mul_comm _ a]; exact this

end GlobalTheory.CharXFB.OffPl

namespace GlobalTheory.CharXFB.OffPl
variable {D : D7}
open GlobalTheory.SeeSaw (idV FI conjFI)

theorem conjFI_conjFI (D : D7) (𝔞 : FI D) : conjFI D (conjFI D 𝔞) = 𝔞 := by
  ext x; rw [GlobalTheory.SeeSaw.mem_conjFI, GlobalTheory.SeeSaw.conj_mem_conjFI]

theorem conjFI_stA {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D (P.stA sc) = P.stAbar sc := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI, ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L P sc).2 x, bridge_star_holds D.R D.host]

theorem conjFI_stAbar {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D (P.stAbar sc) = P.stA sc := by
  rw [← conjFI_stA, conjFI_conjFI]

theorem conjFI_modulBar {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) = ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) := by
  ext x
  rw [GlobalTheory.SeeSaw.mem_conjFI]
  exact (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D (P.modul sc) x).symm

theorem idV_modulBar_eq_one {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ P.S0) (s : AE D) : s ∈ idV ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) v ↔ s ∈ idV 1 v := by
  rw [GlobalTheory.SeeSaw.idV_cA_iff D v _ s, conjFI_modulBar, GlobalTheory.ModulUnit.idV_modul_eq_one P sc v hv,
    GlobalTheory.SeeSaw.idV_cA_iff D v 1 s, map_one]

theorem stair_prod {A B : FI D} (hA : A ≠ 0) (hB : B ≠ 0) (hcA : conjFI D A = B) (hcB : conjFI D B = A)
    (σ : ℕ) (p : Fin (σ + 1)) (h1 : σ + 1 ≤ 2 * σ + 2 - 1) (h2 : σ + 1 ≤ 2 * (σ + 1) + 1 - 1) :
    1 * (GlobalTheory.ChiGrid.stairId A B (2 * σ + 2 - 1) (Fin.castLE h1 p))⁻¹ * ((D.host.AAbar : FI D)⁻¹)⁻¹ *
      (conjFI D (GlobalTheory.ChiGrid.stairId A B (2 * (σ + 1) + 1 - 1) (Fin.castLE h2 p).rev))⁻¹ = D.host.AAbar * A := by
  have hp := p.2
  unfold GlobalTheory.ChiGrid.stairId
  rw [map_mul, map_inv₀, map_pow, map_pow, hcA, hcB]
  simp only [Fin.val_rev, Fin.val_castLE]
  obtain ⟨n, hn⟩ : ∃ n, 2 * σ + 2 - 1 - p.1 = n := ⟨_, rfl⟩
  have e1 : 2 * (σ + 1) + 1 - 1 - (2 * (σ + 1) + 1 - 1 - (p.1 + 1)) = p.1 + 1 := by omega
  have e2 : 2 * (σ + 1) + 1 - 1 - (p.1 + 1) + 1 = n + 1 := by omega
  rw [hn, e1, e2]
  simp only [mul_inv, inv_inv, one_mul, pow_succ]
  field_simp

end GlobalTheory.CharXFB.OffPl

namespace GlobalTheory.CharXFB.OffPl
open GlobalTheory.SeeSaw (idV FI conjFI)

theorem psi_pair_trivial_off : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  intro D _ T L μ _ sc G W _ _ σ h h' u hu p v hv
  obtain ⟨h1, h2, h3, -, h5, -, -⟩ := GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v
  have hA0 : G.pl.stA sc ≠ 0 := ((GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc).1
  have hB0 : G.pl.stAbar sc ≠ 0 := by rw [← conjFI_stA]; exact (map_ne_zero _).2 hA0
  have hAA : (D.host.AA : FI D) ≠ 0 := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1.1
  have hAb : (D.host.AAbar : FI D) ≠ 0 := by
    rw [← GlobalTheory.SeeSaw.conjFI_AA]; exact (map_ne_zero (conjFI D)).2 hAA
  have hT1 : 1 ≤ 2 * σ + 2 := by omega
  have hS1 : 1 ≤ 2 * (σ + 1) + 1 := by omega
  have hS2 : 2 * (σ + 1) + 1 ≤ D.R.m := by omega
  have sdT : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.isV (X := .grid (2 * σ + 2) 0) ⟨h', Nat.zero_le _⟩ (fun j hj => by injection hj with e; omega)).sd
  have sdS : IsSelfDualC (negSp (G.V (.grid (2 * (σ + 1) + 1) 0))) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
    isSelfDualC_neg (G.isV (X := .grid (2 * (σ + 1) + 1) 0) ⟨hS2, Nat.zero_le _⟩
      (fun j hj => by injection hj with e; omega)).sd
  have hyS : ∀ t ∈ idV (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) v,
      t • ratV (fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev)
        ∈ latV (negSp (G.V (.grid (2 * (σ + 1) + 1) 0))) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (· = v) := by
    intro t ht
    have := scaled_auxiliary_vector_mem_lattice_completion (G.colDec _ hS1 hS2) (G.sp.P _).lat _ _ v ht
    rw [← G.sp.colLat _ hS1 hS2] at this
    exact this
  have hyT : ∀ r ∈ idV (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)
      (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1))) v,
      r • ratV (fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
        ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro r hr
    have := scaled_auxiliary_vector_mem_lattice_completion (G.colDec _ hT1 h') (G.sp.P _).lat _ _ v hr
    rw [← G.sp.colLat _ hT1 h'] at this
    exact this
  have hbS : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev ≠ 0 := by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA0) (inv_ne_zero (pow_ne_zero _ hB0))
  have hbT : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)) ≠ 0 := by
    unfold stairId; exact mul_ne_zero (pow_ne_zero _ hA0) (inv_ne_zero (pow_ne_zero _ hB0))
  have hX := pair_mem_idV W.ψ W.ψ_std sdS sdT hu.1 hbS hbT hyS hyT
  rw [stair_prod hA0 hB0 (conjFI_stA G.pl sc) (conjFI_stAbar G.pl sc)] at hX

  set X := GlobalTheory.FinPlLoc.idem D (· = v) * hA (G.V (.grid (2 * σ + 2) 0))
    (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
    (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) with hXdef
  have hXI : X ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
    intro h0
    have := conjFI_modulBar G.pl sc
    rw [h0, map_zero] at this
    exact (FractionalIdeal.coeIdeal_eq_zero.not.2 (G.pl.modul_ne_bot sc)) this.symm
  have hX2 : X ∈ idV ((D.host.AA : FI D) * D.host.AAbar) v := by
    have e : (D.host.AAbar : FI D) * G.pl.stA sc =
        (D.host.AA * D.host.AAbar) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹ := by
      rw [GlobalTheory.ChiGrid.Places.stA]; ring
    rw [e] at hX
    have hall := (h2 _ _ hmB (mul_ne_zero hAA hAb) X hXI).2 hX
    have := (h2 1 _ one_ne_zero (mul_ne_zero hAA hAb) X hXI).1 fun a ha =>
      hall a ((idV_modulBar_eq_one G.pl sc hv a).2 ha)
    rwa [inv_one, mul_one] at this

  have hξ : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hsI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0))
      (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
      (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev)) ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have hdI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0))
      (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
      (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev)) ∈ idV (GlobalTheory.SeeSaw.dI D) v := by
    rw [GlobalTheory.SeeSaw.dI, mul_assoc]
    refine (h3 _ _ hξ _).2 ⟨?_, hsI⟩
    have e : incA D D.host.xi0⁻¹ * (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA (G.V (.grid (2 * σ + 2) 0))
      (ratV fun k => (G.colDec (2 * σ + 2) hT1 h').a k (Fin.castLE (by omega) p : Fin (2 * σ + 2 - 1)))
      (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) hS1 hS2).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = X := by
      rw [hXdef]
      calc _ = incA D (D.host.xi0⁻¹ * D.host.xi0) * X := by rw [hXdef, map_mul]; ring
        _ = X := by rw [inv_mul_cancel₀ hξ, map_one, one_mul]
    rw [e]; exact hX2
  have := (h5 _ hsI).1 hdI _ (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  rwa [mul_comm, ← mul_assoc, GlobalTheory.FinPlLoc.idem_mul_self] at this

end GlobalTheory.CharXFB.OffPl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEOffS0ColumnPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiE_off_S0_column_pair : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∉ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  first | exact @GlobalTheory.CharXFB.OffPl.psi_pair_trivial_off | exact GlobalTheory.CharXFB.OffPl.psi_pair_trivial_off | (intros; apply GlobalTheory.CharXFB.OffPl.psi_pair_trivial_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEAtS0ColumnPair
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridPairingBoundMemCompletionOfMapBound
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridPairingBoundMemCompletionOfMapBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.PairAt

variable {D : D7}
open GlobalTheory.SeeSaw (idV FI conjFI)

theorem conjFI_modul {T : Type} {L : LevCh D T} (P : GlobalTheory.ChiGrid.Places L) (sc : Consts) :
    conjFI D ((P.modul sc : Ideal (𝓞 D.host.E)) : FI D) = ((P.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) := by
  have h := congrArg (conjFI D) (GlobalTheory.CharXFB.OffPl.conjFI_modulBar P sc)
  rw [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  exact h.symm

private theorem mul_mem_idAt' {D : D7} {v : GlobalTheory.FinPl.Pl D} {a : AE D} (b : AE D) (ha : a ∈ idAt D (· = v)) :
    a * b ∈ idAt D (· = v) := by
  rw [GlobalTheory.FinPlLoc.mem_idAt_iff] at ha ⊢
  rw [← mul_assoc, ha]

theorem pair_mem_idV_of_maps {S T : HSp D} {ΛS : Lat S} {ΛT : Lat T} (sdT : IsSelfDualC T ΛT) {u : WO S T}
    {v : GlobalTheory.FinPl.Pl D} {yS : Fin S.rank → AE D} {yT : Fin T.rank → AE D} {𝔟S 𝔟T 𝔐 : FI D} (h𝔟S : 𝔟S ≠ 0)
    (h𝔟T : 𝔟T ≠ 0) (h𝔐 : 𝔐 ≠ 0)
    (hu : ∀ y ∈ latV S ΛS (· = v), ∀ s ∈ idV 𝔐 v, s • (u *ᵥ y) ∈ latV T ΛT (· = v))
    (hyS : ∀ t ∈ idV 𝔟S v, t • yS ∈ latV S ΛS (· = v)) (hyT : ∀ r ∈ idV 𝔟T v, r • yT ∈ latV T ΛT (· = v)) :
    GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈
      idV (1 * 𝔟T⁻¹ * (conjFI D 𝔐)⁻¹ * (conjFI D 𝔟S)⁻¹) v := by
  have hx : GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) ∈ idAt D (· = v) :=
    mul_mem_idAt' _ (GlobalTheory.FinPlLoc.idem_mem_idAt _)
  have cS : conjFI D 𝔟S ≠ 0 := fun h => h𝔟S ((conjFI D).injective (by rw [h, map_zero]))
  have cM : conjFI D 𝔐 ≠ 0 := fun h => h𝔐 ((conjFI D).injective (by rw [h, map_zero]))
  have n1 : (1 : FI D) * 𝔟T⁻¹ ≠ 0 := mul_ne_zero one_ne_zero (inv_ne_zero h𝔟T)
  have n2 : (1 : FI D) * 𝔟T⁻¹ * (conjFI D 𝔐)⁻¹ ≠ 0 := mul_ne_zero n1 (inv_ne_zero cM)
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v (conjFI D 𝔟S) _ cS n2 _ hx).1 ?_
  intro t ht
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v (conjFI D 𝔐) _ cM n1 _ (mul_mem_idAt' t hx)).1 ?_
  intro m hm
  refine (GlobalTheory.IdealQuot.mul_subset_iff D v 𝔟T 1 h𝔟T one_ne_zero _
    (mul_mem_idAt' m (mul_mem_idAt' t hx))).1 ?_
  intro r hr
  rw [GlobalTheory.SeeSaw.idV_one_eq_intAt]
  have ht' : cA D t ∈ idV 𝔟S v := by
    have h := GlobalTheory.SeeSaw.cA_mem_idV ht
    rwa [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  have hm' : cA D m ∈ idV 𝔐 v := by
    have h := GlobalTheory.SeeSaw.cA_mem_idV hm
    rwa [GlobalTheory.CharXFB.OffPl.conjFI_conjFI] at h
  have hz := GlobalTheory.CharXFB.OffPl.hA_mem_intAt sdT (hyT r hr) (hu _ (hyS _ ht') _ hm')
  have hprod := GlobalTheory.IdealQuot.intAt_mul (GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)) hz
  have e : GlobalTheory.FinPlLoc.idem D (· = v) * hA T (r • yT) (cA D m • (u *ᵥ (cA D t • yS))) =
      GlobalTheory.FinPlLoc.idem D (· = v) * hA T yT (u *ᵥ yS) * t * m * r := by
    rw [GlobalTheory.CharXFB.OffPl.hA_smul_left, GlobalTheory.CharXFB.OffPl.hA_smul_right, Matrix.mulVec_smul,
      GlobalTheory.CharXFB.OffPl.hA_smul_right, GlobalTheory.SeeSaw.cA_cA, GlobalTheory.SeeSaw.cA_cA]
    ring
  rw [← e]
  exact hprod

private theorem stairId_ne_zero_twisted_operators {D : D7} {A B : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} (hA : A ≠ 0) (hB : B ≠ 0)
    (c : ℕ) (p : Fin c) : GlobalTheory.ChiGrid.stairId A B c p ≠ 0 := by
  rw [GlobalTheory.ChiGrid.stairId]
  exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))

theorem pair_mem_AA_AAbar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))) (v : GlobalTheory.FinPl.Pl D), (∀ y ∈ latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) → ∀ p : Fin (σ + 1), GlobalTheory.FinPlLoc.idem D (· = v) * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈ GlobalTheory.SeeSaw.idV (D.host.AA * D.host.AAbar) v := by
  intro D T L sc G σ h h' u v hu p
  have hAA : (D.host.AA : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    first
      | exact (GlobalTheory.SeeSaw.ChainIdeals.host_ne_zero D).2.1
      | exact Formalism.IndefR.Fin.PDA.AA_ne_zero (D := D)
      | exact GlobalTheory.IndefiniteRowSideFullHecke.TwistCoverDesign.AA_ne_zero D
      | exact GlobalTheory.SeeSaw.LatAt.AA_ne_zero (D := D)
  have hAbar : (D.host.AAbar : GlobalTheory.SeeSaw.FI D) ≠ 0 := fun e =>
    hAA ((conjFI D).injective (by rw [GlobalTheory.SeeSaw.conjFI_AA, e, map_zero]))
  have hm : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (G.pl.modul_ne_bot sc)
  have hmB : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 := fun e =>
    hm ((conjFI D).injective (by rw [conjFI_modul G.pl sc, e, map_zero]))
  have hstA : G.pl.stA sc ≠ 0 := by
    rw [GlobalTheory.ChiGrid.Places.stA]
    exact mul_ne_zero hAA (inv_ne_zero hmB)
  have hstAbar : G.pl.stAbar sc ≠ 0 := by
    rw [GlobalTheory.ChiGrid.Places.stAbar]
    exact mul_ne_zero hAbar (inv_ne_zero hm)
  have sdT : IsSelfDualC (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) :=
    (G.sp.V_is (2 * σ + 2) 0 (by omega) h' (Nat.zero_le _)).sd
  have hyT : ∀ r ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.ChiGrid.stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)
      (Fin.castLE (by omega) p)) v,
      r • ratV (fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) ∈
        latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v) := by
    intro r hr
    have hl := GlobalTheory.CharXFB.OffPl.scaled_auxiliary_vector_mem_lattice_completion (G.colDec (2 * σ + 2) (by omega) h') (G.sp.P (2 * σ + 2)).lat _ _ v hr
    rw [show G.Λ (.grid (2 * σ + 2) 0) = _ from G.sp.colLat (2 * σ + 2) (by omega) h']
    exact hl
  have hyS : ∀ t ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.ChiGrid.stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)
      (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) v,
      t • ratV (fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k
        (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈
        latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v) := by
    intro t ht
    have hl := GlobalTheory.CharXFB.OffPl.scaled_auxiliary_vector_mem_lattice_completion (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega))
      (G.sp.P (2 * (σ + 1) + 1)).lat _ _ v ht
    rw [show G.Λ (.grid (2 * σ + 2 + 1) 0) = _ from G.sp.colLat (2 * (σ + 1) + 1) (by omega) (by omega)]
    exact hl
  have key := pair_mem_idV_of_maps (ΛS := G.Λ (.grid (2 * σ + 2 + 1) 0)) sdT (u := u) (v := v)
    (stairId_ne_zero_twisted_operators hstA hstAbar _ _) (stairId_ne_zero_twisted_operators hstA hstAbar _ _)
    (mul_ne_zero (inv_ne_zero hAA) (inv_ne_zero hm)) hu hyS hyT
  have hcM : conjFI D (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) =
      D.host.AAbar⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    rw [map_mul, map_inv₀, map_inv₀, GlobalTheory.SeeSaw.conjFI_AA, conjFI_modul]
  have hst := GlobalTheory.CharXFB.OffPl.stair_prod hstA hstAbar (GlobalTheory.CharXFB.OffPl.conjFI_stA G.pl sc)
    (GlobalTheory.CharXFB.OffPl.conjFI_stAbar G.pl sc) σ p (by omega) (by omega)
  have hid : ∀ X Y : GlobalTheory.SeeSaw.FI D, 1 * X⁻¹ * (D.host.AAbar⁻¹)⁻¹ * Y⁻¹ = D.host.AAbar * G.pl.stA sc →
      1 * X⁻¹ * (D.host.AAbar⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹)⁻¹ * Y⁻¹ =
        D.host.AA * D.host.AAbar := by
    intro X Y hXY
    rw [mul_inv, inv_inv (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D))]
    calc 1 * X⁻¹ * ((D.host.AAbar⁻¹)⁻¹ * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) * Y⁻¹
        = (1 * X⁻¹ * (D.host.AAbar⁻¹)⁻¹ * Y⁻¹) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
          ring
      _ = D.host.AAbar * (D.host.AA * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) *
          ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) := by
          rw [hXY, GlobalTheory.ChiGrid.Places.stA]
      _ = D.host.AA * D.host.AAbar * (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ *
          ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)) := by ring
      _ = D.host.AA * D.host.AAbar := by rw [inv_mul_cancel₀ hmB, mul_one]
  rw [hcM] at key
  rw [← hid _ _ hst]
  exact key

end GlobalTheory.CharXFB.PairAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridPairingBoundMemCompletionOfMapBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGrid_pairingBound_mem_completion_of_mapBound : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (σ : ℕ) (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))) (v : GlobalTheory.FinPl.Pl D), (∀ y ∈ latV (G.V (.grid (2 * σ + 2 + 1) 0)) (G.Λ (.grid (2 * σ + 2 + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid (2 * σ + 2) 0)) (G.Λ (.grid (2 * σ + 2) 0)) (· = v)) → ∀ p : Fin (σ + 1), GlobalTheory.FinPlLoc.idem D (· = v) * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev) ∈ GlobalTheory.SeeSaw.idV (D.host.AA * D.host.AAbar) v := by
  first | exact @GlobalTheory.CharXFB.PairAt.pair_mem_AA_AAbar | exact GlobalTheory.CharXFB.PairAt.pair_mem_AA_AAbar | (intros; apply GlobalTheory.CharXFB.PairAt.pair_mem_AA_AAbar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeScalingAtS0
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeScalingAtS0
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section

namespace GlobalTheory.DepthMap

variable {D : D7}

theorem intAf_mul' {α β : Af D.host.F} (hα : α ∈ intAf D.host.F) (hβ : β ∈ intAf D.host.F) :
    α * β ∈ intAf D.host.F := fun v => by rw [map_mul]; exact mul_mem (hα v) (hβ v)

theorem pairA_mul' (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) := Prod.ext (zero_mul _) rfl

theorem mul_ePl {v : GlobalTheory.FinPl.Pl D} {α : Af D.host.F} (h : ∀ w, w ≠ v → evalV D.host.F w α = 0) :
    α * GlobalTheory.FinPlLoc.ePl D (· = v) = α := by
  classical
  refine RestrictedProduct.ext _ _ fun w => ?_
  show evalV D.host.F w (α * _) = evalV D.host.F w α
  rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl]
  by_cases hw : w = v
  · rw [if_pos hw, mul_one]
  · rw [if_neg hw, mul_zero, h w hw]

theorem smul_mem_homLat {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    {c : D.host.E} (hc : c ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹)
    {X : Matrix (Fin m) (Fin n) D.host.E} (hX : X ∈ 𝔪 • homLat Λ Λ') : c • X ∈ homLat Λ Λ' := by
  have hne : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  refine Submodule.smul_induction_on hX (fun r hr Y hY => ?_) (fun x y hx hy => ?_)
  · have h1 : c * algebraMap (𝓞 D.host.E) D.host.E r ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [← inv_mul_cancel₀ hne]
      exact FractionalIdeal.mul_mem_mul hc (FractionalIdeal.mem_coeIdeal_of_mem _ hr)
    obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have e : c • (r • Y) = o • Y := by
      rw [← algebraMap_smul D.host.E r Y, smul_smul, ← ho, algebraMap_smul]
    rw [e]
    exact Submodule.smul_mem _ o hY
  · rw [smul_add]; exact add_mem hx hy

theorem smul_mem_hatMx {m n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {v : GlobalTheory.FinPl.Pl D}
    {z : AE D} (hz : z ∈ GlobalTheory.SeeSaw.idV ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ v) {x : Mx D m n}
    (hx : x ∈ hatMx (𝔪 • homLat Λ Λ')) : z • x ∈ hatMx (homLat Λ Λ') := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, -, c, hc, rfl⟩ := hz
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨β, hβ, X, hX, rfl⟩ := hx
      refine AddSubgroup.subset_closure ⟨α * β, intAf_mul' hα hβ, c • X, smul_mem_homLat h𝔪 hc hX, ?_⟩
      ext i j
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul']
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_smul]; exact neg_mem ha

theorem val_le_one_of_mem_inv {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : ¬ 𝔪 ≤ Q.asIdeal) {a : D.host.E} (ha : a ∈ ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹) :
    Valued.v (algebraMap D.host.E (Kw Q) a) ≤ 1 := by
  obtain ⟨m, hm, hmQ⟩ := Set.not_subset.1 hQ
  have hne : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h𝔪
  have h1 : a * algebraMap (𝓞 D.host.E) D.host.E m ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [← inv_mul_cancel₀ hne]
    exact FractionalIdeal.mul_mem_mul ha (FractionalIdeal.mem_coeIdeal_of_mem _ hm)
  obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1 h1
  rw [show Valued.v (algebraMap D.host.E (Kw Q) a) = Q.valuation D.host.E a from
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q a]
  have hm1 : Q.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E m) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (Q.intValuation_le_one m)
      (not_lt.1 fun h => hmQ ((Q.intValuation_lt_one_iff_mem m).1 h))
  have ho1 : Q.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E o) ≤ 1 := Q.valuation_le_one o
  rw [ho, map_mul, hm1, mul_one] at ho1
  exact ho1

end GlobalTheory.DepthMap

namespace GlobalTheory.DepthMap

variable {D : D7}

theorem val_cpt_le_one {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : ¬ 𝔪 ≤ Q.asIdeal) {v : GlobalTheory.FinPl.Pl D} {z : AE D}
    (hz : z ∈ GlobalTheory.SeeSaw.idV ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ v) :
    Valued.v (GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D z)) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, -, c, hc, rfl⟩ := hz
    have e : pairA D.host.F 0 α ⊗ₜ[D.host.F] c =
        (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * incA D c := by
      change _ = _ * ((1 : AF D.host.F) ⊗ₜ[D.host.F] c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, RingHom.map_mul, RingHom.map_mul, Valuation.map_mul,
      show GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (incA D c)) = algebraMap D.host.E (Kw Q) c from Comparison₂.cpt_tmul Q c]
    have hi : finPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) ∈ intAE D :=
      AddSubgroup.subset_closure ⟨α, hα, 1, rfl⟩
    exact mul_le_one' (((GlobalTheory.StdFrames.comp_toAd D).int _).1 hi Q) (val_le_one_of_mem_inv h𝔪 hQ hc)
  | zero => simp
  | add x y _ _ hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]; exact Valuation.map_add_le _ hx hy
  | neg x _ hx => rw [RingHom.map_neg, RingHom.map_neg, Valuation.map_neg]; exact hx

theorem cpt_idemSum_of_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) : GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = 1 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show toEAf D (∑ PP ∈ P, es PP) = ∑ PP ∈ P, toEAf D (es PP) from
      map_sum (toEAf D).toAddMonoidHom (fun PP => es PP) P,
    show GlobalTheory.StdFrames.cpt (D := D) Q (∑ PP ∈ P, toEAf D (es PP)) = ∑ PP ∈ P, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (es PP)) from
      map_sum (GlobalTheory.StdFrames.cpt (D := D) Q).toAddMonoidHom (fun PP => toEAf D (es PP)) P, Finset.sum_eq_single Q]
  · exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes Q hQ)).1
  · intro b hb hbQ; exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes b hb)).2 Q (Ne.symm hbQ)
  · intro h; exact absurd hQ h

theorem cpt_idemSum_of_not_mem {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P)
    {Q : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∉ P) : GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D e) = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show toEAf D (∑ PP ∈ P, es PP) = ∑ PP ∈ P, toEAf D (es PP) from
      map_sum (toEAf D).toAddMonoidHom (fun PP => es PP) P,
    show GlobalTheory.StdFrames.cpt (D := D) Q (∑ PP ∈ P, toEAf D (es PP)) = ∑ PP ∈ P, GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D (es PP)) from
      map_sum (GlobalTheory.StdFrames.cpt (D := D) Q).toAddMonoidHom (fun PP => toEAf D (es PP)) P]
  exact Finset.sum_eq_zero fun b hb => (GlobalTheory.StdFrames.cpt_of_isIdemAt (hes b hb)).2 Q fun h => hQ (h ▸ hb)

theorem modul_not_le {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {Q : Formalism.L2.DIV.Pl D.host.E}
    (hQ : Q ∉ P.W0) : ¬ P.modul sc ≤ Q.asIdeal := by
  classical
  intro h
  unfold Places.modul at h
  obtain ⟨v, hv, hle⟩ := (Ideal.IsPrime.prod_le Q.isPrime).1 h
  have h1 : (P.w v).asIdeal ≤ Q.asIdeal := Ideal.IsPrime.le_of_pow_le hle
  have h2 : P.w v = Q := HeightOneSpectrum.ext ((P.w v).isMaximal.eq_of_le Q.isPrime.ne_top h1)
  exact hQ (h2 ▸ Finset.mem_image_of_mem P.w hv)

end GlobalTheory.DepthMap


open GlobalTheory.DepthMap in
theorem GlobalTheory.DepthMap.smul_mulVec_mem_latV : All fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∀ u ∈ latRow G i, ∀ v ∈ G.pl.S0, ∀ y ∈ latV (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
  intro D hD T L μ0 hL sc G W M hM i hi u hu v hv y hy s hs
  classical
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  have P7 := GlobalTheory.SeeSaw.idV_props D ψ hψ v
  have hm0 : G.pl.modul sc ≠ ⊥ := G.pl.modul_ne_bot sc
  have hmF : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hm0
  obtain ⟨e, he⟩ := GlobalTheory.GridIdem.exists_idempotentSum_auxiliaryPlaces D T L G.pl
  have h0 : ∀ j, (Node.grid (i + 1) 0 : Node) ≠ .grid 0 j := fun j h => by
    injection h with h'
    omega
  have hsd : IsSelfDualC (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) :=
    (G.isV (show (Node.grid (i + 1) 0 : Node).InRange D.R.m from ⟨hi, Nat.zero_le _⟩) h0).sd
  obtain ⟨-, -, -, -, -, P6, P7'⟩ := P7
  have key : ∀ z ∈ GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v,
      z • u ∈ latO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) (G.Λ (.grid (i + 1) 0) : Set _)
        (G.Λ (.grid i 0) : Set _) (· = v) := by
    intro z hz
    obtain ⟨g, hg, g', hg', hid, hiff⟩ := P6 _ (inv_ne_zero hmF)
    have hzA : z ∈ idAt D (· = v) := ((hiff z).1 hz).1
    have hsplit : z • u = (e * z) • u + ((1 - e) * z) • u := by
      rw [← add_smul]; congr 1; ring
    rw [hsplit]
    refine add_mem ?_ ?_
    · have h1 : e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0))) := hu.2 e he
      have h2 := smul_mem_hatMx hm0 hz h1
      have h3 : (e * z) • u = z • (e • u) := by rw [mul_comm, mul_smul]
      rw [h3]
      have hhalf : IsHalf e (z • (e • u)) := fun a b => by
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_comm e z, mul_assoc, ← mul_assoc e e, GlobalTheory.PlaceDatum.idemSum_mul_self he]
      have h4 := GlobalTheory.RowLatChi.mem_latO_of_mem_hatMx hsd he (GlobalTheory.AAUnit.exists_valuation_one_element_at_grid_places hD hL G) hhalf h2
      refine (GlobalTheory.AscFinWit.mem_latO_at (fun a b => ?_)).1 h4
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hzA
    · have hint : finPart D ((1 - e) * z) ∈ intAE D := by
        refine ((GlobalTheory.StdFrames.comp_toAd D).int _).2 fun Q => ?_
        show Valued.v (GlobalTheory.StdFrames.cpt (D := D) Q (toEAf D ((1 - e) * z))) ≤ 1
        rw [RingHom.map_mul, RingHom.map_mul, RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one]
        by_cases hQ : Q ∈ G.pl.W0
        · rw [cpt_idemSum_of_mem he hQ, sub_self, zero_mul, Valuation.map_zero]; exact zero_le'
        · have hc := cpt_idemSum_of_not_mem he hQ
          have hb := val_cpt_le_one hm0 (modul_not_le G.pl sc hQ) hz
          simp only [hc, sub_zero, one_mul]
          exact hb
      have hI : (1 - e) * z ∈ intAt D (· = v) := by
        refine ⟨?_, hint⟩
        exact Ideal.mul_mem_left _ _ hzA
      have hS := GlobalTheory.RowInt.smul_mem_latO_at D hD T L μ0 hL sc G W M hM
      exact hS i hi v _ hI u hu
  have hlatA : ∀ z ∈ GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v,
      z • (u *ᵥ y) ∈ latA (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
    intro z hz
    rw [← Matrix.smul_mulVec]
    exact GlobalTheory.FinPl.LatMem.latO_maps hsd (key z hz) hy
  induction hs using AddSubgroup.closure_induction with
  | mem s hs =>
    obtain ⟨α, hα, hsupp, a, ha, rfl⟩ := hs
    refine FractionalIdeal.mul_induction_on
      (C := fun a => (pairA D.host.F 0 α ⊗ₜ[D.host.F] a) • (u *ᵥ y) ∈
        GlobalTheory.FinPl.latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v)) ha (fun b hb c hc => ?_)
      (fun x x' hx hx' => ?_)
    · have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * c) = (pairA D.host.F 0 α ⊗ₜ[D.host.F] b) *
          (pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] c) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, pairA_mul', mul_ePl hsupp]
      have hz : pairA D.host.F 0 (GlobalTheory.FinPlLoc.ePl D (· = v)) ⊗ₜ[D.host.F] c ∈
          GlobalTheory.SeeSaw.idV ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ v :=
        AddSubgroup.subset_closure ⟨_, GlobalTheory.FinPlLoc.ePl_int _, fun w hw => by
          rw [GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw], c, hc, rfl⟩
      have hs' : pairA D.host.F 0 α ⊗ₜ[D.host.F] b ∈ GlobalTheory.SeeSaw.idV D.host.AA⁻¹ v :=
        AddSubgroup.subset_closure ⟨α, hα, hsupp, b, hb, rfl⟩
      show (pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * c)) • (u *ᵥ y) ∈ _
      rw [e1, mul_smul]
      exact ((P7' _ _ _).1 (hlatA _ hz)).2 _ hs'
    · show (pairA D.host.F 0 α ⊗ₜ[D.host.F] (x + x')) • (u *ᵥ y) ∈ _
      rw [TensorProduct.tmul_add, add_smul]; exact add_mem hx hx'
  | zero => rw [zero_smul]; exact zero_mem _
  | add a b _ _ ha hb => rw [add_smul]; exact add_mem ha hb
  | neg a _ ha => rw [neg_smul]; exact neg_mem ha
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeScalingAtS0Statement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_scaling_at_S0 : All fun {D} _ _ {sc} {G} _ _ => ∀ i, i < D.R.m → ∀ u ∈ latRow G i, ∀ v ∈ G.pl.S0, ∀ y ∈ latV (G.V (.grid (i + 1) 0)) (G.Λ (.grid (i + 1) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹ * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v, s • (u *ᵥ y) ∈ latV (G.V (.grid i 0)) (G.Λ (.grid i 0)) (· = v) := by
  first | exact @GlobalTheory.DepthMap.smul_mulVec_mem_latV | exact GlobalTheory.DepthMap.smul_mulVec_mem_latV | (intros; apply GlobalTheory.DepthMap.smul_mulVec_mem_latV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEAtS0ColumnPair
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.HeisenbergPairBadPlaces

theorem traceCharacter_trivial_heisenbergPair_at_badPlaces : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∈ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  intro D hQ T L μ0 hL sc G W M hM σ h h' u hu p v hv
  have hb := GlobalTheory.T.lattice_scaling_at_S0 D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) u hu v hv
  have hC := GlobalTheory.T.thetaGrid_pairingBound_mem_completion_of_mapBound G σ h h' u v hb p
  generalize hA _ _ _ = x at hC ⊢
  obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v
  have hε : GlobalTheory.FinPlLoc.idem D (· = v) ∈ idAt D (· = v) := GlobalTheory.FinPlLoc.idem_mem_idAt _
  have hs : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hε
  have hx0 : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  have hdI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
    have e : GlobalTheory.SeeSaw.dI D = FractionalIdeal.spanSingleton _ D.host.xi0 * (D.host.AA * D.host.AAbar) := by
      unfold GlobalTheory.SeeSaw.dI; rw [mul_assoc]
    rw [e, h3 _ _ hx0]
    refine ⟨?_, hs⟩
    have e1 : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    convert hC using 1
    linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * x) * e1
  have h6 := (h5 _ hs).1 hdI _ (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have e2 : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) * GlobalTheory.FinPlLoc.idem D (· = v) =
      GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) := by
    rw [mul_comm, ← mul_assoc, GlobalTheory.FinPlLoc.idem_mul_self]
  rwa [e2] at h6

end GlobalTheory.CharXFB.HeisenbergPairBadPlaces
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEAtS0ColumnPairStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiE_at_S0_column_pair : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∈ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  first | exact @GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces | exact GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces | (intros; apply GlobalTheory.CharXFB.HeisenbergPairBadPlaces.traceCharacter_trivial_heisenbergPair_at_badPlaces <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBasePointCharacterTrivialDepthLatti
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB
variable {D : D7}

theorem charx_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m)
    (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)),
    (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' ∈ latRow G (2 * σ + 2) →
      W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h'))
        ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a')) = 1 := by
  intro D hD T L μ0 hL sc G W M hM F hF σ h h' a' ha'
  have hh := (F.dJ (σ + 1) h).hO_ext (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h') 0 0 a' 0 0
  simp only [map_zero, zero_add, add_zero] at hh
  rw [symplO, hh, show hO (G.V (.core (2 * (σ + 1) + 1))) (G.V (.grid (2 * σ + 2) 0)) 0 0 = 0 by simp [hO],
    show pairS (G.V (.grid (2 * σ + 2) 0)) (0 : Mx D _ (σ + 1)) 0 = 0 by simp [pairS], add_zero, add_zero,
    pairS_eq_sum, Finset.mul_sum]
  change psiE W.ψ _ = 1
  refine Finset.sum_induction _ (fun z => psiE W.ψ z = 1) (fun a b ha hb => by rw [psiE_add, ha, hb, one_mul])
    (psiE_zero W.ψ) fun p _ => ?_
  rw [GlobalTheory.T.hermitianPairing_fourierJacobi_step_basePoint_columns D hD T L μ0 hL sc G W M hM F hF σ h h' a' p]
  refine GlobalTheory.FinPl.PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 (P := fun _ => True) ?_ fun v _ => ?_
  · have hu : MxAt (fun _ => True) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a') :=
      mxAt_of_mem_depLat (p := .chi (2 * σ + 2) 0) ha'
    refine Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (GlobalTheory.LastOpPf.cA_mem_idAt ?_))
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hu k l)
  · by_cases hv : v ∈ G.pl.S0
    · exact GlobalTheory.T.psiE_at_S0_column_pair D hD T L μ0 hL sc G W M hM σ h h' _ ha' p v hv
    · exact GlobalTheory.T.psiE_off_S0_column_pair D hD T L μ0 hL sc G W M hM σ h h' _ ha' p v hv

end GlobalTheory.CharXFB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBasePointCharacterTrivialDepthLattiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_basePoint_character_trivial_depthLattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)), (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' ∈ latRow G (2 * σ + 2) → W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h')) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a')) = 1 := by
  first | exact @GlobalTheory.CharXFB.charx_fb | exact GlobalTheory.CharXFB.charx_fb | (intros; apply GlobalTheory.CharXFB.charx_fb <;> assumption)
end
