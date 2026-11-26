module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagGenDiag
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

variable {D : D7}

section Rescale

variable {S S₀ : HSp D} {ρ : ℕ}

theorem sandwich {m n : ℕ} (A : Matrix (Fin S.rank) (Fin m) D.host.E) (B : Matrix (Fin S.rank) (Fin n) D.host.E)
    (P : Matrix (Fin m) (Fin m) D.host.E) (Q : Matrix (Fin n) (Fin n) D.host.E) :
    (A * P)ᴴ * S.gram * (B * Q) = Pᴴ * (Aᴴ * S.gram * B) * Q := by
  simp only [conjTranspose_mul, Matrix.mul_assoc]

def diagDec (d : HypDec S S₀ ρ) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) : HypDec S S₀ ρ where
  e := d.e * diagonal l
  e' := d.e' * diagonal fun a => (star (l a))⁻¹
  i₀ := d.i₀
  ee := by rw [sandwich, d.ee, Matrix.mul_zero, Matrix.zero_mul]
  e'e' := by rw [sandwich, d.e'e', Matrix.mul_zero, Matrix.zero_mul]
  e'e := by
    rw [sandwich, d.e'e, Matrix.mul_one, diagonal_conjTranspose, diagonal_mul_diagonal,
      ← diagonal_one, Matrix.diagonal_eq_diagonal_iff]
    intro a
    simpa only [Pi.star_apply, star_inv₀, star_star] using inv_mul_cancel₀ (hl a)
  iso := d.iso
  i₀e := by rw [← Matrix.mul_assoc, d.i₀e, Matrix.zero_mul]
  i₀e' := by rw [← Matrix.mul_assoc, d.i₀e', Matrix.zero_mul]
  rank_add := d.rank_add

theorem perp_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0)
    (x : Fin S.rank → D.host.E) (hx : ((e * diagonal l)ᴴ * S.gram).mulVec x = 0) : (eᴴ * S.gram).mulVec x = 0 := by
  rw [conjTranspose_mul, diagonal_conjTranspose, Matrix.mul_assoc, ← mulVec_mulVec] at hx
  funext j
  have := congrFun hx j
  rw [mulVec_diagonal] at this
  simp only [Pi.zero_apply, Pi.star_apply, mul_eq_zero, star_eq_zero] at this
  rcases this with h | h
  · exact absurd h (hl j)
  · exact h

theorem flagGen_diag {e : Matrix (Fin S.rank) (Fin ρ) D.host.E} (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) (g : GA D S)
    (hg : (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => e k i) = (e.map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E, (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = (e.map (incA D)).mulVec a) :
    (∀ i : Fin ρ, ∃ a : Fin ρ → AE D, (∀ j, i ≤ j → a j = 0) ∧
      (subOne S g).mulVec (ratV fun k => (e * diagonal l) k i) = ((e * diagonal l).map (incA D)).mulVec a) ∧
      ∀ x : Fin S.rank → D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) * S.gram).mulVec x = 0 →
        ∃ a : Fin ρ → AE D, (subOne S g).mulVec (ratV x) = ((e * diagonal l).map (incA D)).mulVec a := by
  have hmv : ∀ a : Fin ρ → AE D, ((e * diagonal l).map (incA D)).mulVec (fun j => incA D (l j)⁻¹ * a j) =
      (e.map (incA D)).mulVec a := fun a => by
    funext k
    simp only [mulVec, dotProduct, Matrix.map_apply, mul_diagonal]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, mul_assoc, ← mul_assoc (incA D (l j)), ← map_mul, mul_inv_cancel₀ (hl j), map_one, one_mul]
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha0, ha⟩ := hg.1 i
    refine ⟨fun j => incA D (l j)⁻¹ * (incA D (l i) * a j), fun j hj => ?_, ?_⟩
    · show incA D (l j)⁻¹ * (incA D (l i) * a j) = 0
      rw [ha0 j hj, mul_zero, mul_zero]
    have hcol : (ratV fun k => (e * diagonal l) k i) = incA D (l i) • ratV fun k => e k i := by
      funext k
      show incA D ((e * diagonal l) k i) = incA D (l i) * incA D (e k i)
      rw [mul_diagonal, map_mul, mul_comm]
    rw [hcol, mulVec_smul, ha, ← mulVec_smul, ← hmv]
    rfl
  · have h1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (e * diagonal l) = (e * diagonal l)ᴴ := rfl
    have h2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) e = eᴴ := rfl
    rw [h1] at hx
    obtain ⟨a, ha⟩ := hg.2 x (by rw [h2]; exact perp_diag l hl x hx)
    exact ⟨_, ha.trans (hmv a).symm⟩

theorem nFlag_diag (e : Matrix (Fin S.rank) (Fin ρ) D.host.E) (l : Fin ρ → D.host.E) (hl : ∀ a, l a ≠ 0) :
    NFlag S (e * diagonal l) = NFlag S e := by
  have hl' : ∀ a, (l a)⁻¹ ≠ 0 := fun a => inv_ne_zero (hl a)
  have e0 : diagonal l * diagonal (fun a => (l a)⁻¹) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact mul_inv_cancel₀ (hl a)
  have e1 : e * diagonal l * diagonal (fun a => (l a)⁻¹) = e := by
    rw [Matrix.mul_assoc, e0, Matrix.mul_one]
  unfold NFlag
  congr 1
  ext g
  refine ⟨fun h => ?_, fun h => flagGen_diag l hl g h⟩
  have := flagGen_diag (e := e * diagonal l) (fun a => (l a)⁻¹) hl' g h
  rwa [e1] at this

def trMeas {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) : Measure N' := h ▸ ν

def trSet {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (𝓝 : Set N) : Set N' := h ▸ 𝓝

theorem isUnit_trans {S : HSp D} {N N' : Subgroup (GA D S)} (h : N = N') (ν : Measure N) (𝓝 : Set N)
    (hu : ν.IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N) 𝓝 ν ∧ ν 𝓝 = 1) :
    (trMeas h ν).IsHaarMeasure ∧ IsFundamentalDomain ((GQ S).subgroupOf N') (trSet h 𝓝) (trMeas h ν) ∧
      trMeas h ν (trSet h 𝓝) = 1 := by
  subst h
  exact hu

def volNOf {S₀' : HSp D} {ρ' : ℕ} {d : HypDec S S₀ ρ} {d' : HypDec S S₀' ρ'} (h : NFlag S d.e = NFlag S d'.e)
    (v : VolN d) : VolN d' :=
  ⟨trMeas h v.ν, trSet h v.𝓝, isUnit_trans h v.ν v.𝓝 v.unit⟩

end Rescale

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj

variable {T : Type}

noncomputable def splitFam {S : Arrow T → Type} {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z), (p.comp q).Fam S → p.Fam S × q.Fam S
  | _, .nil, d => (d, ())
  | _, .snoc _ q, d => ((splitFam q d.1).1, ((splitFam q d.1).2, d.2))

theorem all_splitFam {S : Arrow T → Type} (P : ∀ a, S a → Prop) {X Y : Node} {p : Path T X Y} :
    ∀ {Z : Node} (q : Path T Y Z) (d : (p.comp q).Fam S), Path.Fam.All P d →
      Path.Fam.All P (splitFam q d).1 ∧ Path.Fam.All P (splitFam q d).2
  | _, .nil, _, h => ⟨h, trivial⟩
  | _, .snoc _ q, d, h => ⟨(all_splitFam P q d.1 h.1).1, (all_splitFam P q d.1 h.1).2, h.2⟩

noncomputable def getD {S : Arrow T → Type} (t : T) (i : ℕ) : ∀ (n : ℕ), (downPath t i n).Fam S → ∀ j, j < n → S (.down t i j)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, j, h =>
    if hj : j < n then getD t i n (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).2 j hj
    else (show n = j by omega) ▸ (splitFam (p := Path.one (.down t i n)) (downPath t i n) d).1.2

theorem getD_all {S : Arrow T → Type} (P : ∀ a, S a → Prop) (t : T) (i : ℕ) :
    ∀ (n : ℕ) (d : (downPath t i n).Fam S), Path.Fam.All P d → ∀ j (h : j < n), P (.down t i j) (getD t i n d j h)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, d, hd, j, h => by
    have hs := all_splitFam P (p := Path.one (.down t i n)) (downPath t i n) d hd
    unfold getD
    split_ifs with hj
    · exact getD_all P t i n _ hs.2 j hj
    · have hnj : n = j := by omega
      subst j
      change P (.down t i n) (splitFam (downPath t i n) d).1.2
      exact hs.1.2

end GlobalTheory.RowChain
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

def lam (σ : ℕ) : Fin σ → D.host.E := fun a => D.host.xi0 ^ (a : ℕ)

theorem lam_ne (σ : ℕ) (a : Fin σ) : lam (D := D) σ a ≠ 0 := pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D)

def besDecAt (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) :
    HypDec (G.V (.grid D.R.m j)) (GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)) σ :=
  diagDec (rowBes G j (by omega) σ (by omega)) (lam σ) (lam_ne σ)


variable {G t M} in
def volAt (hM : M.Is t) (X : Node) (hX : X.InRange D.R.m) : GlobalTheory.Unf.Vol (G.V X) :=
  ⟨M.ν X, M.fd X, (hM.vtx X hX).haar_fund.1, (hM.vtx X hX).haar_fund.2⟩


variable {t M} in
def besAt (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)) : BesLev D σ where
  V := G.V (.grid D.R.m j)
  V₀ := GlobalTheory.Doubling.hsum (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
  A := G.V (.top j)
  L := GlobalTheory.SeeSaw.Model.nLine D
  d := besDecAt G j σ hj
  o := GlobalTheory.OrthSumExists.orthDecHsum D _ _
  ζ := fun _ => D.host.xi0 ^ σ
  line := GlobalTheory.SeeSaw.Model.isLineVec_nLine (pow_ne_zero _ (GlobalTheory.Unf.Inhab.cmHost_imaginaryGenerator_ne_zero D))
  cpt := cocpt_top G (by omega)
  vA := volAt hM (.top j) (by show j ≤ D.R.m; omega)
  vN := vN


variable {t M} in
def jacAt (hM : M.Is t) (n σ : ℕ) (hn : n + 2 * σ + 1 = D.R.m) : JacLev D σ where
  W := G.V (.grid D.R.m n)
  W₀ := G.V (.top n)
  d := rowJac G n (by omega) σ (by omega)
  cpt := cocpt_top G (by omega)
  v0 := volAt hM (.top n) (by show n ≤ D.R.m; omega)
  vN := (GlobalTheory.Unf.Inhab.nonempty_volN _).some

theorem exists_weilDatum_anisotropicKernelPair {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) :
    ∃ om₀ : Om V₀ W₀, IsWeilDatumO ψ V₀ W₀ χV χW om₀ := by
  obtain ⟨om₁, h₁⟩ := (GlobalTheory.Desc.weil_data_descend D ψ V W χV χW om h).1 V₀ ρ dV
  exact (GlobalTheory.Desc.weil_data_descend D ψ V₀ W χV χW om₁ h₁).2 W₀ σ dW


variable {M} in
def stepAt (hM : M.Is t) (j : ℕ) (hj : j + 1 ≤ D.R.m) {V₀ W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec (G.V (.grid D.R.m j)) V₀ ρ)
    (dW : HypDec (G.V (.grid D.R.m (j + 1))) W₀ σ) :
    Step Wl.ψ (G.V (.grid D.R.m j)) V₀ (G.V (.grid D.R.m (j + 1))) W₀ ρ σ where
  χV := G.chrS (.mu t D.R.m j)
  χW := G.chrT (.mu t D.R.m j)
  om := Wl.om (.mu t D.R.m j)
  om₀ := (exists_weilDatum_anisotropicKernelPair dV dW (Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩)).choose
  weil := Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩
  weil₀ := (exists_weilDatum_anisotropicKernelPair dV dW (Wl.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩)).choose_spec
  vW := volAt hM (.grid D.R.m (j + 1)) ⟨le_rfl, hj⟩
  vS := (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some
  vT := (GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some
  vU := (GlobalTheory.Unf.Inhab.nonempty_volU D _).some

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

theorem link_map {n : ℕ} (σ : ℕ) :
    (-(D.host.xi0 • (1 : Matrix (Fin n) (Fin n) D.host.E))) *ᵥ (fun _ => D.host.xi0 ^ σ) = -fun _ => D.host.xi0 ^ (σ + 1) := by
  rw [neg_mulVec, smul_mulVec, one_mulVec]
  funext i
  simp [pow_succ, mul_comm]

theorem link_norm (L : HSp D) (σ : ℕ) :
    star (fun _ : Fin L.rank => D.host.xi0 ^ (σ + 1)) ⬝ᵥ L.gram *ᵥ (fun _ => D.host.xi0 ^ (σ + 1)) =
      D.host.xi0 * star D.host.xi0 * (star (fun _ : Fin L.rank => D.host.xi0 ^ σ) ⬝ᵥ L.gram *ᵥ (fun _ => D.host.xi0 ^ σ)) := by
  have e : (fun _ : Fin L.rank => D.host.xi0 ^ (σ + 1)) = D.host.xi0 • fun _ => D.host.xi0 ^ σ := by
    funext i
    simp [pow_succ, mul_comm]
  rw [e, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring


variable {G t M} in
def linkAt (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : VolN (besDecAt G j (σ + 1) hj))
    (hj' : j + 1 + 1 + 2 * σ + 2 = D.R.m) (vN' : VolN (besDecAt G (j + 1 + 1) σ hj')) :
    Link (besAt G hM j (σ + 1) hj vN) (besAt G hM (j + 1 + 1) σ hj' vN').L (besAt G hM (j + 1 + 1) σ hj' vN').ζ where
  τ := -(D.host.xi0 • (1 : Matrix (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) (Fin (GlobalTheory.SeeSaw.Model.nLine D).rank) D.host.E))
  map := link_map σ
  norm := link_norm _ σ

theorem cocpt_last : CoCpt (G.V (.grid D.R.m D.R.m)) := by
  have hm := D.R.two_le_m
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ fun j e => by
    injection e with e1
    omega
  refine GlobalTheory.SeeSaw.Inh.coCpt_of_isDefinite h.sigOK fun τ => Or.inl ?_
  rw [h.sig τ, h.rank]
  simp [Node.neg]

def castOm {V : HSp D} {n n' : ℕ} (h : n = n') (om : Om V (G.V (.grid D.R.m n))) : Om V (G.V (.grid D.R.m n')) :=
  Eq.rec (motive := fun k _ => Om V (G.V (.grid D.R.m k))) om h

theorem castOm_weil {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {n n' : ℕ} (h : n = n') {χV χW : (AE D)ˣ →* Circle}
    {om : Om V (G.V (.grid D.R.m n))} (hom : IsWeilDatumO ψ V _ χV χW om) :
    IsWeilDatumO ψ V (G.V (.grid D.R.m n')) χV χW (castOm G h om) := by
  subst h
  exact hom

def castSch {V : HSp D} {n n' : ℕ} (h : n = n') (f : WO V (G.V (.grid D.R.m n)) → ℂ) : WO V (G.V (.grid D.R.m n')) → ℂ :=
  Eq.rec (motive := fun k _ => WO V (G.V (.grid D.R.m k)) → ℂ) f h

theorem castSch_theta {ψ : AddChar (AF D.host.F) ℂ} {V : HSp D} {n n' : ℕ} (h : n = n') {f : WO V (G.V (.grid D.R.m n)) → ℂ}
    (hf : IsThetaFunO ψ V _ f) : IsThetaFunO ψ V (G.V (.grid D.R.m n')) (castSch G h f) := by
  subst h
  exact hf


variable {M} in
def lastAt (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : VolN (besDecAt G j 0 hj)) :
    Last Wl.ψ (G.V (.grid D.R.m D.R.m)) (besAt G hM j 0 hj vN) where
  J := jacAt G hM (j + 1) 0 (by omega)
  s := stepAt G Wl t hM j (by omega) (besDecAt G j 0 hj) (rowJac G (j + 1) (by omega) 0 (by omega))
  cptS := GlobalTheory.LastRed.cocpt_zero (rowJac G (j + 1) (by omega) 0 (by omega)) (cocpt_top G (j := j + 1) (by omega))
  cptT := cocpt_last G
  χS := G.chrS (.mu t D.R.m (j + 1))
  χT := G.chrT (.mu t D.R.m (j + 1))
  om := castOm G (show j + 1 + 1 = D.R.m by omega) (Wl.om (.mu t D.R.m (j + 1)))
  weil := castOm_weil G (show j + 1 + 1 = D.R.m by omega) (Wl.om_is (.mu t D.R.m (j + 1)) ⟨le_rfl, by omega⟩)
  vT := volAt hM (.grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩


variable {M} in
noncomputable def chainFrom (hM : M.Is t) : (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) →
    Chain Wl.ψ (G.V (.grid D.R.m D.R.m)) σ (besAt G hM j σ hj vN)
  | 0, j, hj, vN => .last (lastAt G Wl t hM j hj vN)
  | σ + 1, j, hj, vN =>
    .step (jacAt G hM (j + 1) (σ + 1) (by omega)) (besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)))
      (stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
        (besDecAt G (j + 1 + 1) σ (by omega)))
      (linkAt hM j σ hj vN (by omega) _) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some)
      (chainFrom hM σ (j + 1 + 1) (by omega) _)

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (Wl : G.Weil) (t : T) (M : Vol G)

theorem top_idx : 0 + 2 * ((D.R.m - 2) / 2) + 2 = D.R.m := by
  have := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  omega


variable {G t M} in
def topVN (hM : M.Is t) : VolN (besDecAt G 0 ((D.R.m - 2) / 2) top_idx) :=
  volNOf (d := rowBes G 0 (by have := D.R.two_le_m; omega) ((D.R.m - 2) / 2) (by have := top_idx (D := D); omega))
    (nFlag_diag _ (lam _) (lam_ne _)).symm
    (topVolN G M hM.isRow (by have := D.R.two_le_m; omega) (by have := top_idx (D := D); omega))


variable {t M} in
def topLev (hM : M.Is t) : BesLev D ((D.R.m - 2) / 2) := besAt G hM 0 ((D.R.m - 2) / 2) top_idx (topVN hM)


variable {M} in
noncomputable def chain (hM : M.Is t) : Chain Wl.ψ (G.V (.grid D.R.m D.R.m)) ((D.R.m - 2) / 2) (topLev G hM) :=
  chainFrom G Wl t hM _ 0 top_idx (topVN hM)


variable {M} in
noncomputable def dataFrom (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) :
    (σ j : ℕ) → (hj : j + 2 * σ + 2 = D.R.m) → (vN : VolN (besDecAt G j σ hj)) → (chainFrom G Wl t hM σ j hj vN).Data
  | 0, j, hj, _ => (getD t D.R.m D.R.m d j (by omega),
      castSch G (show j + 1 + 1 = D.R.m by omega) (getD t D.R.m D.R.m d (j + 1) (by omega)))
  | σ + 1, j, hj, _ => (getD t D.R.m D.R.m d j (by omega), getD t D.R.m D.R.m d (j + 1) (by omega),
      dataFrom hM d σ (j + 1 + 1) (by omega) _)

def AllTheta (d : PureT G (downPath t D.R.m D.R.m)) : Prop :=
  Path.Fam.All (fun a (f : Sch G a) => IsThetaFunO Wl.ψ (G.pS a.pair) (G.pT a.pair) f) d

variable {M} in
theorem dataFrom_isTheta (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) :
    ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj)),
      (chainFrom G Wl t hM σ j hj vN).IsTheta (dataFrom G Wl t hM d σ j hj vN)
  | 0, j, hj, _ => ⟨getD_all _ t D.R.m D.R.m d hd j (by omega),
      castSch_theta G _ (getD_all _ t D.R.m D.R.m d hd (j + 1) (by omega))⟩
  | σ + 1, j, hj, _ => ⟨getD_all _ t D.R.m D.R.m d hd j (by omega), getD_all _ t D.R.m D.R.m d hd (j + 1) (by omega),
      dataFrom_isTheta hM d hd σ (j + 1 + 1) (by omega) _⟩


variable {M} in
noncomputable def chainData (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) : (chain G Wl t hM).Data :=
  dataFrom G Wl t hM d _ 0 top_idx (topVN hM)


variable {M} in
theorem chainData_isTheta (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) :
    (chain G Wl t hM).IsTheta (chainData G Wl t hM d) :=
  dataFrom_isTheta G Wl t hM d hd _ 0 top_idx (topVN hM)

end GlobalTheory.RowChain
