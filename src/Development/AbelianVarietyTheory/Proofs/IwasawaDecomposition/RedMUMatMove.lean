module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DetSubMemOfConj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowConditionsAtCompanionFromReadings
public import Formalism.LocalToGlobal.Columns.ThetaOpenTwLevQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RedMUMatMove
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.Datum
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdjMove

section Ring

variable {A R k : Type} [CommRing A] [CommRing R] [CommRing k] {m n : ℕ}

def adj (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) :
    Matrix (Fin m) (Fin n) R := C * (Matrix.of Z).map φ * B

theorem adj_move (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B Y : Matrix (Fin n) (Fin n) R)
    (u : Matrix (Fin n) (Fin n) A) (h : (u.map φ)ᵀ * B * Y = B) (M : ℕ) (Z Z' w : Fin m → Fin n → A)
    (hZ : ∀ b, u *ᵥ Z' b = Z b + M • w b) : adj φ C B Z' = (adj φ C B Z + M • adj φ C B w) * Y := by
  have e : (Matrix.of Z).map φ + M • (Matrix.of w).map φ = (Matrix.of Z').map φ * (u.map φ)ᵀ := by
    ext b a
    have := congrArg φ (congrFun (hZ b) a)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.add_apply, Pi.smul_apply, map_add (f := _), map_nsmul] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.transpose_apply, ← this, mul_comm]
  unfold adj
  rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.add_mul, ← Matrix.mul_add, e]
  conv_lhs => rw [← h]
  simp only [Matrix.mul_assoc]

theorem adj_apply (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A)
    (b' : Fin m) (a : Fin n) : adj φ C B Z b' a = ∑ b, C b' b * ∑ j, φ (Z b j) * B j a := by
  unfold adj
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]

theorem red_eq (S : Subring R) (ρ : S →+* k) (M : ℕ) (hM : (M : k) = 0) (X X' W : Matrix (Fin m) (Fin n) R)
    (y : Matrix (Fin n) (Fin n) S) (hX : ∀ i j, X i j ∈ S) (hX' : ∀ i j, X' i j ∈ S) (hW : ∀ i j, W i j ∈ S)
    (h : X' = (X + M • W) * y.map S.subtype) (i : Fin m) (j : Fin n) :
    ρ ⟨X' i j, hX' i j⟩ = ∑ a, ρ ⟨X i a, hX i a⟩ * ρ (y a j) := by
  have e : (⟨X' i j, hX' i j⟩ : S) = ∑ a, (⟨X i a, hX i a⟩ + M • ⟨W i a, hW i a⟩) * y a j := by
    apply Subtype.ext
    simp [h, Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_add (f := _), map_nsmul, nsmul_eq_mul, hM, zero_mul, add_zero]

def lft (c : R) (P Q : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R := c • (P * Q)

theorem entry_eq {E : Type} [CommRing E] (f : E →+* R) (φ : A →+* R) (c : R) (P : Matrix (Fin m) (Fin m) R)
    (Q : Matrix (Fin m) (Fin m) E) (X : Matrix (Fin m) (Fin n) E) (G : Matrix (Fin n) (Fin n) E)
    (β : Matrix (Fin n) (Fin n) R) (Z : Fin m → Fin n → A) (h : ∀ b a, f (X b a) = φ (Z b a)) :
    (fun b a => c * (P * (Q * X * G).map f * β) b a) = adj φ (lft c P (Q.map f)) (G.map f * β) Z := by
  have e1 : X.map f = (Matrix.of Z).map φ := Matrix.ext h
  unfold adj lft
  rw [Matrix.smul_mul, Matrix.smul_mul, ← e1, Matrix.map_mul, Matrix.map_mul]
  ext b a
  simp only [Matrix.mul_assoc, Matrix.smul_apply, smul_eq_mul]

theorem unit_rel_ring (S : Subring R) (σ : A →+* A) (s : A →+* R) (J : Matrix (Fin n) (Fin n) A) (u : GL (Fin n) A)
    (β : GL (Fin n) R) (y : GL (Fin n) S) (hu : u ∈ Formalism.UG.UJ σ J)
    (hy : β * Formalism.UG.bc S.subtype y * β⁻¹ = Formalism.UG.bc s u) :
    (u.1.map (s.comp σ))ᵀ * (J.map s * β.1) * y.1.map S.subtype = J.map s * β.1 := by
  have h1 : β * Formalism.UG.bc S.subtype y = Formalism.UG.bc s u * β := by rw [← hy, inv_mul_cancel_right]
  have h2 : β.1 * y.1.map S.subtype = u.1.map s * β.1 := congrArg Units.val h1
  have h4 : (u.1.map σ)ᵀ * J * u.1 = J := hu
  have h5 := congrArg (fun N => Matrix.map N s) h4
  simp only [Matrix.map_mul] at h5
  have h6 : (u.1.map (s.comp σ))ᵀ * J.map s * u.1.map s = J.map s := h5
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h6]

theorem adj_int_ring (S : Subring R) (φ : A →+* R) (C : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin n) (Fin n) R)
    (s : Set (Fin n → A)) (La : Type) [Zero La] (v : La → Fin n → A) (v0 : ∀ j, v 0 j = 0)
    (h : ∀ x : Fin m → La, ∀ i j, adj φ C B (fun b => v (x b)) i j ∈ S)
    (hs : ∀ z ∈ s, ∃ t ∈ S, ∃ l, ∀ j, φ (z j) = t * φ (v l j))
    (w : Fin m → Fin n → A) (hw : ∀ b, w b ∈ AddSubgroup.closure s) (b' : Fin m) (a : Fin n) : adj φ C B w b' a ∈ S := by
  rw [adj_apply]
  refine sum_mem fun b _ => ?_
  have key : ∀ z ∈ AddSubgroup.closure s, C b' b * ∑ j, φ (z j) * B j a ∈ S := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨t, ht, l, hl⟩ := hs z hz
      have h1 := h (Pi.single b l) b' a
      rw [adj_apply, Finset.sum_eq_single b] at h1
      · have h2 := mul_mem ht h1
        rw [Pi.single_eq_same, mul_left_comm, Finset.mul_sum] at h2
        simpa only [hl, mul_assoc] using h2
      · intro c _ hc
        rw [Pi.single_eq_of_ne hc]
        simp [v0]
      · simp
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, mul_add]
      exact add_mem hx hy
    | neg x _ hx =>
      simp only [Pi.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
      exact neg_mem hx
  exact key _ (hw b)

end Ring

variable {D : D7}

noncomputable def barSwap (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* EAf D :=
  (Lev.swapAE D).comp (sigR (Af D.host.F) D.sp.cm.sig)

theorem barSwap_tmul (a : Af D.host.F) (x : D.host.E) :
    barSwap D (a ⊗ₜ[D.host.F] x) = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * barSwap D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) := by
  change D.sp.cm.sig x ⊗ₜ[D.host.F] a = ((1 : D.host.E) ⊗ₜ[D.host.F] a) * (D.sp.cm.sig x ⊗ₜ[D.host.F] 1)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem uMat_eq (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D)
    (X : Fin S.rank → Fin T.rank → D.host.E) :
    uMat S T βS βT e X = adj (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D)))
      (T.gram.map (eToEAf D) * βT.1) fun b => finVec T (X b) :=
  entry_eq (eToEAf D) (barSwap D) _ _ _ _ _ _ _ fun _ _ => rfl

theorem unit_rel (T : HSp D) (βT : GL (Fin T.rank) (EAf D)) (u : GA D T)
    (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) (hy : frGL βT y = Lev.finE T u) :
    ((finHom T u).1.map (barSwap D))ᵀ * (T.gram.map (eToEAf D) * βT.1) * y.1.map (Subring.subtype _) =
      T.gram.map (eToEAf D) * βT.1 :=
  unit_rel_ring _ (sigR (Af D.host.F) D.sp.cm.sig) (Lev.swapAE D) (JR (Af D.host.F) T.gram) (finHom T u) βT y
    (GlobalTheory.UnitarySplit.finHom_mem T u) hy

theorem adj_int {m : ℕ} (T : HSp D) (C : Matrix (Fin m) (Fin m) (EAf D)) (B : Matrix (Fin T.rank) (Fin T.rank) (EAf D))
    (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E))
    (h : ∀ x : Fin m → La, IsIntM (adj (barSwap D) C B fun b => finVec T (ι (x b))))
    (w : Fin m → Fin T.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : ∀ b, w b ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι)) : IsIntM (adj (barSwap D) C B w) := by
  refine adj_int_ring _ (barSwap D) C B _ La (fun l => finVec T (ι l)) (fun j => ?_) h ?_ w hw
  · show (1 : Af D.host.F) ⊗ₜ[D.host.F] (ι 0 j) = 0
    rw [LinearMap.map_zero]
    exact TensorProduct.tmul_zero _ _
  · rintro z ⟨α, hα, _, ⟨l, rfl⟩, rfl⟩
    exact ⟨(1 : D.host.E) ⊗ₜ[D.host.F] α, Subring.subset_closure (Or.inr ⟨⟨α, hα⟩, rfl⟩), l,
      fun j => barSwap_tmul α (ι l j)⟩


set_option maxHeartbeats 800000 in
theorem redM_uMat_move : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D) (La : Type) [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)), (∀ x : Fin S.rank → La, IsIntM (uMat S T βS βT e fun b => ι (x b))) → ∀ (u : GA D T) (y : GL (Fin T.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)), frGL βT y = Lev.finE T u → ∀ (M : ℕ) (PP : Pl D.host.E), (M : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x x' : Fin S.rank → La, (∀ b, ∃ w ∈ GlobalTheory.AdLat.hat D.host.F (Set.range ι), (finHom T u).1.mulVec (finVec T (ι (x' b))) = finVec T (ι (x b)) + M • w) → redM PP (uMat S T βS βT e fun b => ι (x' b)) = redM PP (uMat S T βS βT e fun b => ι (x b)) * y.1.map (resS D.host.F PP) := by
  intro D S T βS βT e La _ _ ι hint u y hy M PP hM x x' hx
  choose w hw hx using hx
  have hW := adj_int T _ _ La ι (fun x => by rw [← uMat_eq S T βS βT e]; exact hint x) w hw
  have hmv := adj_move (barSwap D) (lft (toEAf D e) (βS⁻¹).1 (S.gram⁻¹.map (eToEAf D))) _ _ _ (unit_rel T βT u y hy) M
    (fun b => finVec T (ι (x b))) (fun b => finVec T (ι (x' b))) w hx
  rw [← uMat_eq S T βS βT e, ← uMat_eq S T βS βT e] at hmv
  have hM' : (M : kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hM
  ext i j
  have := red_eq _ (resS D.host.F PP) M hM' _ _ _ y.1 (hint x) (hint x') hW hmv i j
  rw [Matrix.mul_apply]
  unfold redM
  rw [dite_eq_left (hint x' i j), this]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dite_eq_left (hint x i a)]
  rfl

end GlobalTheory.AdjMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevel
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtInProd

section Cut

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def cutMat (e : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := e • M + (1 - e) • 1

theorem cutMat_one (e : R) : cutMat e (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [cutMat, ← add_smul, add_sub_cancel, one_smul]

theorem cutMat_one_left (M : Matrix (Fin n) (Fin n) R) : cutMat 1 M = M := by
  rw [cutMat, one_smul, sub_self, zero_smul, add_zero]

theorem cutMat_zero_left (M : Matrix (Fin n) (Fin n) R) : cutMat 0 M = 1 := by
  rw [cutMat, zero_smul, sub_zero, one_smul, zero_add]

theorem cutMat_mul {e : R} (he : e * e = e) (M N : Matrix (Fin n) (Fin n) R) :
    cutMat e (M * N) = cutMat e M * cutMat e N := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [cutMat, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, he, h1,
    h2, h3, zero_smul, add_zero, zero_add]

theorem cutMat_mul_compl {e : R} (he : e * e = e) (M : Matrix (Fin n) (Fin n) R) :
    cutMat e M * cutMat (1 - e) M = M := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [cutMat, sub_sub_cancel, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem map_cutMat (f : R →+* S) (e : R) (M : Matrix (Fin n) (Fin n) R) :
    (cutMat e M).map f = cutMat (f e) (M.map f) := by
  ext i j
  by_cases h : i = j <;> simp [cutMat, Matrix.one_apply, h]

theorem conjT_cutMat (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix (Fin n) (Fin n) R) :
    ReciprocityTheory.Aut.conjT σ (cutMat e M) = cutMat e (ReciprocityTheory.Aut.conjT σ M) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ReciprocityTheory.Aut.conjT, cutMat, hσ]
  · simp [ReciprocityTheory.Aut.conjT, cutMat, hσ, Matrix.one_apply, h, Ne.symm h]

def cutHom {e : R} (he : e * e = e) : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R where
  toFun := cutMat e
  map_one' := cutMat_one e
  map_mul' := cutMat_mul he

end Cut

section Adelic

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open Classical

def idemF (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AFplus L :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem idemF_apply (v w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (idemF (L := L) v) w = if w = v then 1 else 0 := rfl

theorem idemF_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idemF (L := L) v * idemF v = idemF v := by
  apply Subtype.ext
  funext w
  show (if w = v then (1 : w.adicCompletion (maximalRealSubfield L)) else 0) * (if w = v then 1 else 0) = (if w = v then 1 else 0)
  split_ifs <;> simp


variable (L) in
def eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] idemF v

theorem eA_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : eA L v * eA L v = eA L v := by
  rw [eA, Algebra.TensorProduct.tmul_mul_tmul, one_mul, idemF_mul]

theorem conj_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : conjAL L (eA L v) = eA L v := by
  simp [conjAL, eA, Algebra.TensorProduct.map_tmul]

theorem compAt_eA (w v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    compAt L w (eA L v) = if w = v then 1 else 0 := by
  have : compAt L w (eA L v) = (1 : L) ⊗ₜ[maximalRealSubfield L] ((idemF (L := L) v) w) := rfl
  rw [this, idemF_apply]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

theorem eA_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : eA L v ∈ ALint L :=
  Subring.subset_closure (Or.inr ⟨idemF v, fun w => by
    rw [idemF_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _, rfl⟩)

def cutGA {e : AL L} (he : e * e = e) (hc : conjAL L e = e) : GA L n →* GA L n :=
  ((Units.map (cutHom (n := n) he)).comp (GA L n).subtype).codRestrict _ (fun g => by
    have hg : (g.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) g.1 = 1 := g.2
    show cutMat e (g.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (cutMat e g.1) = 1
    rw [conjT_cutMat _ hc, ← cutMat_mul he, hg, cutMat_one])

theorem cutGA_val {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (g : GA L n) :
    ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)) = cutMat e g.1 := rfl

theorem cutGA_mem_Umax {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (heI : e ∈ ALint L) {g : GA L n}
    (hg : g ∈ Umax L n) : cutGA he hc g ∈ Umax L n := by
  have hg' : ∀ i j, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := hg
  show ∀ i j, ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
  intro i j
  rw [cutGA_val]
  simp only [cutMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  refine Subring.add_mem _ (Subring.mul_mem _ heI (hg' i j)) (Subring.mul_mem _ (Subring.sub_mem _ (Subring.one_mem _) heI) ?_)
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

end Adelic

section Adelic2

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cut_map_compAt {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (g : GA L n)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) =
      cutMat (compAt L w e) ((g.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w)) := by
  rw [cutGA_val, map_cutMat]

theorem one_sub_eA_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (1 - eA L v) * (1 - eA L v) = 1 - eA L v := by
  rw [mul_sub, mul_one, sub_mul, one_mul, eA_mul, sub_self, sub_zero]

theorem conj_one_sub_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    conjAL L (1 - eA L v) = 1 - eA L v := by
  rw [map_sub, map_one, conj_eA]

theorem triv_cut_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    TrivOutside {v} (cutGA (eA_mul v) (conj_eA v) g) := by
  intro w hw
  rw [cut_map_compAt, compAt_eA, if_neg (fun h => hw (Set.mem_singleton_iff.2 h)), cutMat_zero_left]

theorem triv_cut_one_sub_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    TrivOutside {v}ᶜ (cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) g) := by
  intro w hw
  have hwv : w = v := by simpa using hw
  rw [cut_map_compAt, map_sub, map_one, compAt_eA, if_pos hwv, sub_self, cutMat_zero_left]

theorem cut_eA_at (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    ((cutGA (eA_mul v) (conj_eA v) g).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) =
      (g.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  rw [cut_map_compAt, compAt_eA, if_pos rfl, cutMat_one_left]

theorem cut_mul_cut (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    cutGA (eA_mul v) (conj_eA v) g * cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) g = g :=
  Subtype.ext (Units.ext (cutMat_mul_compl (eA_mul v) _))

end Adelic2

theorem main : ∀ (D : D7) (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), NG.IsProdLevel (stdJ (datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi)) := by
  intro D n hr Pg Q ψ chi xi κ hκ v
  obtain ⟨hUA, hSt, hred, -⟩ := GlobalTheory.T.stdMaximalCompact_reduction_properties D n
  set κ1 := cutGA (eA_mul v) (conj_eA v) κ with hκ1
  set κ2 := cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) κ with hκ2
  have hκ' := Subgroup.mem_comap.1 hκ
  rw [mem_lev, mem_parLev] at hκ'
  obtain ⟨⟨-, hSκ, hPg, hQ⟩, hT⟩ := hκ'
  have hUm : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := (hSt κ).1 hSκ
  have hUm1 : κ1 ∈ ReciprocityTheory.Aut.Umax D.host.E n := cutGA_mem_Umax _ _ (eA_mem v) hUm
  have hUm2 : κ2 ∈ ReciprocityTheory.Aut.Umax D.host.E n :=
    cutGA_mem_Umax _ _ (Subring.sub_mem _ (Subring.one_mem _) (eA_mem v)) hUm
  have key : ∀ PP, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ1) = redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) ∨
      redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ1) = 1 := by
    intro PP
    have hov : NG.OverPl PP (underPl (maximalRealSubfield D.host.E) PP) := (underPl_asIdeal (F := maximalRealSubfield D.host.E) PP).symm
    by_cases h : underPl (maximalRealSubfield D.host.E) PP = v
    · left
      rw [← cut_mul_cut v κ, map_mul, redFn_mul ((hSt _).2 hUm1) ((hSt _).2 hUm2),
        hred κ2 hUm2 {v}ᶜ _ PP (triv_cut_one_sub_eA v κ) (h ▸ hov) (by simp), mul_one]
    · right
      exact hred κ1 hUm1 {v} _ PP (triv_cut_eA v κ) hov h
  refine ⟨κ1, ?_, triv_cut_eA v κ, cut_eA_at v κ⟩
  apply Subgroup.mem_comap.2
  rw [mem_lev, mem_parLev]
  refine ⟨⟨hUA κ1, (hSt κ1).2 hUm1, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rcases key PP with h | h <;> rw [h]
    · exact hPg PP hP
    · exact Subgroup.one_mem _
  · rcases key PP with h | h <;> rw [h]
    · exact hQ PP hP
    · exact Subgroup.one_mem _
  · intro PP _
    have hT' := hT PP (Set.mem_univ _)
    show upperLeftBlock _ (redFn _ PP.1 (km D n κ1)) ∈ _
    rcases key PP.1 with h | h <;> rw [h]
    · exact hT'
    · have h2 : upperLeftBlock (MtIn.datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi).hr (1 : GL (Fin n) (kP PP.1)) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
      show upperLeftBlock (MtIn.datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi).hr (1 : GL (Fin n) (kP PP.1)) ∈ unip (kP PP.1) D.R.r
      rw [h2]
      exact (unip (kP PP.1) D.R.r).one_mem

end GlobalTheory.MtInProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProdLevel_stdFrame_twoBlockUnipotentLevel : ∀ (D : D7) (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), NG.IsProdLevel (stdJ (datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi)) := by
  first | exact @GlobalTheory.MtInProd.main | exact GlobalTheory.MtInProd.main | (intros; apply GlobalTheory.MtInProd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelAtTwistPrimesIsOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelAtTwistPrimesIsOpen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx


open Classical in
set_option maxHeartbeats 4000000 in
theorem thetaOpen_levQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}, L.Ok Ch sel mu cst G m2 → (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (j : ℕ) (b : L.β j), ThetaOpen (L.levQ j b) := by
  intro X Pr R Ch sel S mu cst L G m2 hL hQg j b P
  have hc : cst.Ok := hL.cst_ok
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  let h : AutY X R j := L.h j b P'
  have hPg := hQg P.1 P.2
  have hq := ciQ_mem P.1
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    exact P.1.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0)
  obtain ⟨a, ha⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨b', hb⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h⁻¹ : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨e, he⟩ := qth_exists_e P.1 hq0
  refine ⟨a + b' + e + 1, by omega, fun g hg => ?_⟩
  let r : AutY X R j := twZrExt (c := cOf R j) g.1
  have hr := qth_ext_close (c := cOf R j) P.1 g.1 _ hg
  have hrinv : r⁻¹ = twZrExt (c := cOf R j) (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 := LinearEquiv.ext fun v => rfl
  have hinv {E : Type} [Field E] [NumberField E] [StarRing E]
      (P : HeightOneSpectrum (𝓞 E)) {n N : ℕ} (g : ↥(GLint E n P))
      (hg : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n)) :
      lqPrinc P N ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
    unfold lqPrinc at hg ⊢
    intro i j
    set A := LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hA
    set B := LinearMap.toMatrix'
      ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hB
    have hBA : B * A = 1 := by
      rw [hA, hB, ← LinearMap.toMatrix'_comp]
      have hc : ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).comp
          ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = LinearMap.id := by
        refine LinearMap.ext fun x => ?_
        have hx : ((((g⁻¹ * g : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n)) x = x := by
          rw [inv_mul_cancel]
          rfl
        exact hx
      rw [hc, LinearMap.toMatrix'_id]
    have hBle : ∀ a k, P.valuation E (B a k) ≤ 1 := by
      intro a k
      rw [hB, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
      have hs : (Pi.single k (1 : E) : Sp E n) ∈ stdAt E n P := by
        show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
        rw [mem_localization_standardLattice]
        intro t
        rw [qth_intAt_iff]
        by_cases h : t = k
        · subst h
          simp
        · simp [Pi.single_apply, h]
      have hmem : ((g⁻¹ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (stdAt E n P) :=
        (g⁻¹ : GLint E n P).2
      have h2 := (hmem _).2 hs
      have h3 := (mem_localization_standardLattice P _).1 h2 a
      rw [qth_intAt_iff] at h3
      exact h3
    have hBm : B - 1 = -(B * (A - 1)) := by
      rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]
    rw [hBm, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
    refine Valuation.map_sum_le _ (fun k _ => ?_)
    rw [map_mul]
    calc _ ≤ 1 * P.valuation E ((A - 1) k j) := mul_le_mul' (hBle i k) le_rfl
      _ ≤ _ := by rw [one_mul]; exact hg k j
  
  have hr' := qth_ext_close (c := cOf R j) P.1 (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 _ (hinv P.1 g hg)
  have hy : QClose P.1 (qOf P.1) (h⁻¹ * r * h) := qth_conj_close P.1 (qOf P.1) h r a b' _ e ha hb hr he (by omega)
  have hy' : QClose P.1 (qOf P.1) (h⁻¹ * r * h)⁻¹ := by
    have e3 : (h⁻¹ * r * h)⁻¹ = h⁻¹ * r⁻¹ * h := by simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e3, hrinv]
    exact qth_conj_close P.1 (qOf P.1) h _ a b' _ e ha hb hr' he (by omega)
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1 := by
    rw [twJat_Q cst.sharp j hPg]
    exact qth_mem_JQ P.1 (qOf P.1) hq0 (R.k + j) _ hy hy'
  have hC : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := R) cst.sharp j P.1) h := by
    refine ⟨zeroExtension_mem_R1 g.1, ?_⟩
    show (MulAut.conj h⁻¹) r ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1
    simpa [MulAut.conj_apply] using hJ
  have hmem : g.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 h := ⟨r, hC, twZrExt_inX g.1⟩
  have hH : g ∈ (L.levQ j b P).H := by
    rw [hL.grpQ j b P]
    exact Subgroup.mem_subgroupOf.2 hmem
  refine ⟨hH, ?_⟩
  apply Units.ext
  rw [hL.chrQ j b P ⟨g, hH⟩ r hC (fun x => twZrExt_inX g.1 x)]
  have hstd : r ∈ stabL X.E (R.N j + cOf R j) (stdAt X.E (R.N j + cOf R j) P.1) :=
    twZrExt_stab P.1 _ (fun v => ciMem_stdAt P.1 v) g.2
  have hint : IntAt P.1 (Loc.n1Arg r) := by
    unfold Loc.n1Arg
    refine ciIntAt_sum _ _ fun i _ => ?_
    have hv : r (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) ∈ stdAt X.E (R.N j + cOf R j) P.1 :=
      (hstd _).2 (twZr_eN_mem P.1 _ _)
    rw [ciMem_stdAt] at hv
    unfold Loc.atN
    split_ifs
    · exact hv _
    · exact ciIntAt_zero
  unfold chiInv
  rw [hc.psi_int P' _ hint, inv_one, one_mul]
  unfold lamRow
  rw [if_neg hPg]
  have hlam {P : HeightOneSpectrum (𝓞 X.E)} (hq : ((qOf P : ℕ) : 𝓞 X.E) ∈ P.asIdeal) (hq0 : ((qOf P : ℕ) : X.E) ≠ 0) {j : ℕ}
      (ξ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ) (y : AutY X R j) (hy : QClose P (qOf P) y) :
      LocE.lamQB ξ (R.k + j) (R.N j) (y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) = 1 := by
    classical
    unfold LocE.lamQB
    set D : Matrix (Fin (R.N j - (R.k + j))) (Fin (R.N j - (R.k + j))) X.E := Matrix.of fun s t : Fin (R.N j - (R.k + j)) =>
      Loc.atN ((y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) (Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1))) (R.k + j + s.1) with hD
    have hent : ∀ s t : Fin (R.N j - (R.k + j)), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 X.E ⧸ P.asIdeal)) s t := by
      intro s t
      have hs : R.k + j + s.1 < R.N j + cOf R j := by have := s.2; omega
      have ht : R.k + j + t.1 < R.N j + cOf R j := by have := t.2; omega
      have e1 : Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1) = Pi.single ⟨R.k + j + t.1, ht⟩ 1 := by
        funext l
        unfold Loc.eN
        rw [Pi.single_apply]
        congr 1
        apply propext
        constructor
        · intro h; exact Fin.ext h
        · intro h; rw [h]
      have e2 : D s t = ((toGLm X.E (R.N j + cOf R j) y : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E) ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩ := by
        rw [qsp_toGLm_apply, hD, Matrix.of_apply, e1]
        unfold Loc.atN
        rw [dite_eq_left hs]
        rfl
      obtain ⟨h1, h2⟩ := qth_red_entry P (qOf P) hq0 hq hy ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩
      rw [e2]
      refine ⟨h1, ?_⟩
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      by_cases hst : s = t
      · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst, redP_one]
      · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst, redP_zero]
    have hdet : redP P D.det = 1 := by
      rw [redP_det D fun s t => (hent s t).1]
      have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
      rw [this, Matrix.det_one]
    unfold LocE.unitV
    have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
    rw [dite_eq_left hu]
    have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
    rw [this, map_one, Units.val_one, inv_one]
  exact hlam hq hq0 _ _ hy

end GlobalTheory.Mem.Col2.ChEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelAtTwistPrimesIsOpenStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelAtTwistPrimes_isOpen : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}, L.Ok Ch sel mu cst G m2 → (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (j : ℕ) (b : L.β j), ThetaOpen (L.levQ j b) := by
  first | exact @GlobalTheory.Mem.Col2.ChEx.thetaOpen_levQ | exact GlobalTheory.Mem.Col2.ChEx.thetaOpen_levQ | (intros; apply GlobalTheory.Mem.Col2.ChEx.thetaOpen_levQ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceDoubleCosetOperatorSemisimpleTypeSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceDoubleCosetOperatorSemisimpleTypeSpace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeNormal

open GlobalTheory.HeckeStdFacts GlobalTheory.CoefDuty

theorem eq_smul_of_normal {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (V : Submodule ℂ M)
    (T S : M →ₗ[ℂ] M) (hpos : ∀ x ∈ V, B x x = 0 → x = 0)
    (hT : ∀ x ∈ V, T x ∈ V) (hS : ∀ x ∈ V, S x ∈ V) (hadj : ∀ x ∈ V, ∀ y ∈ V, B (T x) y = B x (S y))
    (hc : ∀ x ∈ V, T (S x) = S (T x)) {f : M} (hf : f ∈ V) (μ : ℂ)
    (h : T (T f - μ • f) = μ • (T f - μ • f)) : T f = μ • f := by
  have hg : T f - μ • f ∈ V := V.sub_mem (hT f hf) (V.smul_mem μ hf)
  have adj : ∀ x ∈ V, ∀ y ∈ V, B (T x - μ • x) y = B x (S y - starRingEnd ℂ μ • y) := by
    intro x hx y hy
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_sub, map_smul, hadj x hx y hy]
  have hfg := adj f hf _ hg
  rw [← sub_eq_zero]
  generalize T f - μ • f = g at hg h hfg ⊢
  have hu : S g - starRingEnd ℂ μ • g ∈ V := V.sub_mem (hS g hg) (V.smul_mem _ hg)
  have h0 : T (S g - starRingEnd ℂ μ • g) - μ • (S g - starRingEnd ℂ μ • g) = 0 := by
    rw [map_sub, map_smul, hc g hg, h, map_smul, smul_sub, smul_comm μ (starRingEnd ℂ μ) g, sub_self]
  have h1 := adj _ hu g hg
  rw [h0, map_zero, LinearMap.zero_apply] at h1
  rw [hpos _ hu h1.symm, map_zero] at hfg
  exact hpos g hg hfg

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => NumberField.maximalRealSubfield L

theorem rt_mem_all {a : NG.AlgWt L n} (h : GAf L n) {f : GAf L n → a.W} (hf : f ∈ NG.AFall L n a.ρ) :
    NG.rt L n h f ∈ NG.AFall L n a.ρ := by
  obtain ⟨N, hN, h2⟩ := hf.2
  obtain ⟨⟨N', hN', hc⟩, -, -⟩ :=
    GlobalTheory.CongIndex.finite_index_conj L n (Umax L n) GlobalTheory.ClassPet.umax_bounded h N hN
  exact (GlobalTheory.ClassPet.rt_mem a hf hN' h2 hc).1

def sph (a : NG.AlgWt L n) (v : HeightOneSpectrum (𝓞 L⁺)) : Submodule ℂ (GAf L n → a.W) where
  carrier := {f | f ∈ NG.AFall L n a.ρ ∧ ∀ κ ∈ locK n v, NG.rt L n κ f = f}
  zero_mem' := ⟨zero_mem _, fun _ _ => map_zero _⟩
  add_mem' := fun hf hg => ⟨add_mem hf.1 hg.1, fun κ hκ => by rw [map_add (f := _), hf.2 κ hκ, hg.2 κ hκ]⟩
  smul_mem' := fun c f hf => ⟨Submodule.smul_mem _ c hf.1, fun κ hκ => by rw [map_smul, hf.2 κ hκ]⟩

def IsReps (v : HeightOneSpectrum (𝓞 L⁺)) (α : GAf L n) (R : Finset (GAf L n)) : Prop :=
  (∀ γ ∈ R, ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, γ = k₁ * α * k₂) ∧
    ∀ x, (∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n

theorem IsReps.card_ne_zero {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R) :
    (R.card : ℂ) ≠ 0 := by
  obtain ⟨γ, ⟨hγ, -⟩, -⟩ := h.2 α ⟨1, one_mem _, 1, one_mem _, by simp⟩
  exact_mod_cast Finset.card_ne_zero_of_mem hγ

theorem sum_mem_sph {a : NG.AlgWt L n} {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} (hα : TrivOutside {v} α)
    {R : Finset (GAf L n)} (h : IsReps v α R) {f : GAf L n → a.W} (hf : f ∈ sph a v) :
    ∑ γ ∈ R, NG.rt L n γ f ∈ sph a v := by
  classical
  refine ⟨sum_mem fun γ _ => rt_mem_all γ hf.1, fun κ hκ => ?_⟩
  have hD : ∀ x ∈ {x : GAf L n | ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * α * k₂}, TrivOutside {v} x := by
    rintro _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact triv_mul (triv_mul h₁.2 hα) h₂.2
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f := fun κ h1 h2 => hf.2 κ ⟨h1, h2⟩
  have e1 := heckeD_eq_sum (J := Umax L n) hD h.1 h.2 hfix
  have e2 := heckeD_eq_sum (J := Umax L n) hD (R := R.image fun γ => κ * γ)
    (by
      intro γ hγ
      obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ
      obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 δ hδ
      exact ⟨κ * k₁, mul_mem hκ h₁, k₂, h₂, by simp only [mul_assoc]⟩)
    (by
      rintro _ ⟨k₁, h₁, k₂, h₂, rfl⟩
      obtain ⟨γ, ⟨hγ, hm⟩, hu⟩ := h.2 (κ⁻¹ * k₁ * α * k₂) ⟨κ⁻¹ * k₁, mul_mem (inv_mem hκ) h₁, k₂, h₂, rfl⟩
      refine ⟨κ * γ, ⟨Finset.mem_image.2 ⟨γ, hγ, rfl⟩, ?_⟩, ?_⟩
      · convert hm using 1
        group
      · rintro _ ⟨hδ, hm'⟩
        obtain ⟨δ, hδ', rfl⟩ := Finset.mem_image.1 hδ
        rw [hu δ ⟨hδ', ?_⟩]
        convert hm' using 1
        group) hfix
  rw [Finset.sum_image (mul_right_injective κ).injOn, e1] at e2
  conv_rhs => rw [e2]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, rt_rt]

theorem form_sum {a : NG.AlgWt L n} {B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ} (hB : IsPetersson a B)
    {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R)
    {f g : GAf L n → a.W} (hf : f ∈ sph a v) (hg : g ∈ sph a v) :
    B f (∑ γ ∈ R, NG.rt L n γ g) = R.card * B f (NG.rt L n α g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 γ hγ
  rw [← rt_rt, hg.2 k₂ h₂, ← rt_rt]
  conv_lhs => rw [← hf.2 k₁ h₁]
  exact (hB f hf.1 _ (rt_mem_all α hg.1)).2.2 k₁

theorem form_sum_left {a : NG.AlgWt L n} {B : (GAf L n → a.W) →ₗ⋆[ℂ] (GAf L n → a.W) →ₗ[ℂ] ℂ} (hB : IsPetersson a B)
    {v : HeightOneSpectrum (𝓞 L⁺)} {α : GAf L n} {R : Finset (GAf L n)} (h : IsReps v α R)
    {f g : GAf L n → a.W} (hf : f ∈ sph a v) (hg : g ∈ sph a v) :
    B (∑ γ ∈ R, NG.rt L n γ f) g = R.card * B f (NG.rt L n α⁻¹ g) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 γ hγ
  have e : g = NG.rt L n (k₁ * α) (NG.rt L n α⁻¹ g) := by
    rw [rt_rt, mul_inv_cancel_right, hg.2 k₁ h₁]
  rw [← rt_rt, hf.2 k₂ h₂]
  conv_lhs => rw [e]
  exact (hB f hf.1 _ (rt_mem_all α⁻¹ hg.1)).2.2 _

theorem sum_semisimple (a : NG.AlgWt L n) (s : SplitPlace L) {α : GAf L n} (hα : TrivOutside {s.v} α)
    {R : Finset (GAf L n)} (h : IsReps s.v α R) (c : ℂ) {f : GAf L n → a.W} (hf : f ∈ sph a s.v) (μ : ℂ)
    (hμ : c • ∑ γ ∈ R, NG.rt L n γ (c • ∑ γ ∈ R, NG.rt L n γ f - μ • f) = μ • (c • ∑ γ ∈ R, NG.rt L n γ f - μ • f)) :
    c • ∑ γ ∈ R, NG.rt L n γ f = μ • f := by
  obtain ⟨β, hβ⟩ := GlobalTheory.InvFormBdd.exists_isInvForm L n a
  obtain ⟨B, hB, -⟩ := GlobalTheory.ClassPet.classSum_eq_pet L n a β hβ
  obtain ⟨R', h'⟩ : ∃ R', IsReps s.v α⁻¹ R' := exists_repsU s.v α⁻¹
  have key := eq_smul_of_normal B (sph a s.v) (c • ∑ γ ∈ R, NG.rt L n γ)
    ((starRingEnd ℂ c * R.card / R'.card) • ∑ γ ∈ R', NG.rt L n γ)
    (fun x hx h0 => by
      by_contra hne
      have := (hB x hx.1 x hx.1).2.1 hne
      rw [h0] at this
      simp at this)
    (fun x hx => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply]
      exact Submodule.smul_mem _ _ (sum_mem_sph hα h hx))
    (fun x hx => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply]
      exact Submodule.smul_mem _ _ (sum_mem_sph (triv_inv hα) h' hx))
    (fun x hx y hy => by
      rw [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sum_apply, map_smulₛₗ,
        LinearMap.smul_apply, map_smul, form_sum_left hB h hx hy, form_sum hB h' hx hy, smul_eq_mul, smul_eq_mul]
      have := h'.card_ne_zero
      field_simp)
    (fun x hx => by
      have conv : ∀ (δ x : GAf L n), (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧
          x = k₁ * δ * k₂) ↔ ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * δ * k₂ := fun δ x =>
        ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
          fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
      have e := GlobalTheory.SplitHeckeComm.doubleCoset_comm L n a.W s α α⁻¹ R R' hα (triv_inv hα)
        (fun y hy => h.2 y ((conv _ _).1 hy)) (fun y hy => (conv _ _).2 (h.1 y hy))
        (fun y hy => h'.2 y ((conv _ _).1 hy)) (fun y hy => (conv _ _).2 (h'.1 y hy)) x
        (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
      rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smul,
        smul_comm]
      simp only [LinearMap.sum_apply]
      rw [e]) hf μ
  simp only [LinearMap.smul_apply, LinearMap.sum_apply] at key
  exact key hμ

theorem tN_semisimple : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f := by
  intro L _ _ _ n a J χ B hN hB s ϖ k hv hϖ _ _ f hf μ hμ
  obtain ⟨α, hα, hset⟩ := exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, h⟩ : ∃ R, IsReps s.v α R := exists_repsU s.v α
  have hT : ∀ g ∈ NG.TypeSp a.ρ J χ, NG.tN J s ϖ k g = ((s.q : ℂ) ^ (k * (n - 1)))⁻¹ • ∑ γ ∈ R, NG.rt L n γ g := by
    intro g hg
    unfold NG.tN
    rw [heckeD_type hB hv (fun γ hγ => (hset γ).2 (h.1 γ hγ)) (fun x hx => h.2 x ((hset x).1 hx)) hg]
  have hg : NG.tN J s ϖ k f - μ • f ∈ NG.TypeSp a.ρ J χ :=
    sub_mem (Submodule.smul_mem _ _ (heckeD_mem hN hB hv hϖ k hf)) (Submodule.smul_mem _ _ hf)
  rw [hT _ hg, hT f hf] at hμ
  rw [hT f hf]
  exact sum_semisimple a s hα h _
    ⟨hf.1, fun κ hκ => fixed_of_type hB hv hf κ ((hyp_at hB hv κ hκ.2).1.2 hκ.1) hκ.2⟩ μ hμ

end GlobalTheory.HeckeNormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceDoubleCosetOperatorSemisimpleTypeSpaceStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleCosetOperator_semisimple_typeSpace : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f := by
  first | exact @GlobalTheory.HeckeNormal.tN_semisimple | exact GlobalTheory.HeckeNormal.tN_semisimple | (intros; apply GlobalTheory.HeckeNormal.tN_semisimple <;> assumption)
end
end
