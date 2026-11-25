import Tetrahedral.NormEleven.D2Entrance
import Tetrahedral.NormEleven.D2Congruences
import Tetrahedral.NormEleven.LatticeDirectionData
import Tetrahedral.NormEleven.DyadicSimple

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace Tetrahedral.NormEleven.Dyadic2
open Quartic2 R

def centre (c : Fin 2) : ℤ := ![0,-1] c

/-- The two close roots share one class modulo four. A single parity split
separates them; the third root has its own, shorter local period. -/
theorem roots (m : ℤ) (hm : f (xi0*(↑(rhoU^m):R))=0) : m=0 ∨ m= -4 ∨ m= -1 := by
  obtain ⟨c,hc⟩ : ∃ c : Fin 2, m%4=centre c%4 := by
    rcases Entrance2.root_residue m hm with h|h
    · exact ⟨0,by simpa [centre] using h⟩
    · exact ⟨1,by simpa [centre] using h⟩
  have hd : (4:ℤ) ∣ m-centre c := Int.dvd_of_emod_eq_zero (by
    rw [Int.sub_emod,hc,sub_self,Int.zero_emod])
  obtain ⟨a,ha⟩ := hd
  have he : m=centre c+4*a := by omega
  have hp : rhoU^m=rhoU^(centre c)*(rhoU^4)^a := by
    rw [← zpow_natCast,← zpow_mul,← zpow_add]
    norm_num; rw [← he]
  have hb : f ((xi0*(↑(rhoU^(centre c)):R))*(↑((rhoU^4)^a):R))=0 := by
    simpa only [hp,Units.val_mul,mul_assoc] using hm
  fin_cases c
  · change m=0+4*a at he
    change f (xi0*(↑((rhoU^4)^a):R))=0 at hb
    rcases DyadicSimple.pair f (rhoU^4) xi0 (fun j i hi =>
      Local2.unique j i (by simpa only [← pow_mul,Nat.reduceMul,Local2.centre,DyadicSimple.centre] using hi)) a hb with h|h
    · left; omega
    · right; left; omega
  · change m= -1+4*a at he
    change f ((xi0*(↑(rhoU^(-1:ℤ)):R))*(↑((rhoU^4)^a):R))=0 at hb
    have ha0 := Local2Odd.unique 0 a hb
    right; right; omega

theorem exclude (r : ℕ) (m : ℤ)
    (hf : f (xi1*(↑(rhoU^m):R))=0)
    (hr : (xi1*(↑(rhoU^m):R)) 0=2*(r:ℤ)^2) : False :=
  Extra2.exclude r m hf hr

end Tetrahedral.NormEleven.Dyadic2
