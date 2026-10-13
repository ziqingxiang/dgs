module

public import DGS.Main
public import DGS.S04_Reduction.LargeDegrees
public import DGS.S09_Smooth.Smooth
public import DGS.S13_Deg3.Moderate
public import DGS.S15_Huge.Huge

@[expose] public section

namespace DGS

theorem main_of_external (hTV : TaoVuStatement) (hOT : ORourkeTouriStatement) : MainStatement :=
  main_of_components hOT (thm_largedegrees hTV) (thm_smooth hTV hOT) (thm_moderate hTV) (thm_huge hTV)

end DGS
