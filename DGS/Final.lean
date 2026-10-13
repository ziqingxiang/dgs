module

public import DGS.MainProof
public import DGS.Ext.TaoVu.TaoVu
public import DGS.Ext.ORourkeTouri.ORourkeTouri

@[expose] public section

namespace DGS

theorem main : MainStatement :=
  main_of_external ext_tao_vu ext_orourke_touri

end DGS
