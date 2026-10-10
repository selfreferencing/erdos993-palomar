module

public import F4Heavy.Finite.Arithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite
open Fraction

-- Source assertions.json[1120]: H_r6_endpoint_D norm 2
theorem cert_1120_H_r6_endpoint_D_norm_2 :
    (positive (normMargin
    [⟨254697256236310699529890756515, 2151296⟩, ⟨-141709163748384955234903702431, 614656⟩, ⟨-268888043398565979867597087, 1372⟩, ⟨404818927206091691477638481, 1568⟩, ⟨12333706912964203318844423, 56⟩, ⟨643156676497528212264501, 16⟩]
    ⟨1, 14⟩)) = true := by
  decide +kernel

-- Source assertions.json[1121]: H_r6_endpoint_D norm 3
theorem cert_1121_H_r6_endpoint_D_norm_3 :
    (positive (normMargin
    [⟨153245272773877772899408352745, 1075648⟩, ⟨-89183392994504378269917204573, 307328⟩, ⟨-85824137390003166686155788, 343⟩, ⟨286864326591939975599299651, 784⟩, ⟨9363688344261410159798221, 28⟩, ⟨532213774573284882211839, 8⟩]
    ⟨1, 14⟩)) = true := by
  decide +kernel

-- Source assertions.json[1122]: H_r6_endpoint_D norm 4
theorem cert_1122_H_r6_endpoint_D_norm_4 :
    (positive (normMargin
    [⟨4259619487251678986225935815, 33614⟩, ⟨-3687775882382115007216581651, 9604⟩, ⟨-90847812118791148810360032, 343⟩, ⟨26876914484233361937822682, 49⟩, ⟨3524437327409622652316824, 7⟩, ⟨108762116571217018917444, 1⟩]
    ⟨1, 14⟩)) = true := by
  decide +kernel

end F4Heavy.Finite
