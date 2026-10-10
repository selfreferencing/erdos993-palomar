module

public import F4Heavy.Finite.Arithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite
open Fraction

-- Source assertions.json[200]: exact square division
theorem cert_0200_exact_square_division :
    (eq (add ⟨21346366265379139432191348324705, 524288⟩ (mul ⟨1, 4⟩ ⟨-21346366265379139432191348324705, 131072⟩)) zero) = true := by
  decide +kernel

-- Source assertions.json[201]: exact square division
theorem cert_0201_exact_square_division :
    (eq (add ⟨-21346366265379139432191348324705, 131072⟩ (mul ⟨1, 4⟩ ⟨21346366265379139432191348324705, 32768⟩)) zero) = true := by
  decide +kernel

-- Source assertions.json[202]: D_r6_endpoint_R projective square existence 0
theorem cert_0202_D_r6_endpoint_R_projective_square_existence_0 :
    (squareExists
    [⟨475715275739165168977260869496165, 1048576⟩, ⟨110251269170317079700700168827867, 262144⟩, ⟨-142142073543287542592855184516531, 32768⟩, ⟨-9795473390064009089296579644717, 4096⟩, ⟨5321288328754731660318942862899, 256⟩, ⟨64777115570228779686663483897, 2⟩, ⟨13480698648273262711616898750, 1⟩]
    [⟨21346366265379139432191348324705, 32768⟩, ⟨61100304472899650847107667154923, 4096⟩, ⟨10114097260366490170423016972307, 256⟩, ⟨78257814218502042398280382647, 2⟩, ⟨13480698648273262711616898750, 1⟩] ⟨1, 4⟩) = true := by
  decide +kernel

-- Source assertions.json[203]: D_r6_endpoint_R square quotient coefficient 0,0
theorem cert_0203_D_r6_endpoint_R_square_quotient_coefficient_0_0 :
    (positive ⟨21346366265379139432191348324705, 32768⟩) = true := by
  decide +kernel

-- Source assertions.json[204]: D_r6_endpoint_R square quotient coefficient 0,1
theorem cert_0204_D_r6_endpoint_R_square_quotient_coefficient_0_1 :
    (positive ⟨61100304472899650847107667154923, 4096⟩) = true := by
  decide +kernel

-- Source assertions.json[205]: D_r6_endpoint_R square quotient coefficient 0,2
theorem cert_0205_D_r6_endpoint_R_square_quotient_coefficient_0_2 :
    (positive ⟨10114097260366490170423016972307, 256⟩) = true := by
  decide +kernel

-- Source assertions.json[206]: D_r6_endpoint_R square quotient coefficient 0,3
theorem cert_0206_D_r6_endpoint_R_square_quotient_coefficient_0_3 :
    (positive ⟨78257814218502042398280382647, 2⟩) = true := by
  decide +kernel

-- Source assertions.json[207]: D_r6_endpoint_R square quotient coefficient 0,4
theorem cert_0207_D_r6_endpoint_R_square_quotient_coefficient_0_4 :
    (positive ⟨13480698648273262711616898750, 1⟩) = true := by
  decide +kernel

-- Source assertions.json[208]: D_r6_endpoint_R square discriminant and closed endpoint 0
theorem cert_0208_D_r6_endpoint_R_square_discriminant_and_closed_endpoint_0 :
    (positive (squareDiscriminant [⟨21346366265379139432191348324705, 32768⟩, ⟨61100304472899650847107667154923, 4096⟩, ⟨10114097260366490170423016972307, 256⟩, ⟨78257814218502042398280382647, 2⟩, ⟨13480698648273262711616898750, 1⟩] ⟨192129029774320962076956533176875, 524288⟩ ⟨-48764483659764965958965106493005, 262144⟩) && positive ⟨13480698648273262711616898750, 1⟩) = true := by
  decide +kernel

-- Source assertions.json[209]: D_r6_endpoint_R positive parent control 1,0
theorem cert_0209_D_r6_endpoint_R_positive_parent_control_1_0 :
    (positive ⟨2480956704607556443386510946215, 4096⟩) = true := by
  decide +kernel

-- Source assertions.json[210]: D_r6_endpoint_R positive parent control 1,1
theorem cert_0210_D_r6_endpoint_R_positive_parent_control_1_1 :
    (positive ⟨3803788899119425448934000803874493, 12845056⟩) = true := by
  decide +kernel

-- Source assertions.json[211]: D_r6_endpoint_R positive parent control 1,2
theorem cert_0211_D_r6_endpoint_R_positive_parent_control_1_2 :
    (positive ⟨4401623013202485197718663083369, 1003520⟩) = true := by
  decide +kernel

-- Source assertions.json[212]: D_r6_endpoint_R positive parent control 1,3
theorem cert_0212_D_r6_endpoint_R_positive_parent_control_1_3 :
    (positive ⟨406274204695361085544507934107221, 2007040⟩) = true := by
  decide +kernel

-- Source assertions.json[213]: D_r6_endpoint_R positive parent control 1,4
theorem cert_0213_D_r6_endpoint_R_positive_parent_control_1_4 :
    (positive ⟨51956319540483653949218301457121, 31360⟩) = true := by
  decide +kernel

-- Source assertions.json[214]: D_r6_endpoint_R positive parent control 1,5
theorem cert_0214_D_r6_endpoint_R_positive_parent_control_1_5 :
    (positive ⟨1076631910413139447472809690601, 196⟩) = true := by
  decide +kernel

-- Source assertions.json[215]: D_r6_endpoint_R positive parent control 1,6
theorem cert_0215_D_r6_endpoint_R_positive_parent_control_1_6 :
    (positive ⟨648084812577402167649823211100, 49⟩) = true := by
  decide +kernel

-- Source assertions.json[216]: D_r6_endpoint_R positive parent control 2,0
theorem cert_0216_D_r6_endpoint_R_positive_parent_control_2_0 :
    (positive ⟨910165140988012056984480564532704805, 1213857792⟩) = true := by
  decide +kernel

-- Source assertions.json[217]: D_r6_endpoint_R positive parent control 2,1
theorem cert_0217_D_r6_endpoint_R_positive_parent_control_2_1 :
    (positive ⟨267773917636228287574170487722081479, 520224768⟩) = true := by
  decide +kernel

-- Source assertions.json[218]: D_r6_endpoint_R positive parent control 2,2
theorem cert_0218_D_r6_endpoint_R_positive_parent_control_2_2 :
    (positive ⟨334845724252464560451259361950073921, 1137991680⟩) = true := by
  decide +kernel

-- Source assertions.json[219]: D_r6_endpoint_R positive parent control 2,3
theorem cert_0219_D_r6_endpoint_R_positive_parent_control_2_3 :
    (positive ⟨511820074941227967502024259484107, 967680⟩) = true := by
  decide +kernel

-- Source assertions.json[220]: D_r6_endpoint_R positive parent control 2,4
theorem cert_0220_D_r6_endpoint_R_positive_parent_control_2_4 :
    (positive ⟨8647531944001191336373740262416383, 4445280⟩) = true := by
  decide +kernel

-- Source assertions.json[221]: D_r6_endpoint_R positive parent control 2,5
theorem cert_0221_D_r6_endpoint_R_positive_parent_control_2_5 :
    (positive ⟨312428347057406584988386457152871, 55566⟩) = true := by
  decide +kernel

-- Source assertions.json[222]: D_r6_endpoint_R positive parent control 2,6
theorem cert_0222_D_r6_endpoint_R_positive_parent_control_2_6 :
    (positive ⟨120637030318937291676052444746800, 9261⟩) = true := by
  decide +kernel

-- Source assertions.json[223]: D_r6_endpoint_R positive parent control 3,0
theorem cert_0223_D_r6_endpoint_R_positive_parent_control_3_0 :
    (positive ⟨1629980615796872659884271553934845, 1843968⟩) = true := by
  decide +kernel

-- Source assertions.json[224]: D_r6_endpoint_R positive parent control 3,1
theorem cert_0224_D_r6_endpoint_R_positive_parent_control_3_1 :
    (positive ⟨341069907855732163724661938974745449, 472055808⟩) = true := by
  decide +kernel

-- Source assertions.json[225]: D_r6_endpoint_R positive parent control 3,2
theorem cert_0225_D_r6_endpoint_R_positive_parent_control_3_2 :
    (positive ⟨127317850251751663277500379455214777, 221276160⟩) = true := by
  decide +kernel

-- Source assertions.json[226]: D_r6_endpoint_R positive parent control 3,3
theorem cert_0226_D_r6_endpoint_R_positive_parent_control_3_3 :
    (positive ⟨47199875022504408947179840937056771, 55319040⟩) = true := by
  decide +kernel

-- Source assertions.json[227]: D_r6_endpoint_R positive parent control 3,4
theorem cert_0227_D_r6_endpoint_R_positive_parent_control_3_4 :
    (positive ⟨831089744456992013484134119938709, 370440⟩) = true := by
  decide +kernel

-- Source assertions.json[228]: D_r6_endpoint_R positive parent control 3,5
theorem cert_0228_D_r6_endpoint_R_positive_parent_control_3_5 :
    (positive ⟨374627667366156891877401282069212, 64827⟩) = true := by
  decide +kernel

-- Source assertions.json[229]: D_r6_endpoint_R positive parent control 3,6
theorem cert_0229_D_r6_endpoint_R_positive_parent_control_3_6 :
    (positive ⟨39743757446838240221684506686400, 3087⟩) = true := by
  decide +kernel

-- Source assertions.json[230]: D_r6_endpoint_R positive parent control 4,0
theorem cert_0230_D_r6_endpoint_R_positive_parent_control_4_0 :
    (positive ⟨29922572025140831647571077085026974535, 29739515904⟩) = true := by
  decide +kernel

-- Source assertions.json[231]: D_r6_endpoint_R positive parent control 4,1
theorem cert_0231_D_r6_endpoint_R_positive_parent_control_4_1 :
    (positive ⟨2189364110618443339221175315461642859, 2389782528⟩) = true := by
  decide +kernel

-- Source assertions.json[232]: D_r6_endpoint_R positive parent control 4,2
theorem cert_0232_D_r6_endpoint_R_positive_parent_control_4_2 :
    (positive ⟨2202218281620636695424437988171157883, 2613824640⟩) = true := by
  decide +kernel

-- Source assertions.json[233]: D_r6_endpoint_R positive parent control 4,3
theorem cert_0233_D_r6_endpoint_R_positive_parent_control_4_3 :
    (positive ⟨63594462125996595599360822243828557, 54454680⟩) = true := by
  decide +kernel

-- Source assertions.json[234]: D_r6_endpoint_R positive parent control 4,4
theorem cert_0234_D_r6_endpoint_R_positive_parent_control_4_4 :
    (positive ⟨51898500853856300315066028244058743, 20420505⟩) = true := by
  decide +kernel

-- Source assertions.json[235]: D_r6_endpoint_R positive parent control 4,5
theorem cert_0235_D_r6_endpoint_R_positive_parent_control_4_5 :
    (positive ⟨24299865917619849374644641029979856, 4084101⟩) = true := by
  decide +kernel

-- Source assertions.json[236]: D_r6_endpoint_R positive parent control 4,6
theorem cert_0236_D_r6_endpoint_R_positive_parent_control_4_6 :
    (positive ⟨17368054889648155576315787875187200, 1361367⟩) = true := by
  decide +kernel

-- Source assertions.json[237]: D_r6_endpoint_R positive parent control 5,0
theorem cert_0237_D_r6_endpoint_R_positive_parent_control_5_0 :
    (positive ⟨391537279330039505468079276296576516515, 351298031616⟩) = true := by
  decide +kernel

-- Source assertions.json[238]: D_r6_endpoint_R positive parent control 5,1
theorem cert_0238_D_r6_endpoint_R_positive_parent_control_5_1 :
    (positive ⟨287772984438907673416803137912890237961, 263473523712⟩) = true := by
  decide +kernel

-- Source assertions.json[239]: D_r6_endpoint_R positive parent control 5,2
theorem cert_0239_D_r6_endpoint_R_positive_parent_control_5_2 :
    (positive ⟨44881207645484960596986817658600040151, 41167738080⟩) = true := by
  decide +kernel

end F4Heavy.Finite
