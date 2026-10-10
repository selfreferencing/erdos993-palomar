module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0517Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0518Part0000
public import Erdos993Lean.Analytic.V213.LowMeanIntegerExpr
public import Erdos993Lean.Ceiling.Prefix
public import Erdos993Lean.Ceiling.Statement


/-! Direct-fiber core witnesses with explicit complete integer windows. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanRankExpr0518_143_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (43, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-17, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-221, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (84993, 10000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (289, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (373677, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-373677, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (13225203, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (30091229149, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e24 43
  let e26 : LowMeanIntegerExpr := .mul (3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e26
  let e28 : LowMeanIntegerExpr := .add (22990786982128814558316286409248914062226304501375883247211138789827523761, 2521930536465588616577172514610490347856298061722673548020128000171200000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000)
  let e30 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (344, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (98, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (197985, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-197985, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1864133, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (817, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-817, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4056094, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4056094, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4056094, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (16451898536836, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (4112974634209, 4337457500000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-4112974634209, 4337457500000) e48
  let e50 : LowMeanIntegerExpr := .add (-337479446948262886914431255143826306781059591072020484444353272049438322282446537198038049949568915429448673129171274699510633, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (337479446948262886914431255143826306781059591072020484444353272049438322282446537198038049949568915429448673129171274699510633, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e50
  e51

noncomputable def lowMeanRankExpr0518_143_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0518_144_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (43, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-17, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-221, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (84993, 10000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (289, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (373677, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-373677, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (13225203, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (30091229149, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e24 43
  let e26 : LowMeanIntegerExpr := .mul (3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e26
  let e28 : LowMeanIntegerExpr := .add (22990786982128814558316286409248914062226304501375883247211138789827523761, 2521930536465588616577172514610490347856298061722673548020128000171200000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000)
  let e30 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (344, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (99, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (200048, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-200048, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1890952, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (817, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-817, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4115921, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4115921, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4115921, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (16940805678241, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (16940805678241, 17349830000000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-16940805678241, 17349830000000) e48
  let e50 : LowMeanIntegerExpr := .add (-347628977618221953629718130740325620233278717304275217578558075452510206354091920604077985025555851336460103058813514519257033, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (347628977618221953629718130740325620233278717304275217578558075452510206354091920604077985025555851336460103058813514519257033, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e50
  e51

noncomputable def lowMeanRankExpr0518_144_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0518_145_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (43, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-17, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-221, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (84993, 10000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (289, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (373677, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-373677, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (13225203, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (30091229149, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e24 43
  let e26 : LowMeanIntegerExpr := .mul (3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e26
  let e28 : LowMeanIntegerExpr := .add (22990786982128814558316286409248914062226304501375883247211138789827523761, 2521930536465588616577172514610490347856298061722673548020128000171200000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000)
  let e30 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (344, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (100, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (202111, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-202111, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1917771, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (817, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-817, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4175748, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4175748, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4175748, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (17436871359504, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (1089804459969, 1084364375000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-1089804459969, 1084364375000) e48
  let e50 : LowMeanIntegerExpr := .add (-357927116916870919001425844503742582374568021128004539028917479837884639211649793978144936986800846709713034703369568442794473, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (357927116916870919001425844503742582374568021128004539028917479837884639211649793978144936986800846709713034703369568442794473, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e50
  e51

noncomputable def lowMeanRankExpr0518_145_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0518_146_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (43, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-17, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-221, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (84993, 10000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (289, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (373677, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-373677, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (13225203, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (30091229149, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e24 43
  let e26 : LowMeanIntegerExpr := .mul (3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e26
  let e28 : LowMeanIntegerExpr := .add (22990786982128814558316286409248914062226304501375883247211138789827523761, 2521930536465588616577172514610490347856298061722673548020128000171200000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000)
  let e30 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (344, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (101, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (204174, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-204174, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1944590, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (817, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-817, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4235575, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4235575, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4235575, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (17940095580625, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (28704152929, 27759728000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-28704152929, 27759728000) e48
  let e50 : LowMeanIntegerExpr := .add (-368373864844209783029554396434077193204927502543208448795431485205561620855120157320238905833303901549207468062839436470122953, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (368373864844209783029554396434077193204927502543208448795431485205561620855120157320238905833303901549207468062839436470122953, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e50
  e51

noncomputable def lowMeanRankExpr0518_146_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0518_147_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (43, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-17, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-221, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (84993, 10000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (289, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (373677, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-373677, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (13225203, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (30091229149, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e24 43
  let e26 : LowMeanIntegerExpr := .mul (3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e26
  let e28 : LowMeanIntegerExpr := .add (22990786982128814558316286409248914062226304501375883247211138789827523761, 2521930536465588616577172514610490347856298061722673548020128000171200000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000)
  let e30 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (344, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (102, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (206237, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-206237, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1971409, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (817, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-817, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4295402, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4295402, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4295402, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (18450478341604, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (4612619585401, 4337457500000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-4612619585401, 4337457500000) e48
  let e50 : LowMeanIntegerExpr := .add (-378969221400238545714103786531329452724357161549886946878100091555541151284503010630359891565065015854943403137223118601242473, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (378969221400238545714103786531329452724357161549886946878100091555541151284503010630359891565065015854943403137223118601242473, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e50
  e51

noncomputable def lowMeanRankExpr0518_147_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0518_148_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (43, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-17, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-221, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (84993, 10000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (289, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (373677, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-373677, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (13225203, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (30091229149, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e24 43
  let e26 : LowMeanIntegerExpr := .mul (3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e26
  let e28 : LowMeanIntegerExpr := .add (22990786982128814558316286409248914062226304501375883247211138789827523761, 2521930536465588616577172514610490347856298061722673548020128000171200000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000)
  let e30 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (344, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (103, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (208300, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-208300, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-1998228, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (817, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-817, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4355229, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4355229, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4355229, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (18968019642441, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (18968019642441, 17349830000000) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-18968019642441, 17349830000000) e48
  let e50 : LowMeanIntegerExpr := .add (-389713186584957207055074014795499360932856998148040033276923298887823230499798353908507894182084189626920839926520614836153033, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (389713186584957207055074014795499360932856998148040033276923298887823230499798353908507894182084189626920839926520614836153033, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e50
  e51

noncomputable def lowMeanRankExpr0518_148_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanRankExpr0518_149_a : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (99137, 10000000)
  let e1 : LowMeanIntegerExpr := .atom (26, 78125)
  let e2 : LowMeanIntegerExpr := .atom (43, 1)
  let e3 : LowMeanIntegerExpr := .atom (189, 4)
  let e4 : LowMeanIntegerExpr := .neg (-189, 4) e3
  let e5 : LowMeanIntegerExpr := .add (-17, 4) e2 e4
  let e6 : LowMeanIntegerExpr := .mul (-221, 156250) e1 e5
  let e7 : LowMeanIntegerExpr := .add (84993, 10000000) e0 e6
  let e8 : LowMeanIntegerExpr := .atom (1293, 100000000)
  let e9 : LowMeanIntegerExpr := .pow (289, 16) e5 2
  let e10 : LowMeanIntegerExpr := .mul (373677, 1600000000) e8 e9
  let e11 : LowMeanIntegerExpr := .neg (-373677, 1600000000) e10
  let e12 : LowMeanIntegerExpr := .add (13225203, 1600000000) e7 e11
  let e13 : LowMeanIntegerExpr := .atom (-4189, 5000000)
  let e14 : LowMeanIntegerExpr := .pow (17547721, 25000000000000) e13 2
  let e15 : LowMeanIntegerExpr := .atom (4, 1)
  let e16 : LowMeanIntegerExpr := .atom (2063, 10000000)
  let e17 : LowMeanIntegerExpr := .mul (2063, 2500000) e15 e16
  let e18 : LowMeanIntegerExpr := .div (17547721, 20630000000) e14 e17
  let e19 : LowMeanIntegerExpr := .add (30091229149, 3300800000000) e12 e18
  let e20 : LowMeanIntegerExpr := .atom (328000, 1)
  let e21 : LowMeanIntegerExpr := .atom (1, 1)
  let e22 : LowMeanIntegerExpr := .atom (19, 29)
  let e23 : LowMeanIntegerExpr := .neg (-19, 29) e22
  let e24 : LowMeanIntegerExpr := .add (10, 29) e21 e23
  let e25 : LowMeanIntegerExpr := .pow (10000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e24 43
  let e26 : LowMeanIntegerExpr := .mul (3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e20 e25
  let e27 : LowMeanIntegerExpr := .neg (-3280000000000000000000000000000000000000000000000, 764036153800772120872870975100124317697618171874295185415695589) e26
  let e28 : LowMeanIntegerExpr := .add (22990786982128814558316286409248914062226304501375883247211138789827523761, 2521930536465588616577172514610490347856298061722673548020128000171200000000) e19 e27
  let e29 : LowMeanIntegerExpr := .atom (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000)
  let e30 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e28 e29
  let e31 : LowMeanIntegerExpr := .atom (0, 1)
  let e32 : LowMeanIntegerExpr := .add (8367231456911041002709231048707874399339203998314242771245885900348627236018694083738139316163518580787732862390265944622447961, 743043143449493282104190834588243445350887957372941580773004911512743929562449840135084426290297331207508574569070518955200000000) e30 e31
  let e33 : LowMeanIntegerExpr := .atom (8, 13)
  let e34 : LowMeanIntegerExpr := .mul (344, 13) e2 e33
  let e35 : LowMeanIntegerExpr := .atom (104, 1)
  let e36 : LowMeanIntegerExpr := .atom (2, 1)
  let e37 : LowMeanIntegerExpr := .mul (2063, 5000000) e36 e16
  let e38 : LowMeanIntegerExpr := .div (-4189, 2063) e13 e37
  let e39 : LowMeanIntegerExpr := .add (210363, 2063) e35 e38
  let e40 : LowMeanIntegerExpr := .neg (-210363, 2063) e39
  let e41 : LowMeanIntegerExpr := .add (-2025047, 26819) e34 e40
  let e42 : LowMeanIntegerExpr := .mul (817, 29) e2 e22
  let e43 : LowMeanIntegerExpr := .neg (-817, 29) e42
  let e44 : LowMeanIntegerExpr := .add (4415056, 59827) e39 e43
  let e45 : LowMeanIntegerExpr := .maximum (4415056, 59827) e41 e44
  let e46 : LowMeanIntegerExpr := .maximum (4415056, 59827) e31 e45
  let e47 : LowMeanIntegerExpr := .pow (19492719483136, 3579269929) e46 2
  let e48 : LowMeanIntegerExpr := .mul (152286870962, 135545546875) e16 e47
  let e49 : LowMeanIntegerExpr := .neg (-152286870962, 135545546875) e48
  let e50 : LowMeanIntegerExpr := .add (-400605760398365767052465081226586917830427012337667707991901107202407858501006187154682913684361422865139778430731925174854633, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e32 e49
  let e51 : LowMeanIntegerExpr := .neg (400605760398365767052465081226586917830427012337667707991901107202407858501006187154682913684361422865139778430731925174854633, 360176026878086903589040637221640060761458050108066689662144891668804619274091051931693856660347712655118068138182510400000000) e50
  e51

noncomputable def lowMeanRankExpr0518_149_b : LowMeanIntegerExpr :=
  let e0 : LowMeanIntegerExpr := .atom (0, 1)
  e0

noncomputable def lowMeanFiber0518 : LowMeanFiberInput :=
{ record := 518, certificate := 26, M := 43, zeta := (25272612939121885367859160609927755827009252204377769253131, 11785307052760404213423474919652927412165962604668812840000000), lo := -45, hi := 104,
  gL := (169255528179462832128000000000000000000000000, 61040881526285814362156628321386486455989674569), gR := (50705217988680786849778712189530656427456080236800000000000000, 764036153800772120872870975100124317697618171874295185415695589), core := [35, 36, 37],
  gLExpr := lowMeanFiberExpr0518_0, gRExpr := lowMeanFiberExpr0518_1,
  leftSide := lowMeanFiberExpr0518_2, rightSide := lowMeanFiberExpr0518_3,
  leftTail := lowMeanFiberExpr0518_4, rightTail := lowMeanFiberExpr0518_5,
  ranks := [{ j := -45, state := 0, first := lowMeanRankExpr0518_0_a, second := lowMeanRankExpr0518_0_b }, { j := -44, state := 0, first := lowMeanRankExpr0518_1_a, second := lowMeanRankExpr0518_1_b }, { j := -43, state := 0, first := lowMeanRankExpr0518_2_a, second := lowMeanRankExpr0518_2_b }, { j := -42, state := 0, first := lowMeanRankExpr0518_3_a, second := lowMeanRankExpr0518_3_b }, { j := -41, state := 0, first := lowMeanRankExpr0518_4_a, second := lowMeanRankExpr0518_4_b }, { j := -40, state := 0, first := lowMeanRankExpr0518_5_a, second := lowMeanRankExpr0518_5_b }, { j := -39, state := 0, first := lowMeanRankExpr0518_6_a, second := lowMeanRankExpr0518_6_b }, { j := -38, state := 0, first := lowMeanRankExpr0518_7_a, second := lowMeanRankExpr0518_7_b }, { j := -37, state := 0, first := lowMeanRankExpr0518_8_a, second := lowMeanRankExpr0518_8_b }, { j := -36, state := 0, first := lowMeanRankExpr0518_9_a, second := lowMeanRankExpr0518_9_b }, { j := -35, state := 0, first := lowMeanRankExpr0518_10_a, second := lowMeanRankExpr0518_10_b }, { j := -34, state := 0, first := lowMeanRankExpr0518_11_a, second := lowMeanRankExpr0518_11_b }, { j := -33, state := 0, first := lowMeanRankExpr0518_12_a, second := lowMeanRankExpr0518_12_b }, { j := -32, state := 0, first := lowMeanRankExpr0518_13_a, second := lowMeanRankExpr0518_13_b }, { j := -31, state := 0, first := lowMeanRankExpr0518_14_a, second := lowMeanRankExpr0518_14_b }, { j := -30, state := 0, first := lowMeanRankExpr0518_15_a, second := lowMeanRankExpr0518_15_b }, { j := -29, state := 0, first := lowMeanRankExpr0518_16_a, second := lowMeanRankExpr0518_16_b }, { j := -28, state := 0, first := lowMeanRankExpr0518_17_a, second := lowMeanRankExpr0518_17_b }, { j := -27, state := 0, first := lowMeanRankExpr0518_18_a, second := lowMeanRankExpr0518_18_b }, { j := -26, state := 0, first := lowMeanRankExpr0518_19_a, second := lowMeanRankExpr0518_19_b }, { j := -25, state := 0, first := lowMeanRankExpr0518_20_a, second := lowMeanRankExpr0518_20_b }, { j := -24, state := 0, first := lowMeanRankExpr0518_21_a, second := lowMeanRankExpr0518_21_b }, { j := -23, state := 0, first := lowMeanRankExpr0518_22_a, second := lowMeanRankExpr0518_22_b }, { j := -22, state := 0, first := lowMeanRankExpr0518_23_a, second := lowMeanRankExpr0518_23_b }, { j := -21, state := 0, first := lowMeanRankExpr0518_24_a, second := lowMeanRankExpr0518_24_b }, { j := -20, state := 0, first := lowMeanRankExpr0518_25_a, second := lowMeanRankExpr0518_25_b }, { j := -19, state := 0, first := lowMeanRankExpr0518_26_a, second := lowMeanRankExpr0518_26_b }, { j := -18, state := 0, first := lowMeanRankExpr0518_27_a, second := lowMeanRankExpr0518_27_b }, { j := -17, state := 0, first := lowMeanRankExpr0518_28_a, second := lowMeanRankExpr0518_28_b }, { j := -16, state := 0, first := lowMeanRankExpr0518_29_a, second := lowMeanRankExpr0518_29_b }, { j := -15, state := 0, first := lowMeanRankExpr0518_30_a, second := lowMeanRankExpr0518_30_b }, { j := -14, state := 0, first := lowMeanRankExpr0518_31_a, second := lowMeanRankExpr0518_31_b }, { j := -13, state := 0, first := lowMeanRankExpr0518_32_a, second := lowMeanRankExpr0518_32_b }, { j := -12, state := 0, first := lowMeanRankExpr0518_33_a, second := lowMeanRankExpr0518_33_b }, { j := -11, state := 0, first := lowMeanRankExpr0518_34_a, second := lowMeanRankExpr0518_34_b }, { j := -10, state := 0, first := lowMeanRankExpr0518_35_a, second := lowMeanRankExpr0518_35_b }, { j := -9, state := 0, first := lowMeanRankExpr0518_36_a, second := lowMeanRankExpr0518_36_b }, { j := -8, state := 0, first := lowMeanRankExpr0518_37_a, second := lowMeanRankExpr0518_37_b }, { j := -7, state := 0, first := lowMeanRankExpr0518_38_a, second := lowMeanRankExpr0518_38_b }, { j := -6, state := 0, first := lowMeanRankExpr0518_39_a, second := lowMeanRankExpr0518_39_b }, { j := -5, state := 0, first := lowMeanRankExpr0518_40_a, second := lowMeanRankExpr0518_40_b }, { j := -4, state := 0, first := lowMeanRankExpr0518_41_a, second := lowMeanRankExpr0518_41_b }, { j := -3, state := 0, first := lowMeanRankExpr0518_42_a, second := lowMeanRankExpr0518_42_b }, { j := -2, state := 0, first := lowMeanRankExpr0518_43_a, second := lowMeanRankExpr0518_43_b }, { j := -1, state := 0, first := lowMeanRankExpr0518_44_a, second := lowMeanRankExpr0518_44_b }, { j := 0, state := 0, first := lowMeanRankExpr0518_45_a, second := lowMeanRankExpr0518_45_b }, { j := 1, state := 0, first := lowMeanRankExpr0518_46_a, second := lowMeanRankExpr0518_46_b }, { j := 2, state := 0, first := lowMeanRankExpr0518_47_a, second := lowMeanRankExpr0518_47_b }, { j := 3, state := 0, first := lowMeanRankExpr0518_48_a, second := lowMeanRankExpr0518_48_b }, { j := 4, state := 0, first := lowMeanRankExpr0518_49_a, second := lowMeanRankExpr0518_49_b }, { j := 5, state := 0, first := lowMeanRankExpr0518_50_a, second := lowMeanRankExpr0518_50_b }, { j := 6, state := 0, first := lowMeanRankExpr0518_51_a, second := lowMeanRankExpr0518_51_b }, { j := 7, state := 0, first := lowMeanRankExpr0518_52_a, second := lowMeanRankExpr0518_52_b }, { j := 8, state := 0, first := lowMeanRankExpr0518_53_a, second := lowMeanRankExpr0518_53_b }, { j := 9, state := 0, first := lowMeanRankExpr0518_54_a, second := lowMeanRankExpr0518_54_b }, { j := 10, state := 0, first := lowMeanRankExpr0518_55_a, second := lowMeanRankExpr0518_55_b }, { j := 11, state := 0, first := lowMeanRankExpr0518_56_a, second := lowMeanRankExpr0518_56_b }, { j := 12, state := 0, first := lowMeanRankExpr0518_57_a, second := lowMeanRankExpr0518_57_b }, { j := 13, state := 0, first := lowMeanRankExpr0518_58_a, second := lowMeanRankExpr0518_58_b }, { j := 14, state := 0, first := lowMeanRankExpr0518_59_a, second := lowMeanRankExpr0518_59_b }, { j := 15, state := 0, first := lowMeanRankExpr0518_60_a, second := lowMeanRankExpr0518_60_b }, { j := 16, state := 0, first := lowMeanRankExpr0518_61_a, second := lowMeanRankExpr0518_61_b }, { j := 17, state := 0, first := lowMeanRankExpr0518_62_a, second := lowMeanRankExpr0518_62_b }, { j := 18, state := 0, first := lowMeanRankExpr0518_63_a, second := lowMeanRankExpr0518_63_b }, { j := 19, state := 0, first := lowMeanRankExpr0518_64_a, second := lowMeanRankExpr0518_64_b }, { j := 20, state := 0, first := lowMeanRankExpr0518_65_a, second := lowMeanRankExpr0518_65_b }, { j := 21, state := 0, first := lowMeanRankExpr0518_66_a, second := lowMeanRankExpr0518_66_b }, { j := 22, state := 1, first := lowMeanRankExpr0518_67_a, second := lowMeanRankExpr0518_67_b }, { j := 23, state := 1, first := lowMeanRankExpr0518_68_a, second := lowMeanRankExpr0518_68_b }, { j := 24, state := 1, first := lowMeanRankExpr0518_69_a, second := lowMeanRankExpr0518_69_b }, { j := 25, state := 1, first := lowMeanRankExpr0518_70_a, second := lowMeanRankExpr0518_70_b }, { j := 26, state := 1, first := lowMeanRankExpr0518_71_a, second := lowMeanRankExpr0518_71_b }, { j := 27, state := 1, first := lowMeanRankExpr0518_72_a, second := lowMeanRankExpr0518_72_b }, { j := 28, state := 1, first := lowMeanRankExpr0518_73_a, second := lowMeanRankExpr0518_73_b }, { j := 29, state := 1, first := lowMeanRankExpr0518_74_a, second := lowMeanRankExpr0518_74_b }, { j := 30, state := 1, first := lowMeanRankExpr0518_75_a, second := lowMeanRankExpr0518_75_b }, { j := 31, state := 1, first := lowMeanRankExpr0518_76_a, second := lowMeanRankExpr0518_76_b }, { j := 32, state := 1, first := lowMeanRankExpr0518_77_a, second := lowMeanRankExpr0518_77_b }, { j := 33, state := 1, first := lowMeanRankExpr0518_78_a, second := lowMeanRankExpr0518_78_b }, { j := 34, state := 1, first := lowMeanRankExpr0518_79_a, second := lowMeanRankExpr0518_79_b }, { j := 35, state := 2, first := lowMeanRankExpr0518_80_a, second := lowMeanRankExpr0518_80_b }, { j := 36, state := 2, first := lowMeanRankExpr0518_81_a, second := lowMeanRankExpr0518_81_b }, { j := 37, state := 2, first := lowMeanRankExpr0518_82_a, second := lowMeanRankExpr0518_82_b }, { j := 38, state := 0, first := lowMeanRankExpr0518_83_a, second := lowMeanRankExpr0518_83_b }, { j := 39, state := 0, first := lowMeanRankExpr0518_84_a, second := lowMeanRankExpr0518_84_b }, { j := 40, state := 0, first := lowMeanRankExpr0518_85_a, second := lowMeanRankExpr0518_85_b }, { j := 41, state := 0, first := lowMeanRankExpr0518_86_a, second := lowMeanRankExpr0518_86_b }, { j := 42, state := 0, first := lowMeanRankExpr0518_87_a, second := lowMeanRankExpr0518_87_b }, { j := 43, state := 0, first := lowMeanRankExpr0518_88_a, second := lowMeanRankExpr0518_88_b }, { j := 44, state := 0, first := lowMeanRankExpr0518_89_a, second := lowMeanRankExpr0518_89_b }, { j := 45, state := 0, first := lowMeanRankExpr0518_90_a, second := lowMeanRankExpr0518_90_b }, { j := 46, state := 0, first := lowMeanRankExpr0518_91_a, second := lowMeanRankExpr0518_91_b }, { j := 47, state := 0, first := lowMeanRankExpr0518_92_a, second := lowMeanRankExpr0518_92_b }, { j := 48, state := 0, first := lowMeanRankExpr0518_93_a, second := lowMeanRankExpr0518_93_b }, { j := 49, state := 0, first := lowMeanRankExpr0518_94_a, second := lowMeanRankExpr0518_94_b }, { j := 50, state := 0, first := lowMeanRankExpr0518_95_a, second := lowMeanRankExpr0518_95_b }, { j := 51, state := 0, first := lowMeanRankExpr0518_96_a, second := lowMeanRankExpr0518_96_b }, { j := 52, state := 0, first := lowMeanRankExpr0518_97_a, second := lowMeanRankExpr0518_97_b }, { j := 53, state := 0, first := lowMeanRankExpr0518_98_a, second := lowMeanRankExpr0518_98_b }, { j := 54, state := 0, first := lowMeanRankExpr0518_99_a, second := lowMeanRankExpr0518_99_b }, { j := 55, state := 0, first := lowMeanRankExpr0518_100_a, second := lowMeanRankExpr0518_100_b }, { j := 56, state := 0, first := lowMeanRankExpr0518_101_a, second := lowMeanRankExpr0518_101_b }, { j := 57, state := 0, first := lowMeanRankExpr0518_102_a, second := lowMeanRankExpr0518_102_b }, { j := 58, state := 0, first := lowMeanRankExpr0518_103_a, second := lowMeanRankExpr0518_103_b }, { j := 59, state := 0, first := lowMeanRankExpr0518_104_a, second := lowMeanRankExpr0518_104_b }, { j := 60, state := 0, first := lowMeanRankExpr0518_105_a, second := lowMeanRankExpr0518_105_b }, { j := 61, state := 0, first := lowMeanRankExpr0518_106_a, second := lowMeanRankExpr0518_106_b }, { j := 62, state := 0, first := lowMeanRankExpr0518_107_a, second := lowMeanRankExpr0518_107_b }, { j := 63, state := 0, first := lowMeanRankExpr0518_108_a, second := lowMeanRankExpr0518_108_b }, { j := 64, state := 0, first := lowMeanRankExpr0518_109_a, second := lowMeanRankExpr0518_109_b }, { j := 65, state := 0, first := lowMeanRankExpr0518_110_a, second := lowMeanRankExpr0518_110_b }, { j := 66, state := 0, first := lowMeanRankExpr0518_111_a, second := lowMeanRankExpr0518_111_b }, { j := 67, state := 0, first := lowMeanRankExpr0518_112_a, second := lowMeanRankExpr0518_112_b }, { j := 68, state := 0, first := lowMeanRankExpr0518_113_a, second := lowMeanRankExpr0518_113_b }, { j := 69, state := 0, first := lowMeanRankExpr0518_114_a, second := lowMeanRankExpr0518_114_b }, { j := 70, state := 0, first := lowMeanRankExpr0518_115_a, second := lowMeanRankExpr0518_115_b }, { j := 71, state := 0, first := lowMeanRankExpr0518_116_a, second := lowMeanRankExpr0518_116_b }, { j := 72, state := 0, first := lowMeanRankExpr0518_117_a, second := lowMeanRankExpr0518_117_b }, { j := 73, state := 0, first := lowMeanRankExpr0518_118_a, second := lowMeanRankExpr0518_118_b }, { j := 74, state := 0, first := lowMeanRankExpr0518_119_a, second := lowMeanRankExpr0518_119_b }, { j := 75, state := 0, first := lowMeanRankExpr0518_120_a, second := lowMeanRankExpr0518_120_b }, { j := 76, state := 0, first := lowMeanRankExpr0518_121_a, second := lowMeanRankExpr0518_121_b }, { j := 77, state := 0, first := lowMeanRankExpr0518_122_a, second := lowMeanRankExpr0518_122_b }, { j := 78, state := 0, first := lowMeanRankExpr0518_123_a, second := lowMeanRankExpr0518_123_b }, { j := 79, state := 0, first := lowMeanRankExpr0518_124_a, second := lowMeanRankExpr0518_124_b }, { j := 80, state := 0, first := lowMeanRankExpr0518_125_a, second := lowMeanRankExpr0518_125_b }, { j := 81, state := 0, first := lowMeanRankExpr0518_126_a, second := lowMeanRankExpr0518_126_b }, { j := 82, state := 0, first := lowMeanRankExpr0518_127_a, second := lowMeanRankExpr0518_127_b }, { j := 83, state := 0, first := lowMeanRankExpr0518_128_a, second := lowMeanRankExpr0518_128_b }, { j := 84, state := 0, first := lowMeanRankExpr0518_129_a, second := lowMeanRankExpr0518_129_b }, { j := 85, state := 0, first := lowMeanRankExpr0518_130_a, second := lowMeanRankExpr0518_130_b }, { j := 86, state := 0, first := lowMeanRankExpr0518_131_a, second := lowMeanRankExpr0518_131_b }, { j := 87, state := 0, first := lowMeanRankExpr0518_132_a, second := lowMeanRankExpr0518_132_b }, { j := 88, state := 0, first := lowMeanRankExpr0518_133_a, second := lowMeanRankExpr0518_133_b }, { j := 89, state := 0, first := lowMeanRankExpr0518_134_a, second := lowMeanRankExpr0518_134_b }, { j := 90, state := 0, first := lowMeanRankExpr0518_135_a, second := lowMeanRankExpr0518_135_b }, { j := 91, state := 0, first := lowMeanRankExpr0518_136_a, second := lowMeanRankExpr0518_136_b }, { j := 92, state := 0, first := lowMeanRankExpr0518_137_a, second := lowMeanRankExpr0518_137_b }, { j := 93, state := 0, first := lowMeanRankExpr0518_138_a, second := lowMeanRankExpr0518_138_b }, { j := 94, state := 0, first := lowMeanRankExpr0518_139_a, second := lowMeanRankExpr0518_139_b }, { j := 95, state := 0, first := lowMeanRankExpr0518_140_a, second := lowMeanRankExpr0518_140_b }, { j := 96, state := 0, first := lowMeanRankExpr0518_141_a, second := lowMeanRankExpr0518_141_b }, { j := 97, state := 0, first := lowMeanRankExpr0518_142_a, second := lowMeanRankExpr0518_142_b }, { j := 98, state := 0, first := lowMeanRankExpr0518_143_a, second := lowMeanRankExpr0518_143_b }, { j := 99, state := 0, first := lowMeanRankExpr0518_144_a, second := lowMeanRankExpr0518_144_b }, { j := 100, state := 0, first := lowMeanRankExpr0518_145_a, second := lowMeanRankExpr0518_145_b }, { j := 101, state := 0, first := lowMeanRankExpr0518_146_a, second := lowMeanRankExpr0518_146_b }, { j := 102, state := 0, first := lowMeanRankExpr0518_147_a, second := lowMeanRankExpr0518_147_b }, { j := 103, state := 0, first := lowMeanRankExpr0518_148_a, second := lowMeanRankExpr0518_148_b }, { j := 104, state := 0, first := lowMeanRankExpr0518_149_a, second := lowMeanRankExpr0518_149_b }] }

noncomputable def lowMeanFiberGroup0518 : List LowMeanFiberInput := [lowMeanFiber0518]

end Erdos993Lean.Analytic.V213
