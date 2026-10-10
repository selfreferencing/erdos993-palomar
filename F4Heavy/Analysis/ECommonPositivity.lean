module

public import F4Heavy.Analysis.SquareSemantics
public import F4Heavy.Finite.Certificates.Part006
public import F4Heavy.Finite.Certificates.Part007
public import F4Heavy.Finite.Certificates.Part010
public import F4Heavy.Finite.Certificates.Part011
public import F4Heavy.Finite.Certificates.Part012
public import F4Heavy.Finite.Reconstruction.Function19
public import F4Heavy.Finite.Reconstruction.Function24
public import F4Heavy.Finite.Reconstruction.Function25

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def e_common_E1_r8_H0 : List Fraction :=
  [⟨191040321912593950771330882795253447463925414965, 1⟩, ⟨1401092094746683456049129065329474050797111208604, 1⟩, ⟨3690197758090432892642766668845202729104758468384, 1⟩, ⟨3837456647995348570134076976348323284505142438272, 1⟩, ⟨1586874210614068035898826120510119861855071685632, 1⟩, ⟨538489191793873694574199191823428676838678851584, 1⟩, ⟨438252837496077771257940120658464257521067343872, 1⟩]

theorem e_common_E1_r8_H0_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E1_r8_H0.map fractionValue) x := by
  apply realHorner_positive_of_checks e_common_E1_r8_H0 x (by simp [e_common_E1_r8_H0]) hx
  · intro c hc
    simp only [e_common_E1_r8_H0, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0276_E1_r8_H0_strict_lower_coefficient_0
    · exact cert_0277_E1_r8_H0_strict_lower_coefficient_1
    · exact cert_0278_E1_r8_H0_strict_lower_coefficient_2
    · exact cert_0279_E1_r8_H0_strict_lower_coefficient_3
    · exact cert_0280_E1_r8_H0_strict_lower_coefficient_4
    · exact cert_0281_E1_r8_H0_strict_lower_coefficient_5
    · exact cert_0282_E1_r8_H0_strict_lower_coefficient_6

def e_common_E1_r8_U0 : List Fraction :=
  [⟨455977772040040532446583252806784302423153581243765496423482445512490082040565492225, 1⟩, ⟨3188189273466404789276842731414887066302930529478310775328599552515260656107911813760, 1⟩, ⟨9610532475304638962477462455455295403951408690094509970770232807650111785045041449520, 1⟩, ⟨14248912011463975675948419987602586774778739493868219861053126608808740681648836725760, 1⟩, ⟨7336216103469737051011228397282687497111711594844337128795515455082678846549613281792, 1⟩, ⟨565071459488717399770332873940351295383513175400717807978119335744180297229363810304, 1⟩]

theorem e_common_E1_r8_U0_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E1_r8_U0.map fractionValue) x := by
  apply realHorner_positive_of_checks e_common_E1_r8_U0 x (by simp [e_common_E1_r8_U0]) hx
  · intro c hc
    simp only [e_common_E1_r8_U0, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0286_E1_r8_U0_strict_lower_coefficient_0
    · exact cert_0287_E1_r8_U0_strict_lower_coefficient_1
    · exact cert_0288_E1_r8_U0_strict_lower_coefficient_2
    · exact cert_0289_E1_r8_U0_strict_lower_coefficient_3
    · exact cert_0290_E1_r8_U0_strict_lower_coefficient_4
    · exact cert_0291_E1_r8_U0_strict_lower_coefficient_5

def e_common_E1_r8_U1 : List Fraction :=
  [⟨2719781803739012621556435761235492298880830684936747210075883870912508908703456818846525, 1⟩, ⟨11986970144477384611792472206516518630250620249179182848261590716715582447226581475482285, 1⟩, ⟨16107344462666749861992826482251819333510385907763067233363698893891364289767071575238282, 1⟩, ⟨58142294572078015772258309955570520511966269424076056222553234675760091655627525172072408, 1⟩, ⟨235048960600243321442609330118151473515117919553678009266028117973599001684424193676218144, 1⟩, ⟨321730930780596987370009401092426759667432384903058143840614819487151666125875379877128960, 1⟩, ⟨144871877907936562501910178402079989355229027216838533691477002375351117087411083693629440, 1⟩, ⟨6439380944873294016888258753842355360656754909692411376644824341311007604948599636852736, 1⟩]

theorem e_common_E1_r8_U1_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E1_r8_U1.map fractionValue) x := by
  apply realHorner_positive_of_checks e_common_E1_r8_U1 x (by simp [e_common_E1_r8_U1]) hx
  · intro c hc
    simp only [e_common_E1_r8_U1, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0295_E1_r8_U1_strict_lower_coefficient_0
    · exact cert_0296_E1_r8_U1_strict_lower_coefficient_1
    · exact cert_0297_E1_r8_U1_strict_lower_coefficient_2
    · exact cert_0298_E1_r8_U1_strict_lower_coefficient_3
    · exact cert_0299_E1_r8_U1_strict_lower_coefficient_4
    · exact cert_0300_E1_r8_U1_strict_lower_coefficient_5
    · exact cert_0301_E1_r8_U1_strict_lower_coefficient_6
    · exact cert_0302_E1_r8_U1_strict_lower_coefficient_7

def e_common_E1_r8_U3 : List Fraction :=
  [⟨21318996357400136359271088714736116654610185688745272911363942715795239438475, 1⟩, ⟨-64391769021076966472179743243673337393676659809662810214365525987030967235260, 1⟩, ⟨-327549243125118638003142582357400983448838169028099834795550557350338721420272, 1⟩, ⟨985515306442186385347677117562497404463245285217910124637091171375878994761792, 1⟩, ⟨5813766648845029643220273271993249777302919425868856426926440709770681056569856, 1⟩, ⟨9960945906609534129201909237345823699051577635006962888349317231791448086306816, 1⟩, ⟨6627968967176518935607143632244231290920201788436340391327614355758322693619712, 1⟩, ⟨1474476369005286609942888976755316119823448541481925816802747172162829897302016, 1⟩]

def e_common_E1_r8_U3_quotient : List Fraction :=
  [⟨3559105914658021460102405152484932397687135612470893185676622303770125490582572496, 3125⟩, ⟨591278286584379154619873405360894261192329552166013317633311394982586769140099904, 125⟩, ⟨1330085566419774342336508331257132140958540630976428006920396154335933696380076544, 125⟩, ⟨319726766444019402415947834186353853744961804383983253572417315868857918785773568, 25⟩, ⟨36088797573893167897921496114731788694247906025145553590243566123117273262702592, 5⟩, ⟨1474476369005286609942888976755316119823448541481925816802747172162829897302016, 1⟩]

theorem e_common_E1_r8_U3_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E1_r8_U3.map fractionValue) x := by
  apply squareReconstruction_positive e_common_E1_r8_U3 e_common_E1_r8_U3_quotient ⟨1, 5⟩ ⟨1262139681203683738943283443336824308590710799048069634110912009981335862961994851, 78125⟩ ⟨3155699005439819545977634789982997592636425654585738373587226289079958272413707972, 15625⟩ x
  · intro c hc
    simp only [e_common_E1_r8_U3_quotient, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  · norm_num
  · norm_num
  · norm_num
  · simp [e_common_E1_r8_U3_quotient]
  · exact hx
  · intro c hc
    simp only [e_common_E1_r8_U3_quotient, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0404_E1_r8_U3_strict_square_quotient_coefficient_0
    · exact cert_0405_E1_r8_U3_strict_square_quotient_coefficient_1
    · exact cert_0406_E1_r8_U3_strict_square_quotient_coefficient_2
    · exact cert_0407_E1_r8_U3_strict_square_quotient_coefficient_3
    · exact cert_0408_E1_r8_U3_strict_square_quotient_coefficient_4
    · exact cert_0409_E1_r8_U3_strict_square_quotient_coefficient_5
  · exact cert_0410_E1_r8_U3_strict_common_square_discriminant
  · exact reconstruct_158_E1_r8_U3_square_identity

theorem e_common_E1_r8_U3_closed_endpoint : 0 < fractionValue ⟨1474476369005286609942888976755316119823448541481925816802747172162829897302016, 1⟩ := by
  exact fraction_positive_sound _ cert_0411_E1_r8_U3_closed_x_1_endpoint

def e_common_E1_r8_D : List Fraction :=
  [⟨3467172087346336209467004550679, 1⟩, ⟨39555623398269874935685288151715, 1⟩, ⟨117563641014575996445561814152228, 1⟩, ⟨98794250961085320467154784596416, 1⟩, ⟨14526657839604739169535388685952, 1⟩]

theorem e_common_E1_r8_D_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E1_r8_D.map fractionValue) x := by
  apply realHorner_positive_of_checks e_common_E1_r8_D x (by simp [e_common_E1_r8_D]) hx
  · intro c hc
    simp only [e_common_E1_r8_D, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact cert_0416_E1_r8_D_strict_lower_coefficient_0
    · exact cert_0417_E1_r8_D_strict_lower_coefficient_1
    · exact cert_0418_E1_r8_D_strict_lower_coefficient_2
    · exact cert_0419_E1_r8_D_strict_lower_coefficient_3
    · exact cert_0420_E1_r8_D_strict_lower_coefficient_4

def e_common_E2_r8_H0 : List Fraction :=
  [⟨115514471781014629966860109449120732225047675296605, 1⟩, ⟨852322627191842894342530218017365506665625448518588, 1⟩, ⟨2270186516943876964504273829805792253131125651320992, 1⟩, ⟨2773200776808141973371173892502707117121919526377856, 1⟩, ⟨1710112827287329112816453734267299501151115197979648, 1⟩, ⟨714819369066322070538208086487883406916819057995776, 1⟩, ⟨296543983416094302092306987267034818211098885603328, 1⟩]

theorem e_common_E2_r8_H0_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E2_r8_H0.map fractionValue) x := by
  apply realHorner_positive_of_checks e_common_E2_r8_H0 x (by simp [e_common_E2_r8_H0]) hx
  · intro c hc
    simp only [e_common_E2_r8_H0, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0425_E2_r8_H0_strict_lower_coefficient_0
    · exact cert_0426_E2_r8_H0_strict_lower_coefficient_1
    · exact cert_0427_E2_r8_H0_strict_lower_coefficient_2
    · exact cert_0428_E2_r8_H0_strict_lower_coefficient_3
    · exact cert_0429_E2_r8_H0_strict_lower_coefficient_4
    · exact cert_0430_E2_r8_H0_strict_lower_coefficient_5
    · exact cert_0431_E2_r8_H0_strict_lower_coefficient_6

def e_common_E2_r8_U0 : List Fraction :=
  [⟨207071910342454243522911552929632051054686787414482862511730476776921521561959469775, 1⟩, ⟨1419789572483214959284970209377128632298670028221915220384750814076676876280293659440, 1⟩, ⟨4178662311983525287253594559258751505420615803607323224458000675350122742336095336880, 1⟩, ⟨6020483752523310672338667036739551795303395120536736473178842477410399046536551837440, 1⟩, ⟨2907522940152564029724130903611577412200046181712402861881444554647284040452060285440, 1⟩, ⟨85864603590122838193233174484973903983153146217070714002536057848815526356017362944, 1⟩]

theorem e_common_E2_r8_U0_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E2_r8_U0.map fractionValue) x := by
  apply realHorner_positive_of_checks e_common_E2_r8_U0 x (by simp [e_common_E2_r8_U0]) hx
  · intro c hc
    simp only [e_common_E2_r8_U0, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0435_E2_r8_U0_strict_lower_coefficient_0
    · exact cert_0436_E2_r8_U0_strict_lower_coefficient_1
    · exact cert_0437_E2_r8_U0_strict_lower_coefficient_2
    · exact cert_0438_E2_r8_U0_strict_lower_coefficient_3
    · exact cert_0439_E2_r8_U0_strict_lower_coefficient_4
    · exact cert_0440_E2_r8_U0_strict_lower_coefficient_5

def e_common_E2_r8_U1 : List Fraction :=
  [⟨10896464673442704334776652914020769520720398719186019647745462380798573660748549927427354975, 1⟩, ⟨51232115035111244134749489766675858437034396930276304446344572205903056285440921386809125920, 1⟩, ⟨85812055883518292030529097109358505750356717646818127009622292965727206340998902424072328000, 1⟩, ⟨284851949990162580291288600533532283107723366505632112502484119979178258642806692390929770240, 1⟩, ⟨963633294643525165836623325137998962116470111573108452277403294044537907421022452920462188800, 1⟩, ⟨1238888184549284507730547568833305669060232671008553615765039557772718990736789344293426585600, 1⟩, ⟨509864934372344096043183981399587724414611884415280756721371915171835531548806220696490991616, 1⟩, ⟨9866146081370238488891431035334745290627534179864834004602928426993955278671855210051207168, 1⟩]

theorem e_common_E2_r8_U1_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E2_r8_U1.map fractionValue) x := by
  apply realHorner_positive_of_checks e_common_E2_r8_U1 x (by simp [e_common_E2_r8_U1]) hx
  · intro c hc
    simp only [e_common_E2_r8_U1, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0444_E2_r8_U1_strict_lower_coefficient_0
    · exact cert_0445_E2_r8_U1_strict_lower_coefficient_1
    · exact cert_0446_E2_r8_U1_strict_lower_coefficient_2
    · exact cert_0447_E2_r8_U1_strict_lower_coefficient_3
    · exact cert_0448_E2_r8_U1_strict_lower_coefficient_4
    · exact cert_0449_E2_r8_U1_strict_lower_coefficient_5
    · exact cert_0450_E2_r8_U1_strict_lower_coefficient_6
    · exact cert_0451_E2_r8_U1_strict_lower_coefficient_7

def e_common_E2_r8_U2 : List Fraction :=
  [⟨1731302333154489983906412890188669303468796859680128414255724793581638736112863744890323025, 1⟩, ⟨2841791602897764815286955154290251618983018384401997967494358674334617421856308949177698720, 1⟩, ⟨-21796528523780703918374026120166231560757336508775245153890025532269244224542839977947598144, 1⟩, ⟨-32155712364404945400541668712832085371993615114747590907615575037956465265318709974291494656, 1⟩, ⟨114390077143957896093150578256536580350874793207043477015422224721159715377467838568260522752, 1⟩, ⟨264669933912113432933616501047441876291751578955903283930704909997219342750215717640157110272, 1⟩, ⟨166204380648615371133185886337614819175853524615731491644694753385041914292351828862564605952, 1⟩, ⟨27642604545999004348626462996844380526897157501812087587592390945911636799135894860040175616, 1⟩]

def e_common_E2_r8_U2_quotient : List Fraction :=
  [⟨3523773323571000340722174286137126316447530529803752475256904526546479583353940660382834800, 1⟩, ⟨85592607226672775070594942863339599613804007938946498900591293919329475488585768617763672448, 1⟩, ⟨279616028255754932419220336405863070875154190894308029138379470413584222982337658728822452480, 1⟩, ⟨352955112588795931815576906028157607228471558295358796175725859992098731796229612357696946176, 1⟩, ⟨180025682921614873307499117836037009439302103366637535438490948857997732691919776292584693760, 1⟩, ⟨27642604545999004348626462996844380526897157501812087587592390945911636799135894860040175616, 1⟩]

theorem e_common_E2_r8_U2_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E2_r8_U2.map fractionValue) x := by
  apply squareReconstruction_positive e_common_E2_r8_U2 e_common_E2_r8_U2_quotient ⟨1, 4⟩ ⟨1324601578685356598545241589405121359026834489847323390511132027584925011027409638806117498, 1⟩ ⟨-745859686983783456264141631599910198655966846880281976164144932350235004503331259241113408, 1⟩ x
  · intro c hc
    simp only [e_common_E2_r8_U2_quotient, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  · norm_num
  · norm_num
  · norm_num
  · simp [e_common_E2_r8_U2_quotient]
  · exact hx
  · intro c hc
    simp only [e_common_E2_r8_U2_quotient, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0455_E2_r8_U2_strict_square_quotient_coefficient_0
    · exact cert_0456_E2_r8_U2_strict_square_quotient_coefficient_1
    · exact cert_0457_E2_r8_U2_strict_square_quotient_coefficient_2
    · exact cert_0458_E2_r8_U2_strict_square_quotient_coefficient_3
    · exact cert_0459_E2_r8_U2_strict_square_quotient_coefficient_4
    · exact cert_0460_E2_r8_U2_strict_square_quotient_coefficient_5
  · exact cert_0461_E2_r8_U2_strict_common_square_discriminant
  · exact reconstruct_163_E2_r8_U2_square_identity

theorem e_common_E2_r8_U2_closed_endpoint : 0 < fractionValue ⟨27642604545999004348626462996844380526897157501812087587592390945911636799135894860040175616, 1⟩ := by
  exact fraction_positive_sound _ cert_0462_E2_r8_U2_closed_x_1_endpoint

def e_common_E2_r8_U3 : List Fraction :=
  [⟨11403483393076319983809720204585038576836586731872220072861292170869373644460525, 1⟩, ⟨30834674713629482974769595185548757946408061836015547892780271699292743160912840, 1⟩, ⟨-39354856460706879009654948149321837149292244278216653059449095756495122707253600, 1⟩, ⟨147607711040378738182028913663258377235164103122662540198858546532141215559799680, 1⟩, ⟨1451583281248881356910102566370355985793702636841540288018848793971136931250195200, 1⟩, ⟨2677764001431165534471636930603239743663248205809265061134839995061738565296844800, 1⟩, ⟨1850894090197980599922552513267783229907781061849653855750091062870862043795091456, 1⟩, ⟨406755799556800528188727124963358686550377318440933997002375788517149602138062848, 1⟩]

def e_common_E2_r8_U3_quotient : List Fraction :=
  [⟨512514724345303027093574224812045153796704530518473386873246587778061517756011232, 1⟩, ⟨1499105431780630502161857730075220873284797833499072741284398786140690118082007936, 1⟩, ⟨3162930161348885519643195073219895131142434271245541291352059352572614697243826176, 1⟩, ⟨3679477758947055933468299523167761112345334483941767113447830986844135137595277312, 1⟩, ⟨2054271989976380864016916075749462573182969721070120854251278957129436844864122880, 1⟩, ⟨406755799556800528188727124963358686550377318440933997002375788517149602138062848, 1⟩]

theorem e_common_E2_r8_U3_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E2_r8_U3.map fractionValue) x := by
  apply squareReconstruction_positive e_common_E2_r8_U3 e_common_E2_r8_U3_quotient ⟨1, 4⟩ ⟨27720799971492778324571481019299724030657669199857682143065540798373121199408063, 1⟩ ⟨193397947399991590136440599461870030264460462501560194999128641454530369658792960, 1⟩ x
  · intro c hc
    simp only [e_common_E2_r8_U3_quotient, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  · norm_num
  · norm_num
  · norm_num
  · simp [e_common_E2_r8_U3_quotient]
  · exact hx
  · intro c hc
    simp only [e_common_E2_r8_U3_quotient, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cert_0466_E2_r8_U3_strict_square_quotient_coefficient_0
    · exact cert_0467_E2_r8_U3_strict_square_quotient_coefficient_1
    · exact cert_0468_E2_r8_U3_strict_square_quotient_coefficient_2
    · exact cert_0469_E2_r8_U3_strict_square_quotient_coefficient_3
    · exact cert_0470_E2_r8_U3_strict_square_quotient_coefficient_4
    · exact cert_0471_E2_r8_U3_strict_square_quotient_coefficient_5
  · exact cert_0472_E2_r8_U3_strict_common_square_discriminant
  · exact reconstruct_164_E2_r8_U3_square_identity

theorem e_common_E2_r8_U3_closed_endpoint : 0 < fractionValue ⟨406755799556800528188727124963358686550377318440933997002375788517149602138062848, 1⟩ := by
  exact fraction_positive_sound _ cert_0473_E2_r8_U3_closed_x_1_endpoint

def e_common_E2_r8_D : List Fraction :=
  [⟨284334552067530333853838480346338, 1⟩, ⟨3174477245551583783114855752233215, 1⟩, ⟨9489647139646034854673903262261711, 1⟩, ⟨8253575815813138748180448098476856, 1⟩, ⟨1365060539016179525853779940629792, 1⟩]

theorem e_common_E2_r8_D_positive (x : ℝ) (hx : 0 ≤ x) :
    0 < realHorner (e_common_E2_r8_D.map fractionValue) x := by
  apply realHorner_positive_of_checks e_common_E2_r8_D x (by simp [e_common_E2_r8_D]) hx
  · intro c hc
    simp only [e_common_E2_r8_D, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact cert_0478_E2_r8_D_strict_lower_coefficient_0
    · exact cert_0479_E2_r8_D_strict_lower_coefficient_1
    · exact cert_0480_E2_r8_D_strict_lower_coefficient_2
    · exact cert_0481_E2_r8_D_strict_lower_coefficient_3
    · exact cert_0482_E2_r8_D_strict_lower_coefficient_4

end F4Heavy.Analysis
