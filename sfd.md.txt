# kollarsandor/optimizer – Teljes dokumentáció (Magyar)

Forrás: https://deepwiki.com/kollarsandor/optimizer
Generálva: 2026-04-14

-----

## Áttekintés

Az optimizer egy nagy teljesítményű, fejlett másodrendű optimalizálási algoritmusokat megvalósító könyvtár, amelyet modern mélytanulási feladatokhoz terveztek. Kifejezetten a következő generációs hardverarchitektúrákat célozza meg, mint például az NVIDIA B200 (Blackwell), és natív támogatást biztosít az ultra-alacsony precizitású tanításhoz (FP4/FP8), valamint kifinomult görbületbecslési technikákhoz.

A könyvtár célja áthidalni a szakadékot az elméleti másodrendű módszerek (például KFAC és Hessian-becslés) és a hardveren gyorsított, gyakorlati tanítás között. Egy egyedi Tensor primitíven és dedikált hardverabsztrakciós rétegeken keresztül hatékony adaptív tanulási rátákat tesz lehetővé, amelyek figyelembe veszik a veszteségfelszín geometriáját.

A könyvtár fő tervezési céljai a következők. A másodrendű optimalizálás kapcsán az SFD (Stochastic Fisher Diagonal) és a SophiaSOAP algoritmusokat valósítja meg, amelyek gyorsabb konvergenciát biztosítanak a hagyományos elsőrendű optimalizálókhoz, például az Adamhoz képest. A B200 hardver kihasználásához dedikált B200MemoryManager gondoskodik a 32 MB-os Tensor Memory (TMEM) kezeléséről, a B200KernelOptimizer pedig a műveletek fúziójáról Blackwell GPU-kon. A vegyes precizitás terén natív támogatást kap az fp64-től egészen az fp4-ig terjedő formátumtartomány, dinamikus veszteségskálázással és precizitástudatos típuskonverzióval. A memóriahatékonyság érdekében visszafordítható optimalizálóállapotok és adaptív gyorsítótárazás csökkenti a visszaterjesztés memóriaigényét.

-----

## Első lépések

Ez az útmutató gyakorlati bevezető mérnökök számára, akik integrálni szeretnék az optimizer könyvtárat Zig projektjeikbe. Lefedi a fő inicializálási folyamatot, a szükséges importokat, és egy minimális használati példát mutat be az SFD optimalizálóhoz.

Az optimalizáló használatához importálni kell a Tensor primitíveket és a memóriakezelést biztosító alapmodulokat. Az elsődleges interfész az sfd.zig fájlban van definiálva, amely a magas szintű API-ként funkcionál. A szükséges importok: a core/types.zig, amely az alapvető enum-okat és típusokat definiálja; a core/tensor.zig, amely a Tensor struktúrát és a matematikai műveleteket tartalmazza; valamint a core/memory.zig, amely a memória-allokációs stratégiákat kezeli, beleértve a B200-specifikus TMEM-kezelést.

Az SFD optimalizáló integrálásához először definiálni kell egy SFDConfig-ot, inicializálni az SFD struktúrát, majd a tanítási ciklusban meg kell hívni az update metódust.

Az SFDConfig struktúra paramétereit az alábbi táblázat foglalja össze.

|Paraméter      |Típus|Leírás                                                                      |
|---------------|-----|----------------------------------------------------------------------------|
|beta1          |f32  |Az első momentum exponenciális csökkentési rátája.                          |
|beta2          |f32  |A második momentum (sebesség) exponenciális csökkentési rátája.             |
|eps            |f32  |Kis konstans a numerikus stabilitáshoz.                                     |
|learning_rate  |f32  |Az alap lépésméret a frissítésekhez.                                        |
|clip_threshold |f32  |A gradiensek maximálisan megengedett normájának korlátja.                   |
|fisher_max     |f32  |A Fisher-diagonális értékeinek felső korlátja az instabilitás megelőzéséhez.|
|warmup_steps   |u32  |A tanulási ráta lineáris növelésének lépésszáma.                            |
|finite_diff_eps|f32  |A másodrendű lépések véges differenciás közelítéséhez használt epsilon.     |

A frissítési lépés menete a következő. Először az állapot inicializálásakor az SFD belső puffereket hoz létre (momentum, velocity, fisher_diagonal) az input paraméterek alakjának megfelelően. Ezt követi a momentum frissítése, amely a gradiensek mozgó átlagát számolja ki. Majd jön a sebesség frissítése a négyzetgyök-gradiensek mozgó átlagával. A Fisher-diagonális korrekció a második momentumokat a Fisher-információ becsléssel ötvözi, hogy paraméteres adaptív tanulási rátát biztosítson. Végül a paraméter-lépés a kiszámított frissítést alkalmazza a súly tensorra.

-----

## Architektúra-áttekintés

Az optimizer könyvtár réteges architektúrája négy egymásra épülő rétegből áll, a mély memória- és hardverprimitivektől a magas szintű automatizált hangolásig.

Az első réteg a Tensor primitív réteg, amely a könyvtár alapját képezi. Egy egyedi Tensor implementációból áll, amely vegyes precizitást (FP4-től FP64-ig) és hardvertudatos memóriakezelést támogat. A Tensor az alapadatstruktúra, amely adatpuffereket, alakokat és metaadat-jelzőket tartalmaz. A precizitáskezelés a formátumok közötti kvantálást és típuskonverziót végzi, beleértve a speciális fp4 és fp8 típusokat is. A lineáris algebra optimalizált implementációkat biztosít a matmul, outerProduct és spectralNorm műveletekhez.

A második réteg az optimalizáló réteg, amely az alapvető optimalizálási algoritmusokat valósítja meg. A fókusz a Hessian vagy a Fisher-információs mátrix közelítésén van, hogy adaptív tanulási rátákat biztosítsanak. Az SFD az elsődleges optimalizáló, amely momentum-, sebesség- és Fisher-diagonális puffereket tart fenn a paraméterfrissítések kiszámításához. A SophiaSOAP egy fejlettebb optimalizáló, amely a Sophia másodrendű megközelítést a KFAC-kal kombinálja. A KFACBlock kezeli a Kronecker-faktorokat a rétegenkénti gradiens-előkondicionáláshoz.

A harmadik réteg a hardverabsztrakciós réteg, amely kifejezetten NVIDIA B200 GPU-kra lett optimalizálva. A B200MemoryManager a 32 MB-os Tensor Memory-t kezeli, és az access_freq küszöbértéke alapján dönt arról, hogy egy tensort HBM-ből TMEM-be helyez-e át. A B200KernelOptimizer operátorfúziót végez, több műveletet (MatMul + Bias + Aktiváció) egyetlen fused_gemm_bias_act hívássá kombinálva. A PerformanceMonitor hardver-specifikus metrikákat követ nyomon, mint a tensor_core_util és az nvlink_bandwidth_util.

A negyedik réteg a tanítási segédeszközök rétege. Az LRScheduler dinamikus tanulási ráta stratégiákat valósít meg, köztük a cosine_annealing és a sophia_style Hessian-alapú csökkentést. A MixedPrecisionTrainer koordinálja a mester FP32 súlyok és a kvantált munkasúlyok használatát a DynamicLossScaler segítségével. A BayesianOptimizer Gauss-folyamat modell segítségével automatizálja a hiperparaméter-hangolást.

A fő komponensek egymáshoz való viszonyát az alábbi táblázat foglalja össze.

|Magas szintű fogalom   |Kódentitás                            |
|-----------------------|--------------------------------------|
|Másodrendű optimalizáló|SFD, SophiaSOAPOptimizer              |
|Görbületközelítés      |KFACBlock, updateHessianDiagonal      |
|Hardverkezelés         |B200MemoryManager, B200KernelOptimizer|
|Állapotmentés          |Tensor.save, Tensor.load              |

-----

## Tensor könyvtár

A Tensor könyvtár az összes optimalizálási művelet alapját alkotó adatstruktúrákat és matematikai primitíveket biztosítja. Nagy teljesítményű mélytanulási feladatokhoz tervezték, különös tekintettel a másodrendű optimalizálási módszerekre és az NVIDIA Blackwell (B200) architektúrákra vonatkozó hardver-specifikus optimalizálásokra.

A rendszer a Tensor struktúra köré épül, amely egy összefüggő memóriablokkot és a kapcsolódó metaadatokat foglalja magában. A könyvtár számos numerikus precizitást támogat, a standard FP64-től a rendkívül tömörített FP4 formátumokig, lehetővé téve a vegyes precizitású tanítási munkafolyamatokat.

-----

## Tensor adatstruktúra és műveletek

A Tensor struktúra a könyvtár alapvető építőköve, amely egységes interfészt biztosít a többdimenziós adattároláshoz, a matematikai műveletekhez és a memóriakezeléshez. Vegyes precizitású tanítást és hardver-specifikus optimalizálásokat támogat olyan platformokon, mint az NVIDIA B200.

A Tensor struktúra mezői a következők.

|Mező     |Típus      |Leírás                                                                         |
|---------|-----------|-------------------------------------------------------------------------------|
|data     |[]f32      |Az alapul szolgáló lapos memóriapuffer a tensor elemekkel.                     |
|shape    |Shape      |A tensor dimenzióit és teljes méretét tartalmazó struktúra.                    |
|dtype    |Precision  |A numerikus precizitás (pl. fp32, fp16, fp8, fp4).                             |
|flags    |TensorFlags|Logikai jelzők a memória-elhelyezkedésről, gradiens-követésről és tömörítésről.|
|allocator|Allocator  |A Zig allocator, amely a tensor életciklusát kezeli.                           |

A TensorFlags struktúra három jelzőt tartalmaz. Az in_tensor_memory jelzi, hogy a tensor jelenleg a B200 TMEM-ben található-e. A requires_grad meghatározza, hogy a tensornak részt kell-e vennie a gradiens-számításban. Az is_compressed igaz értéket vesz fel az fp4 vagy fp8 formátumoknál.

Az inicializálási módszerek közül az init a megadott dimenziókhoz allokál memóriát és biztosítja, hogy a Tensor saját alakmetaadatokkal rendelkezzen. A zeros nullákkal tölti fel a puffert, az ones egyesekkel, az eye pedig egy négyzetes identitásmátrixot hoz létre.

A véletlenszerű inicializáláshoz a könyvtár globális PRNG számlálót és Wyhash függvényt használ a determinisztikus, de változatos inicializáláshoz. A fillRandomNormal a Box-Muller transzformációt alkalmazza normáleloszlású kitöltéshez, a fillRademacher pedig -1.0 vagy 1.0 értékeket rendel véletlenszerűen (ez utóbbi a Hutchinson Hessian-becslésben használatos).

A matematikai műveletek közül az add helyben adja össze a tensorokat, a sub vonja ki, a mulScalar pedig egy skaláris konstanssal szorozza az összes elemet. A lineáris algebrában a matmul standard mátrixszorzást végez, az outerProduct két vektor külső szorzatát számítja ki, a normL2 a Frobenius/L2 normát adja vissza, a spectralNorm pedig a legnagyobb szinguláris értéket becsüli a Power Iteration módszerrel.

A könyvtár allokátor-agnosztikus, ami elengedhetetlen a B200MemoryManager számára a HBM és TMEM közötti átmenetek kezeléséhez. Az initWithArena rövid életű tensorokhoz való, az initWithPool és initWithSlab fix méretű tensorokhoz (pl. KFAC blokkokban), az initWithBuddy pedig nagy, dinamikus allokációkhoz a 32 MB-os TMEM hatékony kezelésére.

-----

## Precizitás és kvantálás

A könyvtár robusztus rendszert biztosít a vegyes precizitású tanításhoz és a memóriahatékony tensor-reprezentációhoz. A rendszer középpontjában a Precision enum és kvantálási segédfüggvények állnak.

Az öt támogatott precizitási szint a következő.

|Enum tag|Leírás                        |Implementációs állapot             |
|--------|------------------------------|-----------------------------------|
|fp4     |4 bites lebegőpontos          |Szimulált, [-8.0, 7.0] clamping    |
|fp8     |8 bites lebegőpontos          |Szimulált, [-448.0, 448.0] clamping|
|fp16    |16 bites félprecizitású       |Szimulált, 1/1024 kerekítés        |
|fp32    |32 bites egyszeres precizitású|Natív f32                          |
|fp64    |64 bites dupla precizitású    |f32-re vetítve                     |

A kvantálást elsősorban a quantizeValue függvény végzi. FP4 esetén az értékek -8.0 és 7.0 közé szorulnak, majd a legközelebbi 0.5-ös lépésre kerekítődnek. FP8 esetén a tartomány -448.0 és 448.0, a kerekítés 1/16-os lépésekben történik. FP16 esetén nincs explicit clamping, de az értékek 1/1024-re kerekítődnek.

A copyFromWithCast metódus a forrástensor minden elemén alkalmazza a quantizeValue-t, és automatikusan beállítja a TensorFlags.is_compressed jelzőt, ha a cél dtype fp4 vagy fp8. A convertToFP4 egy specializált kényelmi metódus, amely a tensor dtype-ját fp4-re állítja és újrakvantálja az adatokat.

A bináris szerializálási formátum varázs számmal azonosítható: 0x54464453 (ASCII “SDFT” little-endian sorrendben). A fájlszerkezet a következő elemekből áll: varázsszám (u32), rang azaz a dimenziók száma (u32), dimenziók (u64 tömb, rankonként egy), dtype (u8), jelzők (u8 bitmaszk), és az adatok (f32 tömb). A jelzők bitmaszk-kodolása: 0b001 az in_tensor_memory, 0b010 a requires_grad, 0b100 az is_compressed.

-----

## Optimalizálók

A könyvtár két elsődleges optimalizálóra összpontosít: az SFD-re (Stochastic Fisher Diagonal), amely egy robusztus adaptív optimalizáló az Adam és a Shampoo tulajdonságait ötvözi, valamint a SophiaSOAPOptimizerre, amely a Sophia másodrendű megközelítést kombinálja a KFAC-kal és Hessian-alapú frissítésekkel.

A két optimalizáló összehasonlítása az alábbi táblázatban látható.

|Tulajdonság   |SFD                                            |SophiaSOAP                                               |
|--------------|-----------------------------------------------|---------------------------------------------------------|
|Fő stratégia  |Adaptív tanulási rátá + Fisher-diagonális      |KFAC + Hutchinson Hessian-becslés                        |
|Görbülettérkép|A Fisher-mátrix diagonális közelítése          |Blokk-diagonális KFAC + sztochasztikus Hessian-diagonális|
|Komplexitás   |Alacsony, O(N) memória és számítás             |Magas, O(N) + KFAC blokk overhead                        |
|Stabilitás    |Sajátérték-korrekció a spektrális stabilitásért|EMA-simított Hessian és előkondicionálás                 |

-----

## SFD optimalizáló (Stochastic Fisher Diagonal)

Az SFD egy nagy teljesítményű másodrendű optimalizálási algoritmus, amelyet nagyszabású mélytanulási feladatokhoz terveztek. A Fisher-információs mátrixot (FIM) egy diagonális becsléssel közelíti, ötvözi az elsőrendű módszerek hatékonyságát az Adam-tól ismert megközelítéssel és a másodrendű módszerek görbülettudatosságával. Az implementáció kifejezetten NVIDIA B200 hardverre van hangolva.

Az SFDConfig paramétereit az alábbi táblázat foglalja össze.

|Paraméter       |Típus|Leírás                                                                  |
|----------------|-----|------------------------------------------------------------------------|
|beta1           |f32  |Az első momentum exponenciális csökkentési rátája.                      |
|beta2           |f32  |A második momentum (Fisher-diagonális) exponenciális csökkentési rátája.|
|eps             |f32  |A nevező stabilizálásához hozzáadott tag.                               |
|clip_threshold  |f32  |Globális gradiens vágási küszöb.                                        |
|fisher_max      |f32  |A Fisher-diagonális bejegyzéseinek maximális értéke.                    |
|warmup_steps    |u32  |Kezdeti lépések száma csökkentett tanulási rátával.                     |
|finite_diff_eps |f32  |Epsilon a véges differenciás közelítésekhez.                            |
|second_order_eps|f32  |Regularizációs tag a másodrendű görbületi mátrix-inverziókhoz.          |

Az SFD struktúra a következő puffereket tartja fenn: az m a gradiensek EMA-ját tárolja (momentum), a v a négyzetgyök-gradiensek EMA-ját (standard Adam második momentum), a fisher_diag pedig a Fisher-információs mátrix diagonálisának sztochasztikus közelítését.

A frissítési lépés menete: először a momentum frissítése történik, majd a sebesség frissítése, ezután a Fisher-közelítés frissítése (ahol a négyzetes gradienseket görbületi becsléssé ötvözi), majd az adaptív tanulási ráta alkalmazása és végül a clip_threshold szerinti vágás.

A correctEigenvalues metódus egyedi jellemzője az SFD implementációnak. Ez a függvény a standard Adam-stílusú második momentumokat ötvözi egy Shampoo-stílusú sajátérték-megközelítéssel, biztosítva, hogy az előkondicionáló pozitív definit és jól kondicionált maradjon. A second_order_eps regularizálja a diagonálist, a fisher_max pedig korlátozza a bejegyzéseket, nehogy az előkondicionáló teljesen elnyelje a gradienseket magas görbületű régiókban.

-----

## SophiaSOAP optimalizáló

A SophiaSOAPOptimizer egy fejlett másodrendű optimalizáló implementáció, amely a Sophia (Second-order Stochastic Optimization) algoritmus erősségeit kombinálja a SOAP (Shampoo Preconditioned Adaptive) technikákkal. Modern hardveren, mint az NVIDIA B200, Kronecker-faktorizált Approximate Curvature (KFAC) és periodikus Hutchinson-becslőt alkalmaz a Hessian-diagonális becsléséhez.

A SophiaSOAPConfig konfigurációs struktúra paraméterei a következők: lr az alap tanulási ráta, beta1 és beta2 a momentum és a második momentum EMA faktorai, rho a maximális frissítési méret korlátozója (Sophia-stílusú optimalizálókra jellemző), hessian_update_freq szabályozza, hogy milyen gyakran kell újrabecsülni a Hessian-diagonálist, és ema_hessian a Hessian-diagonális becslés simítási faktora.

Az optimalizáló rétegenkénti KFAC blokkokat tart fenn, amelyek mindegyike tartalmaz egy A_inv és egy G_inv faktormátrixot a gradiens előkondicionálásához.

A frissítési folyamat három szakaszból áll. Az első szakaszban KFAC előkondicionálás történik: az optimalizáló végigiterál a rétegeken és alkalmazza a KFAC előkondicionálást, ami a gradiens dekorrelálását eredményezi. A második szakaszban periodikus Hessian-becslés következik: ha az aktuális lépés megfelel a hessian_update_freq értékének, az updateHessianDiagonal meghívódik, amely Rademacher-mintavételt végez, irányderiváltat számít, majd EMA-szal frissíti a hessian_diag puffert. A harmadik szakaszban hibrid paraméterfrissítés zajlik, ahol az előkondicionált gradienseket a Hessian-diagonális becsléssel kombinálja egy Sophia-stílusú frissítésbe.

-----

## Másodrendű módszerek: KFAC és Hessian-becslés

Mindkét optimalizáló kifinomult matematikai közelítésekre támaszkodik az optimalizálási tájkép görbületéhez.

A KFAC alrendszer a KFACBlock struktúrát alkalmazza a Fisher-információs mátrix rétegenkénti közelítéséhez. Ahelyett, hogy a teljes, hatalmas FIM-et tárolná, a KFAC feltételezi, hogy egy réteg Fisher-mátrixa felírható két kisebb mátrix Kronecker-szorzataként: A (aktivációkból) és G (visszaterjesztett gradiensekből).

A KFACBlock mezői a következők.

|Mező |Típus |Leírás                                    |
|-----|------|------------------------------------------|
|A_inv|Tensor|Az aktivációs kovariancia mátrix inverze. |
|G_inv|Tensor|A gradiens kovariancia mátrix inverze.    |
|m_A  |Tensor|Az aktivációs külső szorzatok futó átlaga.|
|m_G  |Tensor|A gradiens külső szorzatok futó átlaga.   |

Az adatfolyamat a következő: az updateStatistics felhalmozza az aktivációk és gradiensek külső szorzatait EMA segítségével, az updateInverses periodikusan kiszámítja a felhalmozott statisztikák inverzét, a preconditionGradient pedig a W_grad gradiensre alkalmazza a faktorokat a G_inv * W_grad * A_inv művelettel.

A Hutchinson-becslő a SophiaSOAPOptimizernél a Hessian mátrix diagonálisának közelítésére szolgál, anélkül hogy a teljes Hessiant kellene kiszámolni. Az updateHessianDiagonal folyamata: először Rademacher-mintavétel történik, ahol z vektort generálunk {-1, 1} elemekkel, majd irányderiváltat számolunk véges differenciák segítségével, és végül EMA simítással frissítjük a diagonális becslést.

A két módszer összehasonlítása az alábbi táblázatban látható.

|Jellemző         |KFAC                           |Hessian-diagonális                    |
|-----------------|-------------------------------|--------------------------------------|
|Közelítés        |Kronecker-szorzat faktorok     |Hessian diagonálisa                   |
|Mintavétel       |Tényleges aktivációk/gradiensek|Véletlen Rademacher vektorok          |
|Számítási költség|Magas (mátrix-inverziók)       |Közepes (extra gradiens kiértékelések)|
|Memóriaköltség   |O(n²) a faktormátrixokhoz      |O(n) (megegyezik a súlyokéval)        |

-----

## Tanítási segédeszközök

A tanítási segédeszközök a könyvtáron belüli alrendszerek, amelyek numerikus stabilitást, memóriahatékonyságot és gyors konvergenciát biztosítanak. Különösen az NVIDIA B200 nagy teljesítményű hardvert célozzák.

-----

## Tanulási ráta ütemezés

Az LRScheduler kezeli a tanulási ráta változását a tanítási folyamat során. A standard cosine_annealing és one_cycle stratégiákon túl implementál egy sophia_style ütemezést is, amely a Hessian-diagonális becslés alapján dinamikusan adaptálja a tanulási rátát, lassítva magas görbületű régiókban és gyorsítva laposabb területeken.

Az LRScheduler mezői a következők.

|Mező        |Típus     |Leírás                                     |
|------------|----------|-------------------------------------------|
|base_lr     |f32       |A kiindulási vagy maximális tanulási ráta. |
|min_lr      |f32       |A csökkentés utáni minimális tanulási ráta.|
|warmup_steps|usize     |A lineáris növekedési szakasz lépésszáma.  |
|total_steps |usize     |A tanítás teljes várható iterációszáma.    |
|strategy    |LRStrategy|A matematikai csökkentési profil.          |
|current_step|usize     |Az eltelt tanítási lépések száma.          |

A támogatott stratégiák: constant megtartja az alap tanulási rátát, cosine_annealing koszinusz-csökkentési görbét alkalmaz, one_cycle kétfázisú stratégia, a sophia_style pedig a Hessian-diagonális értékek nagyságával skálázza a tanulási rátát, biztosítva, hogy magas görbületnél a tanulási ráta csökkenjen.

A warmup szakaszban a tanulási ráta kiszámítása: base_lr szorozva az (aktuális_lépés / warmup_lépések) értékkel.

-----

## Vegyes precizitású tanítás

A vegyes precizitású tanítás az NVIDIA B200 hardveren a lehető legjobb teljesítményt biztosítja azáltal, hogy alacsonyabb precizitású numerikus formátumokat (FP16, FP8, FP4) használ a számítások nagy részéhez, miközben FP32-es mester súlymásolatot tart fenn a numerikus stabilitás megőrzéséhez.

A MixedPrecisionTrainer komponens kezeli a magas precizitású mester súlyok és az alacsony precizitású munkasúlyok életciklusát. A DynamicLossScaler megakadályozza a gradiens alulcsordulást azzal, hogy skálázza a veszteséget mielőtt alacsonyabb precizitásra konvertálódna. A copyFromWithCast a fő mechanizmus az adatok mester súlyokból munkasúlyokba történő áthelyezéséhez, amely minden elemen alkalmazza a quantizeValue függvényt. A syncWorkingWeights az összes tensort végigiterálva frissíti a munkasúlyokat a mester súlyokból, az updateMasterWeights pedig a nem skálázott gradienseket alkalmazza vissza az FP32 mester tensorokra.

A DynamicLossScaler a következő paraméterekkel rendelkezik: scale az aktuális szorzó, growth_factor a skála növelésének szorzója stabil gradiensek esetén (alapértéke 2.0), backoff_factor az azonnali csökkentés szorzója túlcsordulás esetén (alapértéke 0.5), és update metódus, amely ha túlcsordulást észlel, csökkenti a skálát és kihagyja az optimalizáló lépést.

-----

## Gradiens-folyam vezérlés és variancia-csökkentés

A könyvtár három fő komponenst valósít meg a gradiens-folyam és a variancia kezelésére.

A SpectralNormalizer biztosítja, hogy a súlymátrixok ne növekedjenek kontrollálhatatlanul, korlátozva a max_singular_value értékét. Hatalomiteráció segítségével becsüli meg a legnagyobb szinguláris értéket, majd ha az meghaladja a korlátot, az egész tensort átskálázza.

A GradientFlowController magas szintű kezelőként kombinálja a súlyok spektrális normalizálását a belső gradiens-normalizálással, biztosítva, hogy a frissítések nulla középértékű és egységnyi varianciájú eloszlással rendelkezzenek.

A MARSVarianceReducer a MARS (Memory-efficient Adaptive Reductive Stochastic) technikát implementálja a sztochasztikus gradiens becslések stabilizálásához. A reference_gradients puffer tartalmazza a korábbi gradiensek mozgó átlagát, a beta paramétert a referencia gradiensek frissítési simítási faktoraként alkalmazza, a reduce lépés során pedig kiszámítja a különbséget az aktuális és a referencia gradiensek között, és frissíti mindkettőt.

-----

## Visszafordítható optimalizálóállapot

A ReversibleOptimizerState egy memória-optimalizálási komponens, amely csökkenti a visszaterjesztés során szükséges HBM memóriaigényt. Kezeli a memóriafelhasználás és a számítási overhead közötti kompromisszumot az aktivációk gyorsítótárazásával és a rétegállapotok fixpontos rekonstrukciójával.

A standard visszaterjesztésnél az előrepasszból származó aktivációkat memóriában kell tárolni. Mély hálózatoknál ez lineárisan nő a rétegek számával. A ReversibleOptimizerState ezt úgy kezeli, hogy vagy gyorsítótárazza az aktivációkat a CachePolicy alapján, vagy menetközben rekonstruálja őket a reverseLayer függvény segítségével.

A CachePolicy enum három értéket vesz fel: always_cache maximalizálja a sebességet, de nagy memóriát igényel; always_recompute minimalizálja a memóriát, de magas számítási igénnyel jár; adaptive dinamikusan vált a kettő között a memóriahelyzet és a réteg számítási intenzitása alapján.

A memória- és számítási kompromisszum összefoglalása a következő.

|Stratégia               |Memória-komplexitás|Számítási komplexitás|Elsődleges felhasználás                       |
|------------------------|-------------------|---------------------|----------------------------------------------|
|Teljes gyorsítótárazás  |O(L × N)           |1x                   |Kis modellek, nagy HBM rendelkezésre állással.|
|Visszafordítható rétegek|O(1 × N)           |kb. 1.3–1.5x         |Ultra-mély modellek, B200 TMEM optimalizálás. |
|Ellenőrzőpontozás       |O(√L × N)          |1.25x                |Kiegyensúlyozott munkaterhelések.             |

-----

## Hardveroptimalizálás (NVIDIA B200 / Blackwell)

Az optimizer könyvtár kifejezetten az NVIDIA Blackwell (B200) architektúra egyedi hardverképességeinek kihasználásához lett tervezve. A könyvtár dedikált hardverabsztrakciós réteget implementál, amely a nagy sebességű on-chip memória kezelésére és az agresszív kernel-fúzióra összpontosít.

A fő komponensek: a B200MemoryManager automatizálja az adatok mozgatását a HBM és a 32 MB-os TMEM között, a B200KernelOptimizer elemzi a műveleti gráfokat és több matematikai lépést egyetlen, nagy hatékonyságú GPU kernellé fúzionál, a PerformanceMonitor és a B200Profiler pedig valós időben követi nyomon a hardver kihasználtságát.

A teljesítmény-referenciaadatok az alábbi táblázatban láthatók.

|Komponens          |Kódentitás         |Fő felelősség                                |
|-------------------|-------------------|---------------------------------------------|
|Memóriakezelő      |B200MemoryManager  |TMEM és HBM elhelyezés kezelése              |
|Kernel-optimalizáló|B200KernelOptimizer|Műveletek egyetlen kernellé fúzionálása      |
|Profilozó          |B200Profiler       |Blackwell-specifikus hardvermetrikák mérése  |
|Metrikatár         |MetricsStore       |Kihasználtsági és teljesítményadatok tárolása|

-----

## B200 memóriakezelés (TMEM)

A B200 memóriakezelő rendszer egy speciális hardverabsztrakciós réteg, amely az NVIDIA Blackwell (B200) GPU-k architektúrális jellemzőit aknázza ki. Középpontjában a Tensor Memory (TMEM) kezelése áll, egy nagy sávszélességű, kis késleltetésű 32 MB-os memóriakészlet, amely közelebb helyezkedik el a Tensor Core-okhoz, mint a standard HBM.

A B200MemoryManager dinamikusan mozdítja az aktívan használt tensorokat TMEM-be, csökkentve a HBM buszterhelést és jelentősen növelve a teljesítménykritikus műveletek átviteli sebességét.

A B200MemoryManager mezői a következők.

|Mező            |Típus             |Leírás                                                         |
|----------------|------------------|---------------------------------------------------------------|
|tmem_size       |usize             |A TMEM teljes kapacitása (B200 esetén 32 MB).                  |
|available_tmem  |usize             |A tensor előléptetéshez rendelkezésre álló bájtok száma.       |
|access_threshold|u32               |A HBM-ből TMEM-be való előléptetést kiváltó elérési frekvencia.|
|resident_tensors|ArrayList(*Tensor)|A jelenleg TMEM-ben lévő tensorokra mutató pointerek.          |

A tensor-előléptetés folyamata: az optimizeMemoryAccess metódus minden egyes tensor-elérésnél növeli az access_freq számlálót, majd ellenőrzi, hogy meghaladta-e az access_threshold értéket. Ha igen és van elegendő szabad hely, a TensorFlags.in_tensor_memory jelzőt igazra állítja és frissíti a belső könyvelést. A prefetchToTMEM függvény manuálisan is kiválthatja a TMEM-be mozgatást, hogy elrejtse az adatátvitel késleltetését egy kernelindítás előtt.

A TMEM kezelés motivációja az HBM és TMEM sávszélesség különbségéből fakad. Az aktívan frissített tensorok (mint a FisherDiagonal vagy HessianDiagonal) TMEM-ben tartásával a könyvtár csökkenti a késleltetést, maximalizálja a kernel-fúzió hatékonyságát és megakadályozza a HBM busz telítettségét.

|Memória-szint|Kapacitás|Tipikus felhasználás az optimalizálóban                            |
|-------------|---------|-------------------------------------------------------------------|
|HBM          |141 GB+  |Mester súlyok, nagy aktivációs pufferek, történeti ellenőrzőpontok.|
|TMEM         |32 MB    |Aktív gradiensek, Fisher-diagonális, KFAC faktorok (A_inv, G_inv). |

-----

## Kernel-fúzió és B200 profilozás

A B200KernelOptimizer felelős a memóriasávszélességi szűk keresztmetszetek csökkentéséért azzal, hogy több diszkrét műveletet egyetlen GPU kernel futtatásba fúzionál. A Blackwell architektúrán a HBM menetszám minimalizálása kritikus a magas Tensor Core kihasználtság fenntartásához.

A fuseOperations metódus azonosítja azokat a lineáris algebra és aktiváció műveleti sorozatokat, amelyek egyetlen menetben hajthatók végre. A célminta a következő: mátrixszorzás (MatMul) → elem-szerinti összeadás (Bias) → aktivációs függvény. Amikor ez a minta detektálható, az optimalizáló egy fused_gemm_bias_act hívást alkalmaz, és a közbülső eredmények on-chip regiszterekben vagy TMEM-ben maradnak, elkerülve a HBM-be való visszaírást.

A profilozási rendszer telemetriai összetevői az alábbiak.

|Metrika                 |Kódentitás           |Leírás                                                |
|------------------------|---------------------|------------------------------------------------------|
|Teljes kihasználtság    |utilization_percent  |A GPU teljes terhelési százaléka                      |
|Tensor Core terhelés    |tensor_core_util     |A Blackwell Tensor Core-ok kihasználtsága             |
|Összekötési sávszélesség|nvlink_bandwidth_util|Az NVLink kihasználtsága többGPU-s kommunikációhoz    |
|Teljesítmény            |steps_per_sec        |A kiszámított tanítási iterációk száma másodpercenként|

A PerformanceMonitor a recordStep metódus segítségével rögzíti az egyes tanítási iterációk időtartamát, a generateReport pedig feldolgozza a nyers metrikákat olvasható formátumba, átlagokat számítva és lehetséges szűk keresztmetszeteket azonosítva.

-----

## Hiperparaméter-optimalizálás

Az optimizer könyvtár automatizált hiperparaméter-hangolási rendszert tartalmaz, amelynek középpontjában egy Bayesi-optimalizáló áll, Gauss-folyamat modellel. Ez lehetővé teszi a konfigurációs tér hatékony feltárását kimerítő rácsos keresés nélkül.

Az optimalizálási folyamat zárt hurokként működik: teljesítménymetrikákat gyűjt a tanítási futtatásokból, egy valószínűségi modellt (Gauss-folyamat) frissít velük, majd egy akvizíciós függvénnyel javasolja a következő tesztelendő hiperparaméter-készletet.

A BayesianOptimizer struktúra Observation objektumok előzményét tartja fenn, amelyek párosítanak egy HyperparamConfig-ot az eredményül kapott teljesítménymutatóval. Az update metódus egy új megfigyeléssel finomítja a belső Gauss-folyamat modellt, a suggest metódus pedig a következő kiértékelendő HyperparamConfig-ot adja meg.

-----

## Bayesi optimalizáló és Gauss-folyamat

A BayesianOptimizer zárt hurkú hiperparaméter-hangolási alrendszer, amely Gauss-folyamat szurrogátmodellt alkalmaz az objektív függvény közelítésére, és Expected Improvement akvizíciós függvénnyel egyensúlyoz a feltárás és a kihasználás között.

A Gauss-folyamat szurrogátmodell Squared Exponential (RBF) kernelje méri a két hiperparaméter-készlet hasonlóságát:

k(x, x’) = σ² · exp(−‖x − x’‖² / 2l²)

ahol a sigma_f a jelel varianciáját képviseli, a length_scale pedig a függvény simítottságát szabályozza.

A predict függvény kiszámítja a posterior átlagot és varianciát egy új x* pontra a meglévő megfigyelések alapján, a kovarianciamátrix felépítésével és egy kis zaj hozzáadásával a numerikus stabilitáshoz.

Az expectedImprovement akvizíciós függvény kiszámítja a jelenlegi legjobb értéken való várható javulást. Az erfApprox segítségével megbecsüli annak valószínűségét, hogy egy jelölt pont meghaladja az aktuális legjobb értéket. A magas exploration_factor nagy bizonytalanságú régiók mintavételét ösztönzi, alacsony értéknél a magas GP-átlag régiók kerülnek előtérbe.

-----

## Hiperparaméter-konfigurációs referencia

Ez az oldal átfogó technikai referenciát biztosít a könyvtár összes konfigurálható paramétere számára.

Az SFDConfig fő paraméterei: lr (alap tanulási ráta, alapértéke 1e-3), beta1 (első momentum csökkentési ráta, alapértéke 0.9), beta2 (második momentum csökkentési ráta), eps (numerikus stabilitási konstans), clip_threshold (gradiens vágási küszöb), fisher_max (Fisher-diagonális felső korlátja).

A SophiaSOAPConfig paraméterei a következők.

|Paraméter          |Típus |Alapérték  |Tartomány|Leírás                                                 |
|-------------------|------|-----------|---------|-------------------------------------------------------|
|lr                 |f32   |1e-3       |(0, 1]   |Alap tanulási ráta.                                    |
|betas              |[2]f32|{0.9, 0.95}|[0, 1)   |betas[0] momentum, betas[1] Hessian EMA.               |
|rho                |f32   |0.03       |> 0      |Hessian frissítési intenzitás.                         |
|weight_decay       |f32   |0.1        |[0, 1]   |Szétcsatolt súlycsökkentési együttható.                |
|hessian_update_freq|u32   |10         |[1, ∞)   |A Hutchinson Hessian-becslés frekvenciája (lépésekben).|

A KFACBlock konfigurációs paraméterei: ema_decay (az A és G faktormátrixok csökkentési rátája, alapértéke 0.95), damping (Tikhonov regularizáció az inverziók előtt, alapértéke 1e-3), update_freq (az A_inv és G_inv kiszámításának frekvenciája, alapértéke 10).

Az LRScheduler paraméterei: strategy (lehetséges értékek: constant, linear_decay, cosine_annealing, one_cycle, sophia_style), base_lr (1e-3), max_lr (1e-2), min_lr (1e-5), warmup_steps (1000), total_steps (100000).

A BayesianOptimizer és Gauss-folyamat paraméterei: num_initial_points (kezdeti véletlen minták száma a GP modell indítása előtt, alapértéke 5), exploration_weight (az akvizíciós függvény kappa paramétere, alapértéke 0.1), gp_length_scale (a Squared Exponential kernel l paramétere, alapértéke 1.0), gp_signal_variance (a kernel σ² paramétere, alapértéke 1.0).

A Bayesi hangolási rendszer a következő paramétercsoportokat célozza meg.

|Komponens       |Fő paraméterek                      |
|----------------|------------------------------------|
|SFD optimalizáló|learning_rate, beta1, beta2, epsilon|
|SophiaSOAP      |hessian_update_freq, rho            |
|KFAC            |ema_decay, damping                  |
|Ütemező         |warmup_steps, min_lr                |

-----

## Szószedet

Ez az oldal átfogó referenciát biztosít az sfd.zig könyvtárban használt technikai terminológiára, matematikai konstrukciókra és kódbázis-specifikus absztrakciókra.

A Tensor a könyvtár alapvető többdimenziós tömb primitívje, amely saját memóriakezeléssel rendelkezik és több numerikus precizitást támogat. Mezői: data (f32 szelet), shape (dimenziók), dtype (Precision), flags (TensorFlags), allocator.

A Shape egy struktúra, amely a Tensor dimenzióit írja le. A totalSize() metódusa kiszámítja az összes dimenzió szorzatát a memóriaigény meghatározásához.

A TensorFlags egy bitfield-szerű struktúra, amely a tensor állapotát és hardver-elhelyezkedését követi nyomon. Mezői: in_tensor_memory (B200 TMEM elhelyezkedés), requires_grad (autograd követés), is_compressed (kvantálási állapot).

Az SFD (Stochastic Fisher Diagonal) az elsődleges másodrendű optimalizáló implementáció, amely a Fisher-információs mátrixot diagonális becsléssel közelíti. Ötvözi az elsőrendű momentumot egy korrigált másodrendű sebességgel, amely Adam-stílusú momentumokat és Shampoo-stílusú sajátérték-korrekciókat kombinál.

A KFAC (Kronecker-factored Approximate Curvature) módszer a Fisher-információs mátrixot két kisebb mátrix Kronecker-szorzataként faktorizálja (A ⊗ G). A KFACBlock az A_inv és G_inv inverz faktorokat tárolja.

A Hutchinson-becslő egy sztochasztikus algoritmus, amely a teljes Hessian kiszámítása nélkül becsüli meg a Hessian-mátrix diagonálisát. Rademacher-vektoros mintavételt és irányderiváltakat alkalmaz a v^T H v közelítéséhez.

A Spektrális normalizáció egy technika, amely a tanítást stabilizálja azáltal, hogy korlátozza a súlymátrixok Lipschitz-konstansát. A SpectralNormalizer hatalomiterációval becsüli a maximális szinguláris értéket és ennek megfelelően skálázza a tensort.

A TMEM (Tensor Memory) az NVIDIA Blackwell (B200) GPU-kra jellemző nagy sávszélességű, 32 MB-os on-chip memória. Kezelését a B200MemoryManager végzi, amely az access_freq alapján dönt az HBM-ből TMEM-be való előléptetésről.

A Kernel-fúzió több matematikai művelet egyetlen GPU kernel futtatásba való összevonásának folyamata a memóriasávszélességi szűk keresztmetszetek csökkentése érdekében. A B200KernelOptimizer.fuseOperations metódus a MatMul + Bias + Aktiváció mintát fused_gemm_bias_act hívássá alakítja.

A matematikai szimbólumok és kódentitások összefoglalója az alábbi táblázatban látható.

|Fogalom          |Szimbólum  |Kód implementáció    |
|-----------------|-----------|---------------------|
|Momentum         |m_t        |SFD.momentum         |
|Második momentum |v_t        |SFD.velocity         |
|Fisher-diagonális|F̂          |SFD.fisher_diagonal  |
|Rademacher       |ξ ∈ {-1, 1}|Tensor.fillRademacher|
|Hibafüggvény     |erf(x)     |erfApprox            |
|L2 norma         |‖x‖₂       |Tensor.normL2        |
