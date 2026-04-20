Reversible Scatter Flow (RSF) Architektúra – Teljes dokumentáció (Magyar)

> Forrás: https://deepwiki.com/kollarsandor/Reversible-Scatter-Flow-RSF-Architecture  
> Generálva: 2026-04-11

---

 Áttekintés

A Reversible Scatter Flow (RSF) architektúra az ötödik gyökérszintű neurális architektúra, amelyet invertálható csatolási primitívek köré terveztek, a hagyományos perceptronok, konvolúciók vagy figyelemmechanizmusok helyett. Az RSF modell minden rétege bijektív transzformáció, ami biztosítja, hogy a teljes hálózat matematikailag megfordítható legyen – a kimenetek lebegőpontos pontossággal visszaalakíthatók bemenetekre.

A rendszer egy nagy teljesítményű, formálisan verifikált stackre épül, amelynek alapja a Zig programozási nyelv a futásidő kezeléséhez, valamint a Futhark az adatpárhuzamos GPU gyorsításhoz.

 Alaptervezési elvek

Az RSF architektúra három fő mérnöki pilléren alapul:

1. Bijektív transzformációk: Az információt megsemmisítő műveletek (pl. ReLU, Pooling) helyett RSF affin csatolási rétegeket használ. Ezek az állapotot két félre osztják, ahol az egyik fél a másikat tanult skálázási és eltolási paramétereken keresztül transzformálja.
2. O(1) memória-visszaterjesztés: Mivel minden réteg megfordítható, a közbülső aktivációkat nem kell eltárolni a forward pass során. A backward pass menet közben rekonstruálja a szükséges állapotokat, ezzel jelentősen csökkentve a GPU-memória terhelését.
3. Formális verifikáció: Az alaplogika több bizonyítási asszisztensen (Twelf, Beluga, Lean 4, Mizar) át van ellenőrizve, hogy garantálja az invertálhatóságot, az alakbiztonságot és a memóriabiztonságot (use-after-free és double-free megelőzése).

 Részrendszerek integrációja

- Zig Runtime: A rendszer „agya", amely az RSFCore regisztryt kezeli, a modell perzisztenciáját (.rsf fájlok betöltése/mentése) intézi, és a végrehajtást koordinálja.
- Futhark GPU Kernels: Az affin csatolási rétegek és optimalizálók nagy teljesítményű implementációját biztosítja. NVIDIA vagy OpenCL-kompatibilis hardveren való futtatáshoz C kódot generál, amelyet a Zig linkel.
- Elosztott tanítás: Egy réteg, amely a több GPU-s koordinációt NCCL kollektív kommunikáció és Modal felhőalapú skálázás segítségével kezeli.
- Formális bizonyítások: Géppel ellenőrzött bizonyítások összessége, amelyek garantálják, hogy az elméleti definíciók megegyeznek az implementációval.

---

 Architektúra elvek

Az RSF minden rétegben bijektív csatolási primitívekre épülve O(1) memória-komplexitást tesz lehetővé a visszaterjesztés során, és garantálja az állapot pontos rekonstrukcióját.

 A csatolási művelet

A számítás alapegysége az affin csatolási réteg. Adott $[x_1, x_2]$ bemenet esetén:

1. Skálaszámítás: $\text{scale} = \exp(\text{clip}(W_s \cdot x_2 + b_s))$
2. Eltolásszámítás: $\text{trans} = W_t \cdot y_1 + b_t$
3. Csatolás alkalmazása: $y_1 = x_1 \odot \text{scale}$, $y_2 = x_2 + \text{trans}$

 A scatter művelet

Annak érdekében, hogy minden dimenzió interakcióba lépjen, az RSF scatter műveleteket (rsf_scatter) alkalmaz a csatolási rétegek között. Ez biztosítja, hogy az $x_1$-ből származó információ végül befolyásolja az $x_2$ transzformációját a következő rétegekben.

 Mérnöki elvek

O(1) memória-komplexitás: A standard architektúrákkal ellentétben az RSF megfordítható visszaterjesztést alkalmaz. Mivel minden réteg bijektív, egy réteg bemenete rekonstruálható a kimenetéből a backward pass során. Ez a memória-terhelést O(L)-ről O(1)-re csökkenti.

Numerikus biztonság: Strict levágás clip_min és clip_max értékekkel (alapértelmezetten [-5, 5]) érvényesül mind a Futhark GPU kernelekben, mind a Zig runtimeban.

Miért RSF? A standard architektúrák (CNN-ek/Transformer-ek) veszteségesek, az RSF bijektív természete biztosítja: nincs információveszteség, hardver-hatékonyság (összevont kernel-frissítések), és formális helyesség (géppel ellenőrzött bizonyítások).

---

 Első lépések és build rendszer

 Rendszerkövetelmények

- Zig Toolchain: 0.11.0 vagy újabb
- Futhark Compiler: .fut kernel forrásfájlok fordításához optimalizált C kódba
- GPU Driverek: NVIDIA GPU CUDA Toolkit 11.0+ (ajánlott), vagy OpenCL alternatíva
- C Compiler: gcc vagy clang

 Build pipeline


.fut forráskód → Futhark compiler → generált C kód → Zig linker → bináris


 Futhark függőségkezelés

A projekt futhark.pkg fájlt használ a diku-dk/sorts csomaghoz, amely optimalizált GPU-oldali rendezési műveleteket biztosít. Szinkronizálás:

futhark pkg sync


 Kernel belépési pontok

- futhark_entry_rsf_forward: Kiszámítja az affin csatolási transzformációt
- futhark_entry_rsf_backward: Kiszámítja a súlyok és torzítások gradienseit
- futhark_entry_training_step: Összevont kernel a teljes optimalizáló frissítéshez

 Linkelés és futtatás

bash
 C kernelgenerálás
futhark cuda --library accel/main.fut

 Fordítás Ziggel
zig build -Doptimize=ReleaseFast


---

 Core RSF Modell (Zig Runtime)

A Core RSF Modell réteg a Reversible Scatter Flow architektúra central vezérlési csomópontjaként szolgál. Zigben implementálva, ez a réteg kezeli a modell életciklusát, koordinál a CPU-alapú logika és a GPU-gyorsított kerneleken között, és felügyeli a pontos megfordíthatósághoz szükséges matematikai invariánsokat.

 Rendszeráttekintés

A Zig runtime egy handle/core registry mintára épül. A magas szintű handle-ek (RSF, RSFLayer) stabil API-t biztosítanak, míg a belső Core struktúrák (RSFCore, LayerCore) tartják a tényleges tenzor adatokat és állapotot.

 Forward, inverz és backward passzok összefoglalása

| Művelet | Logika | Memória-komplexitás |
|---|---|---|
| Forward | $y = x_2 \odot \exp(s(x_1)) + t(x_1)$ | O(L) |
| Inverz | $x_2 = (y - t(x_1)) \odot \exp(-s(x_1))$ | O(L) |
| Backward | Aktivációkat rekonstruálja a kimenetből a gradiens-számításhoz | O(1) |

 Végrehajtás megoszlása (CPU/GPU)

1. Validáció: Az rsf.zig érvényesíti a tenzor alakokat és véges értékeket
2. Memória-leképezés: A tenzorok GPU-memóriára vannak leképezve az accel interfészen keresztül
3. Kernel-meghívás: A runtime aktiválja a Futhark által generált C-bindingokat (pl. rsf_forward, rsf_backward)

---

 RSF Modell életciklusa és registry

 Handle/Core Registry minta

| Struktúra | Szerep |
|---|---|
| RSF | A modell legfelső szintű handle-je |
| RSFCore | A modell belső állapota, LayerCore objektumok tömbjével |
| RSFLayer | Handle egy egyes csatolási réteghez |
| LayerCore | Tényleges Tensor adatok: súlyok, torzítások, gradiensek |

 Szálbiztos megszerzés és életciklus

- acquireCore(): Növeli a belső referencia-számlálót
- releaseCore(): Csökkenti. Ha nullára csökken és meg van jelölve törlésre, a memória felszabadul
- std.Thread.RwLock: Biztosítja, hogy a súlyfrissítések (írások) nem ütköznek a forward/inverz pass-ekkel (olvasások)

 Inicializáció és törlés

Allokáció előtt: validateClipRange (értékek [-20.0, 20.0]-ban) és validateModelConfigValues (dimenziók és rétegszámok ellenőrzése). A modell inicializálása szigorú „mindent-vagy-semmit" mintát követ errdefer-rel.

Teardown sorrendje: LayerCore teardown → RSFCore teardown → Handle nullázás.

---

 Forward, inverz és backward pass-ek

 Matematikai primitívek

Az affin csatolási réteg adott $[x_1, x_2]$ bemeneten:

1. $s = \exp(\text{clip}(W_s \cdot x_2 + b_s))$
2. $y_1 = x_1 \odot s$
3. $t = W_t \cdot y_1 + b_t$
4. $y_2 = x_2 + t$

 Forward pass implementáció

A ForwardInPlace helyben frissíti a két y1 és y2 tenzort. A skálát clip_min és clip_max között vágja le (alapérték [-5, 5]) az exponencializálás előtt. Az allokáció minimalizálásához az input puffereket outputként újrahasznosítja.

 Inverz pass implementáció

Az InverseInPlace pontosan megfordítja a forward transzformációt, a súlymátrixok invertálása nélkül:
1. Kiszámítja a $t$ eltolást $y_1$-ből, kivonja $y_2$-ből → visszanyeri $x_2$
2. Kiszámítja az $s$ skálát a visszanyert $x_2$-ből, elosztja $y_1$-et $s$-szel → visszanyeri $x_1$

 Backward pass és gradiens akkumuláció

A BackwardOnCore kiszámítja a gradienseket a bemeneti adatokhoz és a modell paramétereihez. Pufferek: dy1_total (gradiensek $y_1$-en), ds (közbülső skálagradiens). Levágott értékeknél a gradiens nullázódik az instabil frissítések megelőzéséhez.

Kódentitás-leképezés:

| Matematikai fogalom | Zig entitás |
|---|---|
| Affin csatolás | ForwardInPlace |
| Pontos megfordítás | InverseInPlace |
| Gradiens akkumuláció | BackwardOnCore |
| Súlytároló | LayerCore |
| Levágási tartomány | RSFLayerConfig |
| Véges értékellenőrzés | ensureFiniteSlice |

---

 Modell perzisztencia és checkpointing

 Sorosítási formátum (RSF0)

Egyéni bináris formátum, aktuális verziószám: 4 (SAVE_VERSION).

Header:

| Eltolás | Típus | Mező |
|---|---|---|
| 0 | [4]u8 | Magic = RSF0 |
| 4 | u32 | Version = 4 |
| 8 | u64 | Dimension |
| 16 | u64 | Layers |
| 24 | f32 | Clip Min |
| 28 | f32 | Clip Max |
| 32 | u8 | Grad Mean |
| 33 | [7]u8 | Padding |
| 40 | u32 | CRC32 |

Payload sorrendje rétegenkénti: s_weight, t_weight, s_bias, t_bias – nyers f32 tömbként.

 Atomi írási stratégia

1. SavedModelSnapshot – konzisztens pillanatnézet a súlyokról
2. Ideiglenes fájlba írás (pl. model.bin.tmp)
3. CRC32 ellenőrzőösszeg számítása
4. Flush és fsync
5. Atomi átnevezés std.fs.Dir.rename-mel

 Betöltési validáció

Magic/Verzió ellenőrzés → Dimenzió-validáció → Ellenőrzőösszeg-verifikáció → ensureFiniteSlice (NaN/Inf keresés).

---

 OFTB: Ortogonális Fraktál Transzformációs Blokk

Az OFTB szimmetrikus pillangó-stílusú keverési műveletet valósít meg, biztosítva az információáramlást a látens tér összes dimenziójában. Rögzített súlyú, ortogonális transzformáció.

 Főbb tulajdonságok

- Szimmetria: Mindkét felet szimmetrikusan kezeli pillangó-keverési mintával
- Skálainvariancia: fractal_scale ≈ $1/\sqrt{2}$ a jel energiájának megőrzésére
- Memória-hatékonyság: Stack-puffereken működik, heap allokáció nélkül

 Forward és backward logika

Forward: Az $x_1$ értékei pufferelve; $x_1$ frissül: $x_1 += x_2 \cdot \text{fractal\_scale}$; $x_2$ frissül a pufferelt $x_1$ alapján: $x_2 += \text{buf} \cdot \text{fractal\_scale} \cdot 0.5$.

Backward: Tükrözi a forward pass-t, hasonlóan stack-puffert alkalmazva közbülső gradiens állapotokhoz.

 Technikai korlátok

| Korlát | Érték |
|---|---|
| Stack puffer limit | 16 384 |
| Bemeneti méret | dim  2 |
| Skálafaktor | ~0.7071 ($1/\sqrt{2}$) |

 Integráció scatter primitívként

Az OFTB biztosítja a szükséges lineáris keverést, hogy minden dimenzió végül minden más dimenzióra hasson, megelőzve a „dead channel" problémát a naiv csatolási architektúráknál.

---

 GPU Gyorsítási Réteg

A GPU gyorsítási réteg négy komponensből áll:

1. Futhark Kernels – matematikai mag (rsf_flow, rsf_scatter, rsf_backward_layer)
2. RSFAccelerator interfész – FutharkContext életciklus és memória-biztonságos burkolók
3. CUDA memóriakezelés – cudaHostAlloc pinned memória DMA átvitelekhez
4. Fractal LPU – hierarchikus ütemező quad-tree (FractalTile) struktúrával

 Hibajelzési stratégia

| Hibakód | Eredet |
|---|---|
| FutharkSyncFailed | futhark_context_sync |
| CudaHostAllocFailed | cudaHostAlloc |
| FutharkArrayNewFailed | futhark_new_ |
| InvalidDimensions | Zig Runtime |

---

 Futhark Kernelok

Az RSF architektúra GPU gyorsítási kernelei két fő Futhark fájlban vannak implementálva.

 RSF csatolási logika

Forward pass: Skála = $\exp(s\_bias + s\_weight \cdot x_2)$; eltolás = $t\_bias + t\_weight \cdot y_1$; $y_1 = x_1 \odot \text{scale}$, $y_2 = x_2 + \text{trans}$.

Backward pass: Nem igényli a közbülső aktivációk tárolását – rekonstruálja őket és kiszámítja a $\nabla w_s, \nabla w_t, \nabla b_s, \nabla b_t$ gradienseket.

 Batch műveletek és tanítási lépés

training_step összevont kernel:
1. batch_forward – jóslatok kiszámítása
2. batch_compute_loss – MSE kiszámítása
3. batch_gradients – súlyfrissítések kiszámítása
4. Momentum-alapú optimalizáló frissítés

 R-GPU gráf és hardver szimuláció

- rgpu_fractal_dim: A routing gráf komplexitásának kiszámítása
- rgpu_canonical_signature: Egyedi bit-aláírás a hierarchiában
- score_segments + topk: Hash-alapú pontszámítás és Top-K kiválasztás radix rendezéssel

 Segédkernelok

- xavier_fill_inplace: Xavier/Glorot egyenletes inicializáció
- matmul_tiled / batched_matmul: Optimalizált mátrixszorzás
- rsf_scatter: Keverési művelet $1/\sqrt{2}$ skálafaktorral
- spectral_clip: Fisher-információs mátrix levágása
- dot_product: NaN-toleráns skaláris szorzat

---

 Futhark Bindingok és RSFAccelerator interfész

 Futhark bindingok (FFI réteg)

Tömb handle típusok: f16 (csatolási rétegekhez), f32 (mátrixműveletekhez), u64/i64 (indexeléshez).

Belépési pontok:
- futhark_entry_rsf_forward
- futhark_entry_rsf_backward
- futhark_entry_matmul
- futhark_entry_training_step

 RSFAccelerator interfész

FutharkContext:

| Függvény | Cél |
|---|---|
| init() | Konfigurációt allokál, alapértelmezett csoportméret (256) és csempéméret (32) |
| sync() | CPU blokkolása az összes GPU-művelet befejezéséig |
| getDataPointer() | Nyers pointer lekérése az interophoz |

FutharkArray burkolók: newFromFlat (CPU → GPU), values1D/values2D (GPU → CPU), free (explicit GPU-memória felszabadítás).

A súlyok tanítás közben GPU-n tarthatók FutharkArray2DF16 objektumként, az futhark_entry_scale_weights_inplace in-place skálázással, minimalizálva a PCIe terhelést.

---

 CUDA Bindingok és memóriakezelés

 CUDA hibakezelés

| Zig hiba | CUDA konstans |
|---|---|
| InvalidValue | cudaErrorInvalidValue |
| MemoryAllocation | cudaErrorMemoryAllocation |
| LaunchFailure | cudaErrorLaunchFailure |
| InvalidDevice | cudaErrorInvalidDevice |

 Memóriakezelés és DMA

Eszközmemória: cudaMalloc / cudaFree – GPU VRAM-ján, modell súlyokhoz és gradiensekhez.

Pinned (lapzárolt) host memória: cudaHostAlloc jelzőkkel:
- cudaHostAllocDefault: Standard lapzárolt memória
- cudaHostAllocMapped: CUDA cím-térbe leképezve
- cudaHostAllocWriteCombined: CPU által csak írható erőforrásokhoz

A pinned memória lehetővé teszi a cudaMemcpyAsync-ot, hogy a CPU és GPU átvitel párhuzamosan futhasson.

 Stream és eszközkezelés

- cudaSetDevice / cudaGetDevice: Specifikus GPU megcélzása
- cudaStream_t: Aszinkron műveletek sorozatainak nyomon követése
- cudaStreamSynchronize: Adott stream befejezéséig blokkol
- cudaDeviceSynchronize: Az aktuális eszköz összes feladatáig blokkol

---

 Fractal LPU: Hierarchikus számítási ütemező

A Fractal Logical Processing Unit (LPU) rekurzív quad-tree struktúrán keresztül kezeli a masszív skálájú párhuzamosságot, áthidalva az SSRG csomópont-leképezések és a fizikai hardver végrehajtása közötti szakadékot.

 FractalDimensionConfig

- hausdorff_dim: A számítási leképezés elméleti sűrűsége
- box_counting_levels: Maximális quad-tree rekurzió mélység
- coherence_threshold: Szükséges jelstabilitás az aktív csempéhez
- min_tile_size / max_tile_size: Egyes szegmensek memória-tárhelyének határai

 Csomópont-leképezési stratégia

1. A node_hash rögzítve az entanglement_map-be
2. Célzott ComputeUnit: node_hash % compute_units.len
3. Az egység pending_ops számlálója növekszik

A balanceLoad terheléskiegyenlítés: átlagos pending_ops kiszámítása az összes egységre, kirívó értékek levágása a load_balance_factor alapján.

 Rögzített pontos batch-végrehajtás

16.16 fixpontos aritmetika a determinisztikus eredményekhez:
1. Koherencia (0.0–1.0) → 16 bites egész: koherencia  65536.0
2. Bemeneti adatok darabolása a ComputeUnit-ok száma szerint
3. Telítési levágással 32 bites tartományra

 Rekurzív inicializáció

A subdivide hívásakor a szülőcsempe négy gyermeket hoz létre, mindegyik örökli az base_addr egy részét és csökkentett coherence értéket (szülő 90%-a). A deinit rekurzív bejárás, amely helyes sorrendben szabadít fel minden erőforrást.

---

 Elosztott tanítás

Az RSF architektúra nagy teljesítményű elosztott tanítást támogat adatpárhuzamos megközelítéssel és delta-átlagolással.

 Infrastruktúra áttekintése

1. Orchestráció: DistributedTrainer és DistributedTrainerFuthark – tanítási ciklus, adatkészlet-felosztás, modell-állapot frissítések
2. Kommunikáció: GPUCoordinator – NCCL-alapú szinkronizáció, allReduce
3. Felhőtelepítés: ModalGPUClient – Modal API-n keresztüli skálázás

 Delta-átlagolási logika

1. Lokális pillanatkép a súlyokról
2. Lokális SGD frissítés (Futhark kernel)
3. Delta = frissített súlyok − pillanatkép
4. allReduce a deltákon az összes rankon
5. Átlagolt delta visszakerül a súlyokra az összes eszközön

 Komponens-kapcsolati táblázat

| Komponens | Felelősség |
|---|---|
| DistributedTrainerFuthark | Tanítási ciklus és adatbetöltés |
| GPUCoordinator | Multi-GPU szinkronizáció |
| nccl_bindings.zig | NCCL/CUDA FFI réteg |
| ModalGPUClient | Távoli feladat végrehajtás |
| RSFAccelerator | Kernel dispatch |

---

 DistributedTrainerFuthark

A DistributedTrainerFuthark az elsődleges orchestrátor a nagy teljesítményű, több GPU-s tanításhoz.

 TrainerConfig

| Mező | Típus | Leírás |
|---|---|---|
| learning_rate | f32 | SGD lépésméret |
| momentum | f32 | Momentum együttható (ki kell kapcsolni, ha world_size > 1) |
| max_line_size | usize | Maximum pufferméret JSONL sorokhoz (alapérték 10MB) |
| checkpoint_version | u32 | Bináris pillanatfelvétel verziószám |

 Adatkészlet betöltés és rank-felosztás

1. Érvényes JSON objektumok megszámlálása a fájlban
2. samples_per_rank és start_valid_index kiszámítása az aktuális rankhoz
3. appendDatasetRange kihagyja a sorokat a rank kezdőindexéig, majd betölti a szükséges mintákat

 Elosztott tanítási lépés (Futhark)

1. Tokenizálás: Input szöveg enkódolása token ID-kra
2. Memória pinning: Tokenek másolása PinnedMemory-ba DMA átvitelhez
3. Futhark meghívás: rsf_forward és rsf_backward kernelok futtatása
4. Delta-átlagolás: Pillanatkép → lokális lépés → delta → allReduce → alkalmazás

 Checkpoint bináris elrendezés

Magic RSF0 (4 bájt) → verzió u32 → model_dim, vocab_size, global_step → nyers f16/f32 súlypufferek → CRC32 ellenőrzőösszeg. Atomi mentés: ideiglenes fájl + std.fs.rename.

---

 DistributedTrainer (Klasszikus és hibrid kvantum)

 Életciklus

- initWithConfig: Lokális RSF modell, optimalizálók beállítása
- trainEpoch: Egy átmenet az adatkészleten (mini-batch, forward/backward, súlyfrissítés)
- trainEpochHybrid: Klasszikus RSF rétegeket kvantumköri végrehajtásokkal váltogatja

 Tenzor könyvtár és COW szemantika

- TensorData: Referencia-számolt memóriablokk, nyers f32 adattal
- retain / release: Atomi műveletek (@atomicRmw) a szálbiztonságért
- Dekompozíciók: QR (súlymátrixok ortogonalizálásához), SVD (rang-redukció), Cholesky (Gauss-folyamat közelítések)

 Fixpontos aritmetika (Fixed32_32)

64 bites fixpontos típus bit-pontos reprodukálhatósághoz különböző CPU architektúrákon és GPU gyártókon. Az alsó 32 bit a töredékes rész, a init(f32) $2^{32}$-vel szoroz és kerekít.

 Hibrid kvantum tanítás

A QuantumTrainingConfig definiálja a kvantum backend paramétereket (IBM CRN konfiguráció, VQE rétegek száma). A trainEpochHybrid kvantum-specifikus metrikákat követ: áramkör mélység, gate hűség becslések, shot noise variancia.

 Matematikai műveletek

| Művelet | Leírás |
|---|---|
| matmulTiled | Cache-barát csempézéssel optimalizált mátrixszorzás |
| decomposeLU | Mátrix faktorizáció alsó és felső háromszög-mátrixokra |
| broadcastTo | NumPy-stílusú tenzor dimenzió bővítés |
| reshape | Dimenziók megváltoztatása adat másolása nélkül |

---

 GPU Koordinátor és NCCL Bindingok

 GPU Koordinátor

A GPUCoordinator az elsődleges interfész egy specifikus GPU rank kezeléséhez:

Inicializáció: cudaGetDeviceCount → rank hozzárendelés: rank % local_device_count → NCCL communicator: ncclCommInitRank → CUDA stream létrehozása.

Kollektív műveletek:
- allReduceFloat32 / allReduceFloat16: Összegzési redukció az összes rankon
- broadcastFloat32: Adatmásolás root rankról az összes rankra
- barrier: Dummy allReduce szinkronizációs ponthoz

Memória és adatfolyam:
- allocDeviceMemory / freeDeviceMemory: cudaMalloc / cudaFree burkolók
- copyHostToDevice / copyDeviceToHost: cudaMemcpyAsync-ot részesíti előnyben

 NCCL Bindingok

Támogatott kollektív műveletek:
- ncclAllReduce: GPU-k közötti összegzés
- ncclBroadcast: Root rank → összes rank
- ncclAllGather: Gyűjtés az összes rankról, összesített eredmény visszaosztása
- ncclReduceScatter: Redukció, majd szétszórás a rankok között

Típusdefiníciók: ncclDataType_t (ncclFloat16, ncclFloat32), ncclRedOp_t (ncclSum, ncclProd, ncclMax, ncclMin), ncclUniqueId (128 bájtos communicator ID).

---

 Modal Cloud GPU Kliens

 Áttekintés

A ModalGPUClient a Modal felhőinfrastruktúrára telepíti az RSF modellek tanítását:

- GPU preferenciák: B300 vagy B200 alapértelmezetten
- Skála: 8 GPU per feladat
- Környezet: jaide-v40-training konténer image

 Feladat telepítése

A deployTrainingJob POST kérést küld a Modal API-ra:

POST https://api.modal.com/v1/functions/deploy

Payload: GPU típus és szám, modell és adatkészlet elérési utak, alapértelmezett batch méret (32) és epochok (10).

Állapotkövetés: getJobStatus GET kéréssel a feladat-specifikus végpontra.

 API kompatibilitási shim

A sendRequest kompilálásidőben, @hasDecl-lel detektálja az elérhető API-t:
1. Modern API (open 5 paraméterrel): http.Headers objektum átadása
2. Közbülső API (open 4 paraméterrel): Manuális server_header_buffer és headerek hozzáfűzése
3. Legacy API (request): A régebbi metódus szignatúra

Hitelesítés: Bearer Token automatikusan az Authorization headerbe kerül; Content-Type: application/json ha body van jelen.

---

 Formális Verifikáció

Az RSF architektúra a formális helyességet elsőrendű követelményként kezeli, négy bizonyítási asszisztens stratégiájával:

- Lean 4: Magas szintű funkcionális helyesség, állapotgép-átmenetek, fixpontos aritmetika
- Twelf: Csatolási rétegek strukturális invertálhatósága, párhuzamos memória modell biztonsága
- Beluga: Alakmegőrzés, függő index-biztonság a rétegeken keresztül
- Mizar: Halmazelméleti specifikációk, bináris sorosítás elrendezése

 Verifikált tulajdonságok

| Tulajdonság | Eszköz | Célzott kódentitás |
|---|---|---|
| Invertálhatóság | Lean 4 / Twelf | ForwardInPlace, InverseInPlace |
| Alakbiztonság | Beluga | RSFConfig.maxdim, LayerCore |
| Memóriabiztonság | Twelf | RSFCore, RwLock, active_ops |
| Perzisztencia | Mizar | save, load, RSF0 Header |
| Keverési helyesség | Lean 4 | oftb.zig, fractal_scale |

---

 Lean 4 Bizonyítások

 RSF Core invertálhatósága

| Tétel | Leírás |
|---|---|
| ThForwardInverseIdentity | Bármely $x$-re: $\text{Inverse}(\text{Forward}(x)) = x$ |
| computeScaleInto_verify | A skálafaktor-számítás helyességének validálása |
| state_machine_consistency | Forward/Inverse/Backward állapotátmenetek invariáns-megőrzése |

 OFTB fixpontos pillangó bizonyítások

- forwardPass_eq_iterative_strict: Az N szakaszon átfutó pillangó implementáció megfelel a rekurzív fraktál definíciónak
- det_forward_eq_det_backward: Jacobian determináns megőrzése (kritikus flow-alapú modellekhez)
- safety_preserved_forward: OFTBState invariánsok megőrzése a transzformáción keresztül

Az OFTB Lean 4 állapota: OFTBState struktúra, fractalScale = 70710678 ($1/\sqrt{2} \times 10^8$), butterfly_op a $2 \times 2$ rotációs logika.

 Tanult embedding életciklus és biztonság

- weightIdx_no_usize_overflow: Ha vocab_size  dim < USIZE_BOUND, bármely érvényes index esetén nem lép fel túlcsordulás
- overflow_safe_any_index: Általánosított tétel az OverflowSafe struktúrára

FP (Fixed Point): 32.32 fixpontos rendszer $10^8$ skálával; listToMem: Lean listák és a Zig runtime lapos memória puffereinek megfeleltetése; EmbeddingState: embedding súlyok életciklusát rögzíti.

---

 Twelf Bizonyítások

A Twelf formalizáció az rsf.twealf fájlban ítéleteket definiál a csatolási réteg transzformációkhoz, memóriabiztonsághoz és GPU állapot-konzisztenciához.

 Aritmetikai invertálhatóság alapjai

| Ítélet | Leírás |
|---|---|
| plus M N P | $M + N = P$ |
| sub M N P | $M - N = P$ |
| add-sub-cancel | $(A + B) - B = A$ |
| sub-add-cancel | $(C - B) + B = C$ |
| times M N P | $M \cdot N = P$ |

Az add-sub-cancel tétel kritikus az InverseInPlace-hez – garantálja, hogy az eltolási komponens $t$ kivonása pontosan visszaállítja az eredeti állapotot.

 Memória modell: Registry és no-alias

A split-judgment biztosítja, hogy a tenzor felosztásakor ($x_1$, $x_2$) a két handle diszjunkt, megelőzve a versenyhelyzeteket a Futhark kernelekben.

 GPU állapot-verziózás

- gpu-sync-op: Validálja a tenzor átmenetét CPU_DIRTY → GPU_CLEAN
- weight-update-op: Formalizálja a momentum-alapú frissítést; tükrözi az active_ops számlálót és az RwLock mechanizmust

 Főszintű invertálhatósági tétel

A top-level-invertibility-theorem kimondja, hogy bármely $L_1, \dots, L_n$ rétegsorozat esetén létezik inverz műveletek sorozata. Bizonyítási struktúra: Alapeset = üres sorozat (identitás); Induktív lépés = egy affin csatolási réteg hozzáadása megőrzi az invertálhatóságot az add-sub-cancel és mul-div-cancel tételekre támaszkodva.

---

 Mizar és Beluga Bizonyítások

 Mizar halmazelméleti specifikáció

Alapvető adatstruktúrák:

| Predikátum/Függvény | Leírás |
|---|---|
| Tensor2D is valid | len(T.data) = T.rows  T.cols |
| T.at(r, c) | 1-alapú indexelés a lapos szekvenciába |
| LayerCore | Súlyok ($s$, $t$), torzítások, opcionális gradiensek |
| LC is well-formed | Dimenziókonzisztencia, levágási határok $[-20.0, 20.0]$ |

Gradiens pipeline: Gradiensek csak akkor frissíthetők, ha a LayerCore-t EnsureGradients-szel inicializálták. Xavier/Glorot: xavier_bound = sqrt(6.0 / (fan_in + fan_out)).

Bináris elrendezés: A SerializeRSF specifikálja a SAVE_VERSION = 4 értéket, garantálva, hogy az rsf.zig perzisztencia-rétege megfelel a formális specifikációnak.

 Beluga kontextuális típuselmélet bizonyítások

Registry biztonság (No Use-After-Free):

Érvényes állapotátmenetek:
- tr-acquire: Növeli az élő core referenciaszámlálóját
- tr-release-final: 1-es referenciaszám → reg-freed (ha megsemmisítésre jelölve)
- tr-destroy-zero: Azonnal felszabadít, ha referenciaszám = 0 és megsemmisítésre jelölve

A RegistryNoUseAfterFreeW tétel biztosítja: ha egy core reg-freed állapotban van, nincs elérhető tr-acquire átmenet.

Alak invariánsok:

| Tétel | Formalizálja |
|---|---|
| model-shape-inv | $Batch \times (Dim + Dim) = Full$ és $Batch \times Dim = Half$ |
| split-valid | Tenzor két egyenlő félre osztásának érvényessége |
| index-in-bounds | Bármely érvényes $B < Rows$, $D < Cols$ esetén $Idx = B \times Cols + D < \text{total}$ |

Főbb tételek:
- completeshapepreservationtheorem: A dimenziók pontosan rekonstruálódnak az InverseInPlace után
- completeindexsafetytheorem: Minden scatter/gather indexelés a lefoglalt memória határain belül van

---

 Szótár

| Fogalom | Definíció |
|---|---|
| Reversible Scatter Flow (RSF) | Bijektív csatolási rétegekre épülő neurális architektúra, O(1) memória-backpropagationnel |
| Affin csatolási primitív | Az RSFLayer alapvető matematikai művelete: split-transform-merge pipeline |
| Scatter művelet | Tanult vagy rögzített permutáció a csatolási rétegek között az információ-keverés biztosításához |
| Bijektív transzformáció | Egy-az-egyhez és szürjektív leképezés; az RSF minden rétege ilyen |
| Butterfly keverés | Rekurzív keverési stratégia az OFTB rétegekben a globális függőség eléréséhez |
| Clip gradiens | Numerikus biztonsági stratégia: nullázza a gradienseket a levágási határokon kívüli értékeknél |
| Delta-átlagolás | Elosztott tanítási technika: csak a paraméterváltozások szinkronizálódnak allReduce-on |
| Fraktálskála | A $1/\sqrt{2}$ konstans, az OFTB és Scatter műveletek energiamegőrzéséhez |
| Handle/Core Registry | Minta: publikus RSF handle kezeli a szálbiztos RSFCore-t referenciaszámlálással |
| OFTB | Orthogonal Fractal Transform Block – nem tanult keverési primitív |
| Pinned memória | Lapzárolt host-memória a GPU-ra való nagy sebességű DMA átvitelekhez |
| Spektrális természetes gradiens | Optimalizáló változat: gradienseket a Fisher-információs mátrix átlójával skálázza |
| SSRG | Sparse Scatter-Route Graph – számítási pontok gráfja a flow-ban |
| ThForwardInverseIdentity | Lean 4 tétel: inverse(forward(x)) == x bármely $x$-re |
| Registry Safety | Beluga bizonyíték: RSFCore registry megakadályozza a Use-After-Free hibákat |
| Shape Invariant | Tenzor dimenziók állandóságának garantálása a forward és backward passokon keresztül |
