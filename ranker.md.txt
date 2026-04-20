# Ranker – LSH-alapú találati rangsorolás

## Áttekintés

A Ranker a JAIDE LLM feldolgozási lánc utolsó lépése. Feladata, hogy az SSI által visszaadott jelölteket újrapontozza és sorrendbe rendezze. Ehhez LSH-paramétereket, n-gram súlyokat és szemantikai átfedési mutatókat használ, hogy a token-szekvenciák végső relevanciáját meghatározza.

## Érintett forrásfájlok

- `src/ranker/ranker.zig`
- `src/core/io.zig`
- `src/index/ssi.zig`
- `src/verification/viper/ranker.vpr`

## Felépítés

A `Ranker` struktúra a pontozáshoz szükséges állapotot kezeli, ideértve a csillapított n-gram súlyokat és az LSH hash paramétereket.

### Adatszerkezetek és konfiguráció

Inicializáláskor a rangsoroló több súlyt és hash paramétert készít elő.

#### N-gram súlyok

Az n-gram súlyok lebegőpontos értékekből álló tömbben vannak tárolva, és jellemzően `1/n` lecsengést követnek.

#### LSH hash paraméterek

A hash paraméterek két külön szorzóval készülnek, hogy a hash-ek kellően változatosak legyenek:

- `HASH_SEED_MULTIPLIER_A`
- `HASH_SEED_MULTIPLIER_B`

## Főbb konstansok

| Paraméter | Érték | Jelentés |
|---|---:|---|
| `STREAMING_BUFFER_SIZE` | 1024 | A streaming rangsoroló puffer maximális mérete. |
| `DIVERSITY_WEIGHT` | 0.3 | A tokenváltozatosság súlya a végső pontszámban. |
| `PROXIMITY_WEIGHT` | 0.3 | Az anchor tokenek közelségének súlya. |
| `BASE_SCORE_WEIGHT` | 0.4 | Az alap n-gram SSI pontszám súlya. |
| `OVERLAP_WEIGHT` | 0.3 | A lekérdezéssel való közvetlen tokenátfedés súlya. |
| `JACCARD_WEIGHT` | 0.3 | A Jaccard-hasonlóság súlya. |

## Pontozási módszer

A Ranker többféle jel alapján számol végső pontszámot. Egyszerre veszi figyelembe a szerkezeti, szemantikai és halmazelméleti jellemzőket.

### Alap szekvenciapontozás

A `scoreSequence` függvény nyers pontszámot számol a következő lépések alapján:

1. N-gram elemzés.
2. Sokféleség mérése.
3. Anchor közelség meghatározása.

#### 1. N-gram elemzés

A függvény az n-gramokon iterál, legfeljebb `num_ngrams` elemszámig. Minden n-gramhoz kiszámít egy `stableHash` értéket, majd az SSI-ből lekéri a megfelelő szegmens pontszámát.

#### 2. Sokféleség mérése

A Ranker meghatározza az egyedi tokenek és az összes token arányát. Ehhez belső `AutoHashMap` struktúrát használ.

#### 3. Anchor közelség

A rendszer azt is méri, milyen közel vannak a tokenek az SSI indexben tárolt anchor pontokhoz.

### Lekérdezésalapú újrarangsorolás

Ha van megadott lekérdezés, a `scoreSequenceWithQuery` az alap pontszámot további jellemzőkkel egészíti ki.

#### Kiegészítő tényezők

- közvetlen tokenátfedés a lekérdezéssel
- Jaccard-hasonlóság
- az alap szekvenciapontszám finomhangolása

## Megvalósítási részletek

### LSH és n-gram feldolgozás

A Ranker a `stableHash` függvényt használja arra, hogy az n-gram szeleteket kulccsá alakítsa az SSI-keresésekhez. Az n-gram ciklus súlycsökkentést alkalmaz, hogy a hosszabb, specifikusabb n-gramok megfelelően járuljanak hozzá a pontszámhoz.

### Streaming puffer

Valós idejű futásnál a Ranker streaming módban is működhet. Ilyenkor egy csúszó tokenablakot tart fenn, és folyamatosan értékeli a keletkező szekvenciákat.

### SSI-integráció

A Ranker szorosan kapcsolódik a `src/index/ssi.zig` modulhoz. Az `SSI.getSegment` hívással előre kiszámított pontszámokat és metaadatokat kér le, például anchor jelöléseket.

### Entitáskapcsolati térkép

A rangsorolás során a rendszer nemcsak a szekvenciák pontszámát, hanem a tokenek közötti kapcsolati mintákat is figyelembe veszi.

## Formális verifikáció

A Ranker memória- és invariánshelyességét Viper-specifikáció ellenőrzi. A `src/verification/viper/ranker.vpr` fájl olyan predikátumokat tartalmaz, amelyek biztosítják a struktúra konzisztens állapotát.

### Fontosabb verifikációs elemek

| Elem | Leírás |
|---|---|
| `valid_ranker` | Ellenőrzi, hogy az `ngram_weights` és az `lsh_hash_params` megfelelően vannak lefoglalva, és hosszuk megegyezik a belső számlálókkal. |
| Matematikai axiómák | Lebegőpontos műveletekhez, minimum–maximum logikához és a hash-elés bitműveleteihez használt szabályok. 
