# agl — Artificial General Logic

Relation-first формальная система представления смысла. Отношения первичны,
плоскости вопроса определяют, где утверждение верно, противоречия видимы и
локализованы. LLM только предлагает, ядро проверяет. Проект личный: цель автора
— прочная и последовательная основа для собственных решений. Личные мотивы в
репозиторий **не** писать: он публичный.

## Перед любой работой прочитать

1. [docs/roadmap.md](docs/roadmap.md) — где мы и что дальше (раздел «Следующие шаги»).
2. [docs/decisions.md](docs/decisions.md) — решения автора (1–22). Их не пересматривать.
3. [docs/hypotheses.md](docs/hypotheses.md) — предложения помощника (H0–H71), **не приняты**.
4. [docs/open-questions.md](docs/open-questions.md) — что решает только автор.
5. [docs/impl/poc.md](docs/impl/poc.md) — нотация `.agl`, семантика ядра, детерминизм, рефлексия, обучение.

Остальное:
- [docs/glossary.md](docs/glossary.md) — словарь: как называется в науке то, о чём речь;
- [docs/mechanisms.md](docs/mechanisms.md) — сводная карта механизмов и связок между ними;
- `docs/cases/` — казусы на бумаге: Ньютон, гексокиназа, газообмен, «Праведные», родство;
- `docs/blind/` — слепые прогоны: агент и 4 модели;
- `docs/dsl/` — LLM пишет `.agl`: прогон DeepSeek V4.1 Flash, скрытый учитель;
- `docs/lessons/` — основания математики (из чего строить всё), дистилляция реализаций (изоморфизм, Фробениус, вид); нейронаука, методологии обучения XX века, пучки и топосы, как мыслители описывают поиск недостающего, как находят способ ответа (Джанибеков, Пуанкаре, Гамильтон, сон), генетический метод, расширение понятия числа (Бомбелли, Пикок, Ганкель, Гильберт и Фреге), основания математики (алгебра отношений, Бурбаки), закрепление выведенного (леммы, полезность, консолидация);
- `docs/review/` — критический разбор, оценка объёма данных;
- `docs/origin/` — исходные заметки, не редактируются.

## Правила работы

- **Язык документов — русский**; код, идентификаторы и коммиты — английский.
- **Решение принимает только автор.** Предложение помощника — гипотеза в
  `hypotheses.md` со следующим номером. В `decisions.md` оно переносится только
  по прямому слову автора, с его формулировкой. Молчание автора — не согласие.
- **Полный детерминизм** (решение 18):
  - никаких `HashMap`/`HashSet` и часов;
  - вся случайность — от seed (`src/sim.rs`);
  - вывод не зависит от порядка утверждений.

  Симуляционные тесты (`tests/sim.rs`) ловят зависимость от порядка и
  детерминизм (нашли 4 ошибки, см. poc). Правильность вывода сверяет эталон
  defeasible logic (`tests/oracle.rs`): он нашёл ошибки К1 и К3 разбора.
- Сеть трогают только загрузчики (`tools/`). Их выход коммитится вместе с
  MANIFEST хешей, ядро работает офлайн.
- Ядро без внешних зависимостей. Rust 2024 edition, `cargo fmt`, `cargo clippy` чисто.
- Автор разрешил помощнику писать код и коммитить с пушем в `main`
  (github.com/heaprip/agl, публичный). Коммиты заканчиваются строкой
  `Co-Authored-By` из системных указаний.

## Команды

```sh
cargo test --release                       # всё; ~20 с
AGL_SIM_SEEDS=20000 cargo test --release --test sim   # широкий прогон
AGL_SEED=<n> cargo test --test sim         # повтор упавшего seed
AGL_SIM_SEEDS=50000 cargo test --release --test oracle  # сверка ядра с эталоном DL
cargo run --release -- cases/*.agl         # казусы
cargo run --release -- -v cases/trunk/oxygen.agl      # с цепочками вывода
cargo run --release -- --diagnose FILE     # рефлексия R1
cargo run --release -- --propose FILE      # рефлексия R2
cargo run --release -- --learn viable cases/learning/viability.agl
cargo run --release -- --concepts cases/kinship.agl  # разложение понятий: уровни, порядок, общий род
cargo run --release -- --where "mother(ego: ?e, alter: ?a)" cases/kinship.agl  # где верно
cargo run --release -- --implications cases/kinship.agl  # что с чем связано по плоскостям
python3 tools/llm_dsl.py run 3              # LLM пишет .agl; вызовы воспроизводятся из docs/dsl/calls
uv run --python 3.11 --with memote==0.17.0 --with cobra==0.32.1 tools/memote_ref.py build  # казусы memote
python3 tools/trunk.py build               # ствол и классы ChEBI из data/raw (офлайн); fetch, fetch-classes — из сети
python3 tools/onto_stats.py stats         # форма ChEBI и WordNet (H61): роды, пути, интервалы, изменения между выпусками
python3 tools/onto_stats.py replay        # H61: правки между выпусками на трёх формах номера (~15 с)
python3 tools/onto_stats.py releases chebi 244 255 > target/scratch/chebi2.agl && cargo run --release -- target/scratch/chebi2.agl  # H61 шаг 7: ChEBI целиком, два выпуска — две плоскости (~5 с, 1,6 ГБ)
python3 tools/onto_stats.py axes 255 > target/scratch/axes.agl && cargo run --release -- target/scratch/axes.agl  # H61 шаг 4: две оси, строение и роль (~3 с)
python3 tools/onto_stats.py fca chebi 255 target/scratch/fca255 && cargo run --release --example fca -- target/scratch/fca255  # H61 шаг 5а: объём и содержание битами (~30 с); второй каталог — проверка следующим выпуском
python3 tools/llm_geometry.py fetch       # матрицы выхода Qwen2.5 0.5B–72B в data/cache/llm (~6 ГБ, вне git)
uv run --python 3.12 --with numpy==2.2.6 tools/llm_geometry.py run [noise]  # H62: векторы понятий против WordNet (~5 мин)
cargo run --release --example labels -- target/scratch/chebi255.tsv  # H61: метки вложенности; рёбра — tools/onto_stats.py edges chebi 255
AGL_SIM_SEEDS=20000 cargo test --release --test nesting  # `nesting` против двух правил: отчёты побайтно
python3 tools/onto_stats.py probe wordnet 2025 lazy > target/scratch/wn.agl && cargo run --release -- target/scratch/wn.agl  # WordNet в ядре (H61, 2б)
cargo run --release --example analogy      # прототип H51: недостающая реакция по аналогии
cargo run --release --example bombelli     # веха Джанибекова, шаг 0: аномалия → плоскость пар (AGL_TRACE=1 — ход)
cargo run --release --example cauchy       # H57 шаг 2: присоединение корня, выбор X² = s по аномалии
cargo run --release --example adjoin -- cases/discovery/adjoin/imaginary.agl  # H57 шаг 3: один приём присоединения
cargo run --release --example hamilton    # H57 шаг 4: какой закон снять — кватернионы (~30 с)
```

## LLM через RouterAI

- Ключ — `ROUTERAI_KEY` и `ROUTERAI_BASE_URL` в `/Users/user/Projects/python/trading/.env`.
  Ключ **общий с торговым ботом автора**: перед прогоном проверить баланс
  (`GET $BASE/credits`), значения ключа не печатать.
- **Провайдера закреплять.** Цена в каталоге — у самого дешёвого провайдера, а
  обслуживать может дорогой: DeepSeek V4 Pro у провайдера DeepSeek стоил в 5 раз
  дороже каталожной цены. Закрепление:
  `provider: {order: [...], allow_fallbacks: false}`; цены по провайдерам —
  `GET $BASE/models/<id>/endpoints`.
- Прошлые прогоны и скрипты — `docs/blind/models/` (промпт и ответы). Скрипты
  лежали во временной папке и не сохранились; формат запроса — OpenAI-совместимый
  `/chat/completions` с `usage: {include: true}`.
