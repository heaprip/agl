# agl — Artificial General Logic

Relation-first формальная система представления смысла. Отношения первичны,
плоскости вопроса определяют, где утверждение верно, противоречия видимы и
локализованы. LLM только предлагает, ядро проверяет. Проект личный: цель автора
— прочная и последовательная основа для собственных решений. Личные мотивы в
репозиторий **не** писать: он публичный.

## Перед любой работой прочитать

1. [docs/roadmap.md](docs/roadmap.md) — где мы и что дальше (раздел «Следующие шаги»).
2. [docs/decisions.md](docs/decisions.md) — решения автора (1–22). Их не пересматривать.
3. [docs/hypotheses.md](docs/hypotheses.md) — предложения помощника (H0–H41), **не приняты**.
4. [docs/open-questions.md](docs/open-questions.md) — что решает только автор.
5. [docs/impl/poc.md](docs/impl/poc.md) — нотация `.agl`, семантика ядра, детерминизм, рефлексия, обучение.

Остальное:
- `docs/cases/` — казусы на бумаге: Ньютон, гексокиназа, газообмен, «Праведные»;
- `docs/blind/` — слепые прогоны: агент и 4 модели;
- `docs/dsl/` — LLM пишет `.agl`: прогон DeepSeek V4.1 Flash, скрытый учитель;
- `docs/lessons/` — нейронаука, методологии обучения XX века;
- `docs/review/` — критический разбор;
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

  Симуляционные тесты (`tests/sim.rs`) — главный ловец ошибок, уже нашли 7
  настоящих.
- Сеть трогают только загрузчики (`tools/`). Их выход коммитится вместе с
  MANIFEST хешей, ядро работает офлайн.
- Ядро без внешних зависимостей. Rust 2024 edition, `cargo fmt`, `cargo clippy` чисто.
- Автор разрешил помощнику писать код и коммитить с пушем в `main`
  (github.com/heaprip/agl, публичный). Коммиты заканчиваются строкой
  `Co-Authored-By` из системных указаний.

## Команды

```sh
cargo test --release                       # всё; ~1 мин
AGL_SIM_SEEDS=20000 cargo test --release --test sim   # широкий прогон
AGL_SEED=<n> cargo test --test sim         # повтор упавшего seed
cargo run --release -- cases/*.agl         # казусы
cargo run --release -- -v cases/trunk/oxygen.agl      # с цепочками вывода
cargo run --release -- --diagnose FILE     # рефлексия R1
cargo run --release -- --propose FILE      # рефлексия R2
cargo run --release -- --learn viable cases/learning/viability.agl
python3 tools/llm_dsl.py run 3              # LLM пишет .agl; вызовы воспроизводятся из docs/dsl/calls
python3 tools/trunk.py build               # ствол из data/raw (офлайн); fetch — из сети
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
