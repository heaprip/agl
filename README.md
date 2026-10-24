# Artificial General Logic

Relation-first система представления смысла. Отношения первичны, устойчивые
сущности выводятся из сети отношений. LLM только предлагает кандидатов,
формальное ядро их проверяет. Противоречия не запрещены, а видимы и
локализованы — по плоскостям вопроса и по веткам интерпретации.

**Состояние:** PoC метаядра v0 на Rust, без зависимостей. Пять казусов
исполняются (Ньютон, гексокиназа, газообмен, «Праведные», корабль Тесея): `cargo run -- cases/*.agl`. Тесты — `cargo test`; среди них
детерминированные симуляционные тесты по seed. Семантика и ограничения —
[impl/poc](docs/impl/poc.md).

**Первый ствол — гликолиз** из Rhea и ChEBI: `python3 tools/trunk.py build &&
cargo run --release -- cases/trunk/glycolysis.agl`. Где мы — [roadmap](docs/roadmap.md).

## Документы

| Документ | Что в нём | Кто автор |
| --- | --- | --- |
| [vision](docs/vision.md) | зачем проект и что считать успехом | автор |
| [decisions](docs/decisions.md) | принятые решения | только автор |
| [hypotheses](docs/hypotheses.md) | рабочие гипотезы H0–H36 | помощник, **не принято** |
| [open-questions](docs/open-questions.md) | вопросы, которые решает только автор | — |
| [cases/newton](docs/cases/newton.md) | первый казус и журнал нагрузки на ядро | помощник, черновик |
| [cases/glycolysis-hexokinase](docs/cases/glycolysis-hexokinase.md) | второй казус: первый шаг гликолиза | помощник, черновик |
| [cases/gas-exchange](docs/cases/gas-exchange.md) | третий казус: газообмен у человека, рыбы, насекомого, птицы | помощник, черновик |
| [cases/les-justes](docs/cases/les-justes.md) | четвёртый казус: «Праведные», первый моральный | помощник, черновик |
| [blind/models-comparison](docs/blind/models-comparison.md) | тот же слепой прогон на DeepSeek V4 Pro, Beam 1.0, Ling 3.1 Flash, LFM2.5 | помощник, черновик |
| [blind/comparison](docs/blind/comparison.md) | слепой прогон (Тесей, Хемингуэй) против метаядра agl | помощник, черновик |
| [roadmap](docs/roadmap.md) | путь к первому самостоятельному стволу и где мы на нём | помощник |
| [impl/poc](docs/impl/poc.md) | реализация PoC: нотация, семантика, детерминизм, симуляционные тесты | помощник |
| [lessons/education](docs/lessons/education.md) | методологии обучения XX века и чего agl не хватает как ученику | помощник |
| [lessons/neuro](docs/lessons/neuro.md) | прочитанные статьи по нейронауке и что из них взято | помощник |
| [review/2026-10-23](docs/review/2026-10-23-analysis.md) | критический разбор обсуждения | агент-рецензент |
| [origin](docs/origin/relation-first-system.md) | исходные заметки, не редактируются | автор |

Правило ведения: решение принимает только автор. Гипотеза становится решением
только по его слову и переносится из `hypotheses` в `decisions`.

Лицензия: код — Apache 2.0 ([LICENSE](LICENSE)), документы — CC BY 4.0
([docs/LICENSE](docs/LICENSE)). Сторонние данные (ChEBI, Rhea, Open English
WordNet, BiGG) — под своими лицензиями, см. [NOTICE](NOTICE).
