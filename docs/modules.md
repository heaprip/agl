# Реестр модулей

Каждый файл `src/*.rs` и `examples/*.rs` обязан иметь строку здесь — это
четыре строки предохранителя [architecture §8](architecture.md) в виде
таблицы. `tests/registry.rs` падает, если файл есть, а строки нет (или
наоборот). Хук сессии не даёт создать новый модуль без строки.

Новый модуль = новая строка **до** кода. Если ответа на «почему отдельный»
нет — значит, это не новый модуль, а расширение существующего.

Статусы:

- **ядро** — исполняет вывод ядра;
- **носитель** — общие типы и запись (metacore);
- **вид** — отчёт или проекция над результатами ядра;
- **боковой мир** — свой вычислитель рядом с ядром (H72–H75), пишет в
  носитель только результаты; по [entities](entities.md) §2.19 должен стать
  миром самого ядра;
- **внешний опыт** — пример или эксперимент, не продвижение ядра.

| Модуль | Статус | Объект контракта | Переиспользует | Почему отдельный | Сквозной тест |
| --- | --- | --- | --- | --- | --- |
| `src/lib.rs` | ядро | — | — | корень крейта | все |
| `src/main.rs` | вид | CLI | `check::run` | точка входа | `tests/cases.rs` |
| `src/model.rs` | ядро | атом, факт, правило, плоскость (`Plane`) | — | модель программы | `tests/cases.rs` |
| `src/parse.rs` | ядро | нотация `.agl` | `model` | разбор текста | `tests/cases.rs` |
| `src/plane.rs` | ядро | оси и вложение значений | `model::Plane` | алгебра плоскостей | `tests/oracle.rs`, `tests/sim.rs` |
| `src/eval.rs` | ядро | вывод, основания (G) | `model`, `plane`, `meta::{Entity, Evidence}` | неподвижная точка и DL | `tests/oracle.rs`, `tests/sim.rs` |
| `src/check.rs` | ядро | противоречия на пересечениях, запросы | `eval` | весь прогон программы | `tests/cases.rs` |
| `src/lint.rs` | ядро | статические проверки | `model` | до вычисления | `tests/cases.rs` |
| `src/units.rs` | ядро | алгебра размерностей (решение 23; по решению 28 — наружу) | `model` | размерности | `tests/cases.rs` |
| `src/sim.rs` | ядро | seed (Z) | — | детерминизм | `tests/sim.rs` |
| `src/meta.rs` | носитель | `Entity`, `Intension`, `Evidence`, `Metaedge`, `EqualAt`, фронтир | `model::Plane`, `plane::Axes` | общий носитель | `tests/metacore.rs`, `tests/identity_extent.rs`, `tests/open_frontier.rs` |
| `src/meta_journal.rs` | носитель | журнал metacore (J) | `meta`, `bank::ExactRelation`, `journal` | воспроизведение | `tests/identity_extent.rs` |
| `src/bits.rs` | носитель | точное плотное множество (N) | — | битовые слова | `tests/atlas.rs`, `tests/bank.rs` |
| `src/extent.rs` | вид | «где верно p», импликации (H52) | `eval`, `check` | отчёт по плоскостям | `tests/extent.rs` |
| `src/concept.rs` | ядро | понятие, разложение (D) | `eval`, `model` | вложение запросов | `tests/concept.rs` |
| `src/label.rs` | ядро | метки вложенности (N, H61) | `eval` | интервалы | `tests/label.rs`, `tests/nesting.rs` |
| `src/reflect.rs` | ядро | R1 диагноз (X) | `check` | рефлексия | `tests/reflect.rs` |
| `src/propose.rs` | ядро | R2 предложения (X) | `reflect`, `check` | рефлексия | `tests/propose.rs` |
| `src/learn.rs` | ядро | обучение по шаблону | `check` | EBG-подобный поиск | `tests/learn.rs` |
| `src/bank.rs` | боковой мир | банк выражений, `ExactRelation` (H72) | `bits`, `meta` | чистый мир | `tests/bank.rs`, `tests/identity_extent.rs` |
| `src/layer.rs` | боковой мир | отношения между отношениями (H75 А) | `bank`, `meta` | слой 2 | `tests/layer.rs` |
| `src/universe.rs` | боковой мир | вселенная конечных отношений (H75 А2) | `bank` | один универсум | `tests/universe.rs` |
| `src/scale.rs` | боковой мир | скрытая шкала (H73, закрыто) | `bank` | опыт шкалы | `tests/scale.rs` |
| `src/atlas.rs` | боковой мир | атлас таблиц (H74) | `bits`, `sat`, `meta` | function-first, к переделке | `tests/atlas.rs`, `tests/atlas_metacore.rs` |
| `src/sat.rs` | боковой мир | поиск моделей CDCL (H74 §7) | — | решатель для атласа | `tests/atlas.rs` |
| `src/free.rs` | боковой мир | свободная сущность, Биркгоф (H74 §10) | `atlas` | законы как элементы | `tests/free.rs` |
| `src/rewrite.rs` | боковой мир | нормальные формы, Кнут–Бендикс (H74 §11) | `free` | пополнение | `tests/free.rs` |
| `src/exists.rs` | боковой мир | «существует» по Сколему (H74 §12) | `rewrite` | законы с ∃ | `tests/free.rs` |
| `src/develop.rs` | боковой мир | развитие с нуля (H74 §9) | `atlas`, `journal` | журнал атласа | `tests/journal.rs` |
| `src/journal.rs` | боковой мир | журнал атласа (H74 §9) | — | отдельный от `meta_journal` | `tests/journal.rs` |
| `examples/adjoin.rs` | внешний опыт | H57 шаг 3 | `check` | свой генератор | — |
| `examples/analogy.rs` | внешний опыт | H51 | `check` | прототип | — |
| `examples/bombelli.rs` | внешний опыт | H53 шаг Бомбелли | `check` | свой генератор | `tests/discovery.rs` |
| `examples/cauchy.rs` | внешний опыт | H57 шаг 2 | `check` | свой генератор | `tests/discovery.rs` |
| `examples/census.rs` | внешний опыт | H61 перепись атомов | `eval` | замер | — |
| `examples/develop.rs` | внешний опыт | H74 §9 | `develop` | запуск | `tests/journal.rs` |
| `examples/exists.rs` | внешний опыт | H74 §12 | `exists` | запуск | — |
| `examples/factor.rs` | внешний опыт | H74 §8 | `atlas` | запуск | — |
| `examples/fca.rs` | внешний опыт | H61 шаг 5а, объём и содержание | свой `Bits` | прототип точного вектора | — |
| `examples/hamilton.rs` | внешний опыт | H57 шаг 4 | `check` | свой генератор | `tests/discovery.rs` |
| `examples/kinship_analogy.rs` | внешний опыт | H51 | `concept` | прототип | — |
| `examples/labels.rs` | внешний опыт | H61 шаг 1 | `label` | запуск | — |
| `examples/maps.rs` | внешний опыт | H74 §6–7 | `atlas`, `sat` | запуск | — |
| `examples/memstage.rs` | внешний опыт | H61 шаг 3, замер памяти | `check` | замер | — |
| `examples/planes_noise.rs` | внешний опыт | H52 | `extent` | синтетика | — |
| `examples/symptoms.rs` | внешний опыт | H73 | `scale` | таблица | — |
| `examples/universe.rs` | внешний опыт | H75 А2 | `universe` | полный прогон | — |
| `examples/weakest.rs` | внешний опыт | H74 шаг 3 | `atlas` | запуск | — |
