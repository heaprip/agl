# Скелет mini-agl с отбором закона по H113

Статус: **не принято**; быстрый грубый опыт, не решение и не основание для ядра
(`docs/course.md`, «Сейчас»). Ветка `experiment/mini-agl-skeleton`. Python 3, только
стандартная библиотека; вне крейта Rust (`tests/registry.rs` и хук
`tools/hooks/guard_module.sh` смотрят только `src/*.rs` и `examples/*.rs`, этот
путь ими не охвачен).

План с приёмкой, записанный до кода: `local/experiments/mini-agl/skeleton-plan.md` (вне git),
sha256 = `fd52d70368bf4a43a359ba3c705c955e88251c68073e1216d74574257eefd5ca`.

Части (каждая читает и пишет файлы): `gen_world.py` → `candidates.py` →
`select_laws.py` → `report.py` → `score.py` (оракул читает только он); общая часть —
`lawlib.py`; вход — `run.sh [OUTDIR] [SEEDS]` (будильник 600 с, seeds по умолчанию 1..5,
итог — `OUTDIR/summary.txt`). `EXC_CODE=binom` включает код исключений плана (нормативный для приёмки); по умолчанию включён более консервативный код `list`, введённый после провала П3.
Детерминизм: случайность только от `random.Random(строка-seed)`, часов и потоков нет, обходы
отсортированы; `run.py` сам сравнивает вывод при перестановке строк и другом
`PYTHONHASHSEED`.
