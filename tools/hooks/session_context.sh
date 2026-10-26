#!/bin/sh
# SessionStart hook (startup, resume, clear, compact): puts the current state
# and the author's corrections back into context, so a new or compacted
# session does not start from memory.
cd "$(dirname "$0")/../.." || exit 0
echo "=== agl: контекст сессии (хук tools/hooks/session_context.sh) ==="
echo
cat docs/now.md
echo
echo "=== Поправки автора, которые агенты уже нарушали (docs/entities.md §0) ==="
awk '/^## 0\./{on=1;next} /^## 1\./{on=0} on' docs/entities.md
cat <<'CARD'
=== Порядок работы ===
- До предложения или кода: прочитать docs/entities.md целиком и нужные H.
  Grep — не чтение. Сказать честно, что прочитано, а что нет.
- Обсуждение с автором — в главной сессии. Исполнение — агентом agl-worker
  (.claude/agents/), проверка — agl-auditor, до коммита.
- Новый модуль — сначала строка в docs/modules.md (architecture §8); тест
  tests/registry.rs это проверяет.
- Эксперимент — ветка от контрольной точки, критерий до кода (решение 24).
- Высказывания автора — только в CLAUDE.local.md / local/ (решение 30).
- Закончил задачу — обнови docs/now.md в том же коммите.
CARD
