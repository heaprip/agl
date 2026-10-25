# Hyperon/MeTTa identity–extent baseline

Сценарий [`identity_extent.metta`](identity_extent.metta) проверен на
официальном `hyperon-experimental` commit
`3f76dc460da6961f57f69f6c3e550c59c74ada83` (`v0.2.10`). Пользовательских
grounded atoms и host-side identity store нет; используются только atoms,
`match` и стандартные операции Space.

Из-за default feature `das` официальный REPL требует внешний `protoc`. Для
минимальной сборки на проверенной ревизии в отдельном временном клоне были
сделаны две build-only правки:

```toml
# workspace Cargo.toml
hyperon = { path = "./lib", version = "0.2.10", default-features = false }

# repl/Cargo.toml
hyperon = { workspace = true, optional = true, default-features = false }
```

Запуск:

```sh
cargo run --release -p metta-repl \
  --no-default-features --features hyperon,hyperon/pkg_mgmt -- \
  /absolute/path/to/experiments/hyperon/identity_extent.metta
```

`pkg_mgmt` оставлен потому, что JSON builtin этой ревизии компилируется с
`serde_json`, объявленным optional через этот feature. DAS в сценарии не
используется.

Чистый stdout должен побайтно совпасть с
[`identity_extent.expected`](identity_extent.expected): 16 строк `[()]`.

SHA-256:

```text
62d631f6a2262b3af7b12683fe4b98be8b36aea6067b09156e95859b9d83dfc3  identity_extent.metta
2dfaabfa228857ff5e6d3afbd4efbb8da7cd3db79e32b2722cf7e306807f494e  identity_extent.expected
```

Assertions после `remove-atom` намеренно проверяют, что зависимые atoms
**остались**. Это зафиксированная граница Hyperon, а не ожидаемая семантика
agl.
