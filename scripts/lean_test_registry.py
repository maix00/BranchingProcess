"""Single reviewed inventory for required and advisory Lean axiom checks."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / 'scripts/lean-test-registry.json'


def unique_fields(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'Duplicate registry field: {key}')
        result[key] = value
    return result


def read_registry(path=REGISTRY, category=None):
    data = json.loads(path.read_text(), object_pairs_hook=unique_fields)
    if data.get('schema_version') != 1:
        raise ValueError(f'Unsupported test registry: {path}')
    for name, entry in data['entries'].items():
        if category is not None and entry.get('category') != category:
            continue
        parts = Path(name).parts
        entry_category = entry['category']
        prefix = {'required': 'BranchingProcessTest', 'literature': 'LiteratureProofTest'}[entry_category]
        if not parts or parts[0] != prefix or '..' in parts or not name.endswith('.lean'):
            raise ValueError(f'Invalid {entry_category} test path: {name}')
        declarations = entry['declarations']
        if len(set(declarations)) != len(declarations):
            raise ValueError(f'Duplicate expected declarations: {name}')
    return data


def registry_entries(category=None):
    entries = read_registry(category=category)['entries']
    return {p: e for p, e in entries.items() if category is None or e.get('category') == category}


def allowed_axioms():
    return set(read_registry(category='policy')['allowed_axioms'])


def expected_declarations(path, category):
    entry = registry_entries(category).get(Path(path).as_posix())
    if entry is None:
        raise ValueError(f'Unregistered {category} axiom entry: {path}')
    if entry['category'] != category:
        raise ValueError(f'Wrong check category for {path}: {category}')
    return tuple(entry['declarations'])
