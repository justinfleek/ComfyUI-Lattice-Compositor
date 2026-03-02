import re

with open('MASTER_CHECKLIST.md', 'r', encoding='utf-8') as f:
    content = f.read()

lines = content.split('\n')
sections = {}
current_section = None

for line in lines:
    m = re.match(r'^## (.+)$', line)
    if m:
        current_section = m.group(1)
        sections[current_section] = {'has_ontology': False, 'file_count': 0}
    elif current_section and 'Ontology' in line and '| File |' in line:
        sections[current_section]['has_ontology'] = True
    elif current_section and re.match(r'^\| [a-zA-Z]', line):
        sections[current_section]['file_count'] += 1

sections_without = {k: v for k, v in sections.items() if not v['has_ontology'] and v['file_count'] > 0}
total = sum(v['file_count'] for v in sections_without.values())

print(f'Sections without Ontology column: {len(sections_without)}')
print(f'Total files in those sections: {total}')
print()
for section, data in sorted(sections_without.items()):
    print(f'  {section}: {data["file_count"]} files')
