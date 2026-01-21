#!/usr/bin/env python3
"""Parse lazy code audit file and get exact counts"""

with open('lazy_code_audit.txt', 'r', encoding='utf-8') as f:
    lines = [line.strip().split('|') for line in f if '|' in line]

# Filter test vs production
test_files = [x for x in lines if '__tests__' in x[0] or '.test.' in x[0] or '.spec.' in x[0]]
prod_files = [x for x in lines if x not in test_files]

def sum_column(files, idx):
    return sum(int(x[idx]) for x in files if len(x) > idx and x[idx].isdigit())

# Production counts
nullish_prod = sum_column(prod_files, 1)
orZero_prod = sum_column(prod_files, 2)
orOne_prod = sum_column(prod_files, 3)
orEmpty_prod = sum_column(prod_files, 4)
orObj_prod = sum_column(prod_files, 5)
asAny_prod = sum_column(prod_files, 6)
asUnknown_prod = sum_column(prod_files, 7)
tsIgnore_prod = sum_column(prod_files, 8)
nonNull_prod = sum_column(prod_files, 9)

# Test counts
nullish_test = sum_column(test_files, 1)
orZero_test = sum_column(test_files, 2)
orOne_test = sum_column(test_files, 3)
orEmpty_test = sum_column(test_files, 4)
orObj_test = sum_column(test_files, 5)
asAny_test = sum_column(test_files, 6)
asUnknown_test = sum_column(test_files, 7)
tsIgnore_test = sum_column(test_files, 8)
nonNull_test = sum_column(test_files, 9)

print("=" * 60)
print("PRODUCTION CODE LAZY PATTERNS (EXACT COUNTS)")
print("=" * 60)
print(f"  Nullish Coalescing (??): {nullish_prod}")
print(f"  Logical OR Zero (|| 0): {orZero_prod}")
print(f"  Logical OR One (|| 1): {orOne_prod}")
print(f"  Logical OR Empty Array (|| []): {orEmpty_prod}")
print(f"  Logical OR Empty Object (|| {{}}): {orObj_prod}")
print(f"  Type Assertion 'as any': {asAny_prod}")
print(f"  Type Assertion 'as unknown as': {asUnknown_prod}")
print(f"  TS Suppression (@ts-ignore/@ts-expect-error): {tsIgnore_prod}")
print(f"  Non-null Assertions (!): {nonNull_prod}")
prod_total = nullish_prod + orZero_prod + orOne_prod + orEmpty_prod + orObj_prod + asAny_prod + asUnknown_prod + tsIgnore_prod + nonNull_prod
print(f"  PRODUCTION TOTAL: {prod_total}")
print()

print("=" * 60)
print("TEST CODE LAZY PATTERNS (EXACT COUNTS)")
print("=" * 60)
print(f"  Nullish Coalescing (??): {nullish_test}")
print(f"  Logical OR Zero (|| 0): {orZero_test}")
print(f"  Logical OR One (|| 1): {orOne_test}")
print(f"  Logical OR Empty Array (|| []): {orEmpty_test}")
print(f"  Logical OR Empty Object (|| {{}}): {orObj_test}")
print(f"  Type Assertion 'as any': {asAny_test}")
print(f"  Type Assertion 'as unknown as': {asUnknown_test}")
print(f"  TS Suppression (@ts-ignore/@ts-expect-error): {tsIgnore_test}")
print(f"  Non-null Assertions (!): {nonNull_test}")
test_total = nullish_test + orZero_test + orOne_test + orEmpty_test + orObj_test + asAny_test + asUnknown_test + tsIgnore_test + nonNull_test
print(f"  TEST TOTAL: {test_total}")
print()

print("=" * 60)
print("GRAND TOTAL")
print("=" * 60)
print(f"  TOTAL LAZY PATTERNS: {prod_total + test_total}")
print(f"  Production Files: {len(prod_files)}")
print(f"  Test Files: {len(test_files)}")
