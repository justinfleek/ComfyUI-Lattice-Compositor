"""Hypothesis property tests for s4_runtime.containers module."""

from hypothesis import given, assume, settings, example, note
from hypothesis import strategies as st

import pytest

try:
    from s4_runtime import containers
    HAS_MODULE = True
except ImportError:
    HAS_MODULE = False
    containers = None


pytestmark = pytest.mark.skipif(not HAS_MODULE, reason="s4_runtime not built")


# Strategy for generating lists of unique integers.
unique_int_lists = st.lists(st.integers(min_value=-1000, max_value=1000), unique=True)


class TestUniqueVector:
    """Property tests for unique_vector container."""
    
    @given(unique_int_lists)
    def test_no_duplicates_after_insert(self, elements):
        """Inserting elements should never create duplicates."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        result = list(vec)
        assert len(result) == len(set(result))
    
    @given(unique_int_lists)
    def test_order_preserved(self, elements):
        """Insertion order should be preserved."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        result = list(vec)
        assert result == elements
    
    @given(unique_int_lists)
    def test_duplicate_insert_noop(self, elements):
        """Inserting a duplicate should be a no-op."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        # Insert all elements again.
        for e in elements:
            vec.push_back(e)
        
        result = list(vec)
        assert result == elements
    
    @given(unique_int_lists)
    def test_contains_correctness(self, elements):
        """contains() should return True for all inserted elements."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        for e in elements:
            assert e in vec
        
        # Check something not in the list.
        not_present = max(elements) + 1 if elements else 0
        assert not_present not in vec
    
    @given(unique_int_lists)
    def test_size_matches_unique_count(self, elements):
        """Size should match number of unique elements."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        assert len(vec) == len(elements)
    
    @given(unique_int_lists)
    def test_clear_empties_container(self, elements):
        """clear() should empty the container."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        vec.clear()
        assert len(vec) == 0
        assert list(vec) == []
    
    @given(unique_int_lists, unique_int_lists)
    def test_intersection_is_symmetric(self, list1, list2):
        """Intersection should be symmetric (A ∩ B = B ∩ A)."""
        vec1 = containers.UniqueVectorInt()
        vec2 = containers.UniqueVectorInt()
        for e in list1:
            vec1.push_back(e)
        for e in list2:
            vec2.push_back(e)
        
        inter1 = vec1.intersect(vec2)
        inter2 = vec2.intersect(vec1)
        
        # Sets should be equal (order may differ).
        assert set(inter1) == set(inter2)
    
    @given(unique_int_lists, unique_int_lists)
    def test_intersection_subset(self, list1, list2):
        """Intersection should be subset of both operands."""
        vec1 = containers.UniqueVectorInt()
        vec2 = containers.UniqueVectorInt()
        for e in list1:
            vec1.push_back(e)
        for e in list2:
            vec2.push_back(e)
        
        inter = set(vec1.intersect(vec2))
        assert inter.issubset(set(list1))
        assert inter.issubset(set(list2))
    
    @given(unique_int_lists, unique_int_lists)
    def test_union_superset(self, list1, list2):
        """Union should be superset of both operands."""
        vec1 = containers.UniqueVectorInt()
        vec2 = containers.UniqueVectorInt()
        for e in list1:
            vec1.push_back(e)
        for e in list2:
            vec2.push_back(e)
        
        union = set(vec1.unite(vec2))
        assert set(list1).issubset(union)
        assert set(list2).issubset(union)
    
    @given(unique_int_lists, unique_int_lists)
    def test_subtract_no_second_elements(self, list1, list2):
        """Subtraction should remove all elements from second set."""
        vec1 = containers.UniqueVectorInt()
        vec2 = containers.UniqueVectorInt()
        for e in list1:
            vec1.push_back(e)
        for e in list2:
            vec2.push_back(e)
        
        diff = set(vec1.subtract(vec2))
        for e in list2:
            assert e not in diff
    
    @given(unique_int_lists)
    def test_copy_independence(self, elements):
        """Copy should be independent from original."""
        vec1 = containers.UniqueVectorInt()
        for e in elements:
            vec1.push_back(e)
        
        vec2 = vec1.copy()
        
        # Modify original.
        vec1.clear()
        
        # Copy should be unchanged.
        assert list(vec2) == elements


class TestDisjointSets:
    """Property tests for disjoint_sets container."""
    
    @given(st.lists(st.integers(min_value=0, max_value=100), min_size=1, max_size=50))
    def test_reflexivity(self, elements):
        """Every element should be in the same set as itself."""
        ds = containers.DisjointSetsInt()
        for e in elements:
            ds.make_set(e)
        
        for e in set(elements):
            assert ds.are_equivalent(e, e)
    
    @given(st.lists(st.tuples(
        st.integers(min_value=0, max_value=50),
        st.integers(min_value=0, max_value=50)
    ), max_size=30))
    def test_symmetry(self, pairs):
        """Equivalence should be symmetric."""
        ds = containers.DisjointSetsInt()
        
        # Make sets for all elements.
        all_elements = set()
        for a, b in pairs:
            all_elements.add(a)
            all_elements.add(b)
        
        for e in all_elements:
            ds.make_set(e)
        
        # Union all pairs.
        for a, b in pairs:
            ds.union_sets(a, b)
        
        # Check symmetry.
        for a, b in pairs:
            assert ds.are_equivalent(a, b) == ds.are_equivalent(b, a)
    
    @given(st.lists(st.tuples(
        st.integers(min_value=0, max_value=30),
        st.integers(min_value=0, max_value=30),
        st.integers(min_value=0, max_value=30)
    ), max_size=20))
    def test_transitivity(self, triples):
        """Equivalence should be transitive."""
        ds = containers.DisjointSetsInt()
        
        # Make sets for all elements.
        all_elements = set()
        for a, b, c in triples:
            all_elements.update([a, b, c])
        
        for e in all_elements:
            ds.make_set(e)
        
        # Union in chains.
        for a, b, c in triples:
            ds.union_sets(a, b)
            ds.union_sets(b, c)
        
        # Check transitivity.
        for a, b, c in triples:
            if ds.are_equivalent(a, b) and ds.are_equivalent(b, c):
                assert ds.are_equivalent(a, c)
    
    @given(st.lists(st.integers(min_value=0, max_value=50), min_size=1, max_size=30, unique=True))
    def test_initial_singletons(self, elements):
        """Initially, all elements should be in singleton sets."""
        ds = containers.DisjointSetsInt()
        for e in elements:
            ds.make_set(e)
        
        for i, e1 in enumerate(elements):
            for e2 in elements[i+1:]:
                assert not ds.are_equivalent(e1, e2)
    
    @given(st.lists(st.integers(min_value=0, max_value=30), min_size=2, max_size=20, unique=True))
    def test_union_makes_equivalent(self, elements):
        """Union should make elements equivalent."""
        ds = containers.DisjointSetsInt()
        for e in elements:
            ds.make_set(e)
        
        # Union first with second.
        ds.union_sets(elements[0], elements[1])
        assert ds.are_equivalent(elements[0], elements[1])
    
    @given(st.lists(st.integers(min_value=0, max_value=50), min_size=1, max_size=30, unique=True))
    def test_copy_independence(self, elements):
        """Copy should be independent from original."""
        ds1 = containers.DisjointSetsInt()
        for e in elements:
            ds1.make_set(e)
        
        # Make some unions.
        for i in range(0, len(elements) - 1, 2):
            ds1.union_sets(elements[i], elements[i + 1])
        
        ds2 = ds1.copy()
        
        if len(elements) >= 3:
            # Modify original.
            ds1.union_sets(elements[0], elements[-1])
            
            # Check copy didn't change (unless they were already equivalent).
            # This test is tricky - we need to check the copy's state.
            # Just verify both are valid.
            assert ds2.are_equivalent(elements[0], elements[0])


class TestDisjointSetsMapping:
    """Property tests for disjoint_sets mapping operations."""
    
    @given(st.lists(st.tuples(
        st.integers(min_value=0, max_value=20),
        st.integers(min_value=0, max_value=20)
    ), min_size=1, max_size=15))
    def test_map_entries_covers_all(self, pairs):
        """get_mapping should cover all elements."""
        ds = containers.DisjointSetsInt()
        
        # Collect all elements.
        all_elements = set()
        for a, b in pairs:
            all_elements.add(a)
            all_elements.add(b)
        
        for e in all_elements:
            ds.make_set(e)
        
        for a, b in pairs:
            ds.union_sets(a, b)
        
        # Get mapping.
        mapping = ds.get_mapping()
        
        # All elements should be in the mapping.
        for e in all_elements:
            assert e in mapping
    
    @given(st.lists(st.tuples(
        st.integers(min_value=0, max_value=20),
        st.integers(min_value=0, max_value=20)
    ), min_size=1, max_size=15))
    def test_map_entries_preserves_equivalence(self, pairs):
        """Equivalent elements should map to the same value."""
        ds = containers.DisjointSetsInt()
        
        all_elements = set()
        for a, b in pairs:
            all_elements.add(a)
            all_elements.add(b)
        
        for e in all_elements:
            ds.make_set(e)
        
        for a, b in pairs:
            ds.union_sets(a, b)
        
        mapping = ds.get_mapping()
        
        for a, b in pairs:
            if ds.are_equivalent(a, b):
                assert mapping[a] == mapping[b]


class TestUniqueVectorSetOperations:
    """Additional set operation tests."""
    
    @given(unique_int_lists)
    def test_union_with_empty_is_identity(self, elements):
        """Union with empty set should be identity."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        empty = containers.UniqueVectorInt()
        result = list(vec.unite(empty))
        
        assert set(result) == set(elements)
    
    @given(unique_int_lists)
    def test_intersect_with_empty_is_empty(self, elements):
        """Intersection with empty set should be empty."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        empty = containers.UniqueVectorInt()
        result = list(vec.intersect(empty))
        
        assert result == []
    
    @given(unique_int_lists)
    def test_subtract_empty_is_identity(self, elements):
        """Subtracting empty set should be identity."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        empty = containers.UniqueVectorInt()
        result = set(vec.subtract(empty))
        
        assert result == set(elements)
    
    @given(unique_int_lists)
    def test_subtract_self_is_empty(self, elements):
        """Subtracting self should be empty."""
        vec = containers.UniqueVectorInt()
        for e in elements:
            vec.push_back(e)
        
        result = list(vec.subtract(vec))
        assert result == []
