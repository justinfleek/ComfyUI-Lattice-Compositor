// Violation: STRAYLIGHT-011-E007 - Raw new/delete
int* ptr = new int(42);
delete ptr;
