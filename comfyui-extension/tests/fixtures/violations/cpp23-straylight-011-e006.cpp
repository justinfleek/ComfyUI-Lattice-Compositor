// Violation: STRAYLIGHT-011-E006 - nullptr without handling
int* ptr = nullptr;
*ptr = 42; // No check before use
