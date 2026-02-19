// Valid C++23 - uses smart pointers
#include <memory>

int main() {
  auto ptr = std::make_unique<int>(42);
  return *ptr;
}
