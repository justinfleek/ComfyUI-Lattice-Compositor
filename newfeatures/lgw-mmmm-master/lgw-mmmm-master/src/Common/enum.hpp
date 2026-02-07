#ifndef ENUM_HPP
#define ENUM_HPP

#define DEFINE_BITWISE_STRUCT(structname, ...)                                \
    struct structname {                                                       \
        int m_val;                                                            \
        constexpr structname(int val) : m_val(val) {}                         \
        explicit constexpr operator bool() const { return (m_val) != 0; }     \
        explicit constexpr operator int() const { return m_val; }             \
        structname& operator&=(structname b) {                                \
            m_val &= b.m_val;                                                 \
            return *this;                                                     \
        }                                                                     \
        structname& operator|=(structname b) {                                \
            m_val |= b.m_val;                                                 \
            return *this;                                                     \
        }                                                                     \
        static const structname __VA_ARGS__;                                  \
    };                                                                        \
    inline structname operator|(structname a, structname b) {                 \
        return static_cast<structname>(                                       \
            static_cast<int>(a) | static_cast<int>(b)                         \
        );                                                                    \
    }                                                                         \
    inline structname operator&(structname a, structname b) {                 \
        return static_cast<structname>(                                       \
            static_cast<int>(a) & static_cast<int>(b)                         \
        );                                                                    \
    }                                                                         \
    inline bool operator==(structname a, structname b) {                      \
        return static_cast<bool>(static_cast<int>(a) == static_cast<int>(b)); \
    }                                                                         \
    inline bool operator!=(structname a, structname b) {                      \
        return static_cast<bool>(static_cast<int>(a) != static_cast<int>(b)); \
    }                                                                         \
    inline structname operator~(structname a) {                               \
        return static_cast<structname>(~static_cast<int>(a));                 \
    }

// https://softwareengineering.stackexchange.com/questions/194412/using-scoped-enums-for-bit-flags-in-c
/*
#define ENUM_FLAG_OPERATOR(T,X)                                         \
    inline T operator X (T lhs, T rhs)                                  \
    { return (T) (static_cast<std::underlying_type_t <T>>(lhs)          \
                  X static_cast<std::underlying_type_t <T>>(rhs)); }
#define ENUM_FLAGS(T) \
    enum class T;                                                       \
    inline T operator ~ (T t) { return (T) (~static_cast<std::underlying_type_t
<T>>(t)); } \
    ENUM_FLAG_OPERATOR(T, |)                                            \
    ENUM_FLAG_OPERATOR(T, ^)                                            \
    ENUM_FLAG_OPERATOR(T, &)
//  \ enum class // Commented out for indentation issues
*/

#endif  // ENUM_HPP
