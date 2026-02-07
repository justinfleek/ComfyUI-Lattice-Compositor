/*
Copyright 2021 by Inria, Mickaël Ly, Jean Jouve, Florence Bertails-Descoubes and
    Laurence Boissieux

This file is part of ProjectiveFriction.

ProjectiveFriction is free software: you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the Free
Software Foundation, either version 3 of the License, or (at your option) any
later version.

ProjectiveFriction is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for more
details.

You should have received a copy of the GNU General Public License along with
ProjectiveFriction. If not, see <https://www.gnu.org/licenses/>.
*/
#ifndef JSON_HELPER_HPP
#define JSON_HELPER_HPP

//#define JSON_HELPER_VERBOSE

#include <iostream>
#include <stdexcept>
#include <string>
#include <rapidjson/rapidjson.h>
#include <rapidjson/filereadstream.h>
#include <rapidjson/document.h>

/** @file
 * Defines high level function to access a JSON document loaded with rapidjson.
 */

rapidjson::Document
getJSONDocumentFromFilename(const std::string& filename);

// Must define through macro as rapidjson is not templated...
// This could be circumvented by implementing a templated wrapper around the
// method necessary for the given type.
// TODO: Implement above technique

template<typename jsonType>
using ValueReference = std::conditional_t<std::is_const<jsonType>::value,
                                          const rapidjson::Value&,
                                          rapidjson::Value&>;

/**
 * @brief Query the value in the document and throw an `std::invalid_argument`
 * if it is not present.
 *
 * @param document  JSON document
 * @param name      Name of the value to require
 *
 * @return The value
 */
template<typename jsonType>
ValueReference<jsonType>
jsonGetValue(jsonType& document, const char* key)
{
  using MemberIterator =
    std::conditional_t<std::is_const<jsonType>::value,
                       rapidjson::Value::ConstMemberIterator,
                       rapidjson::Value::MemberIterator>;

  std::string keyStr(key);
  MemberIterator itr = document.FindMember(key);
  if (itr == document.MemberEnd())
  {
    const std::string notFoundPrefix =
      "JSON reader - Error: cannot find key ";
    throw std::invalid_argument(notFoundPrefix + keyStr);
  }
  return (itr->value);
}



#ifdef JSON_HELPER_VERBOSE

#define jsonRequireTypeCheck(type, funcName, jsonFuncCheck, jsonFuncGet) \
    template<typename jsonType>                                         \
    type funcName(jsonType& document, const char* key)                  \
    {                                                                   \
        std::string keyStr(key);                                        \
        ValueReference<jsonType> val = jsonGetValue(document, key);     \
        if (!(val.jsonFuncCheck()))                                     \
        {                                                               \
            const std::string typeErrorPrefix =                         \
                "JSON reader - Error: type error with key ";            \
            throw std::invalid_argument(typeErrorPrefix + keyStr);      \
        }                                                               \
        std::cout << "JSON reader - Key " << key                        \
                  << "=" << val.jsonFuncGet() << std::endl;             \
        return (type)(val.jsonFuncGet());                               \
    }


#define jsonOptionalTypeCheck(type, funcName, jsonFuncCheck, jsonFuncGet) \
    template<typename jsonType>                                         \
    type funcName(jsonType& document, const char* key, const type &dflt) \
    {                                                                   \
        std::string keyStr(key);                                        \
        try {                                                           \
            ValueReference<jsonType> val = jsonGetValue(document, key); \
            if (!(val.jsonFuncCheck()))                                 \
            {                                                           \
                const std::string typeErrorPrefix =                     \
                    "JSON reader - Error: type error with key ";        \
                throw std::invalid_argument(typeErrorPrefix + keyStr);  \
            }                                                           \
            std::cout << "JSON reader - Key " << key                    \
                      << "=" << val.jsonFuncGet() << std::endl;         \
            return (type)(val.jsonFuncGet());                           \
        } catch (const std::invalid_argument &e) {                      \
            std::cout << "JSON reader - Warning: Key \"" << key           \
                      << "\" not found, use default value" << std::endl;  \
            return dflt;                                                \
        }                                                               \
    }

#else // JSON_HELPER_VERBOSE

#define jsonRequireTypeCheck(type, funcName, jsonFuncCheck, jsonFuncGet) \
    template<typename jsonType>                                         \
    type funcName(jsonType& document, const char* key)                  \
    {                                                                   \
        std::string keyStr(key);                                        \
        ValueReference<jsonType> val = jsonGetValue(document, key);     \
        if (!(val.jsonFuncCheck()))                                     \
        {                                                               \
            const std::string typeErrorPrefix =                         \
                "JSON reader - Error: type error with key ";            \
            throw std::invalid_argument(typeErrorPrefix + keyStr);      \
        }                                                               \
        return (type)(val.jsonFuncGet());                               \
    }

#define jsonOptionalTypeCheck(type, funcName, jsonFuncCheck, jsonFuncGet) \
    template<typename jsonType>                                         \
    type funcName(jsonType& document, const char* key, const type &dflt) \
    {                                                                   \
        std::string keyStr(key);                                        \
        try {                                                           \
            ValueReference<jsonType> val = jsonGetValue(document, key); \
            if (!(val.jsonFuncCheck()))                                 \
            {                                                           \
                const std::string typeErrorPrefix =                     \
                    "JSON reader - Error: type error with key ";        \
                throw std::invalid_argument(typeErrorPrefix + keyStr);  \
            }                                                           \
            return (type)(val.jsonFuncGet());                           \
        } catch (const std::invalid_argument &e) {                      \
            std::cout << "JSON reader - Warning: Key \"" << key         \
                      << "\" not found, use default value: "            \
			          << dflt << std::endl;                             \
            return dflt;                                                \
        }                                                               \
    }

#endif // JSON_HELPER_VERBOSE

/**
 * Returns the JSON object associated to the given key in the given document. If
 * the key is not present an `std::invalid_argument` is thrown.
 * If the value associated to the given key is not a JSON object an
 * `std::invalid_argument` is thrown.
 *
 * @param document A rapidjson value which represents a JSON object. If
 *                 `document` does not represent an object the behavior is
 *                 undefined.
 * @param key The key to which the array is associated.
 *
 */
template<typename jsonType>
ValueReference<jsonType>
jsonRequireObjectCheck(jsonType& document, const char* key)
{
  std::string keyStr(key);
  ValueReference<jsonType> val = jsonGetValue(document, key);
  if (!(val.IsObject()))
  {
    const std::string typeErrorPrefix =
      "JSON reader - Error: type error with key ";
    throw std::invalid_argument(typeErrorPrefix + keyStr);
  }
  return val;
}

/**
 * Returns the JSON array associated to the given key in the given document. If
 * the key is not present an `std::invalid_argument` is thrown. If the value
 * associated to the given key is not a JSON array an `std::invalid_argument` is
 * thrown.
 *
 * @param document A rapidjson value which represents a JSON object. If
 *                 `document` does not represent an object the behavior is
 *                 undefined.
 * @param key The key to which the array is associated.
 *
 */
template<typename jsonType>
ValueReference<jsonType>
jsonRequireArrayCheck(jsonType& document, const char* key)
{
  std::string keyStr(key);
  ValueReference<jsonType>& val = jsonGetValue(document, key);
  if (!(val.IsArray()))
  {
    const std::string typeErrorPrefix =
      "JSON reader - Error: type error with key ";
    throw std::invalid_argument(typeErrorPrefix + keyStr);
  }
  return val;
}

#ifdef JSON_HELPER_VERBOSE

#define jsonRequire(type, funcName, jsonFuncGet)                        \
    template<typename jsonType>                                         \
    type funcName(jsonType& document, const char* key)                  \
    {                                                                   \
        ValueReference<jsonType> val = jsonGetValue(document, key);     \
        std::cout << "JSON reader - Key " << key                        \
                  << "=" << val.jsonFuncGet() << std::endl;             \
        return val.jsonFuncGet();                                       \
    }
#define jsonOptional(type, funcName, jsonFuncGet)                       \
    template<typename jsonType>                                         \
    type funcName(jsonType& document, const char* key, const type &dflt) \
    {                                                                   \
        try {                                                           \
            ValueReference<jsonType> val = jsonGetValue(document, key); \
            std::cout << "JSON reader - Key " << key                    \
                      << "=" << val.jsonFuncGet() << std::endl;         \
            return val.jsonFuncGet();                                   \
        } catch (const std::invalid_argument &e) {                      \
            std::cout << "JSON reader - Warning: Key \"" << key           \
                      << "\" not found, use default value" << std::endl;  \
            return dflt;                                                \
        }                                                               \
    }


#else // JSON_HELPER_VERBOSE

#define jsonRequire(type, funcName, jsonFuncGet)                        \
    template<typename jsonType>                                         \
    type funcName(jsonType& document, const char* key)                  \
    {                                                                   \
        ValueReference<jsonType> val = jsonGetValue(document, key);     \
        return val.jsonFuncGet();                                       \
    }
#define jsonOptional(type, funcName, jsonFuncGet)                       \
    template<typename jsonType>                                         \
    type funcName(jsonType& document, const char* key, const type &dflt) \
    {                                                                   \
        try {                                                           \
            ValueReference<jsonType> val = jsonGetValue(document, key); \
            return val.jsonFuncGet();                                   \
        } catch (const std::invalid_argument &e) {                      \
            std::cout << "JSON reader - Warning: Key \"" << key           \
                      << "\" not found, use default value" << std::endl;  \
            return dflt;                                                \
        }                                                               \
    }

#endif // JSON_HELPER_VERBOSE

/** @fn jsonRequireInt
 * Returns the integer associated to the given key in the given object. If the
 * key is not associated to an integer an `std::invalid_argument` is thrown.
 * @param document The object. If the given document is not an object you have
 *                 undefined behavior.
 * @param key The key to which the integer is associated. If the key is not
 *            found an `std::invalid_argument` is thrown.
 */
jsonRequireTypeCheck(int, jsonRequireInt, IsInt, GetInt)
jsonOptionalTypeCheck(int, jsonOptionalInt, IsInt, GetInt)

  /** @fn jsonRequireUint
   * Returns the unsigned integer associated to the given key in the given
   * object. If the key is not associated to an unsigned integer an
   * `std::invalid_argument` is thrown.
   * @param document The object. If the given document is not an object you have
   *                 undefined behavior.
   * @param key The key to which the integer is associated. If the key is not
   *            found an `std::invalid_argument` is thrown.
   */
  jsonRequireTypeCheck(unsigned int, jsonRequireUint, IsUint, GetUint)
  jsonOptionalTypeCheck(unsigned int, jsonOptionalUint, IsUint, GetUint)

  /** @fn jsonRequireUint
   * Returns the floating point number associated to the given key in the given
   * object.  If the key is not associated to a floating point number an
   * `std::invalid_argument` is thrown.
   *
   * @param document The object. If the given document is not an object you have
   *                 undefined behavior.
   * @param key The key to which the integer is associated. If the key is not
   *            found an `std::invalid_argument` is thrown.
   */
  jsonRequireTypeCheck(float, jsonRequireFloat, IsDouble, GetDouble)
  jsonOptionalTypeCheck(float, jsonOptionalFloat, IsDouble, GetDouble)

  /** @fn jsonRequireDouble
   * Returns the double precision floating point number associated to the given
   * key in the given object. If the key is not associated to a double precision
   * floating point number an `std::invalid_argument` is thrown.
   *
   * @param document The object. If the given document is not an object you have
   *                 undefined behavior.
   * @param key The key to which the integer is associated. If the key is not
   *            found an `std::invalid_argument` is thrown.
   */
  jsonRequireTypeCheck(double, jsonRequireDouble, IsDouble, GetDouble)
  jsonOptionalTypeCheck(double, jsonOptionalDouble, IsDouble, GetDouble)

  /** @fn jsonRequireBool
   * Returns the boolean associated to the given key in the given object. If the
   * key is not associated to a boolean number an `std::invalid_argument` is
   * thrown.
   *
   * @param document The object. If the given document is not an object you have
   *                 undefined behavior.
   * @param key The key to which the integer is associated. If the key is not
   *            found an `std::invalid_argument` is thrown.
   */
  jsonRequireTypeCheck(bool, jsonRequireBool, IsBool, GetBool)
  jsonOptionalTypeCheck(bool, jsonOptionalBool, IsBool, GetBool)

  /** @fn jsonRequireString
   * Returns the string associated to the given key in the given object. If the
   * key is not associated to a boolean number an `std::invalid_argument` is
   * thrown.
   *
   * @param document The object. If the given document is not an object you have
   *                 undefined behavior
   * @param key The key to which the integer is associated. If the key is not
   *            found an `std::invalid_argument` is thrown.
   */
  jsonRequire(std::string, jsonRequireString, GetString)
  jsonOptional(std::string, jsonOptionalString, GetString)

#undef jsonRequireTypeCheck
#undef jsonRequire
#endif // JSON_HELPER_HPP
