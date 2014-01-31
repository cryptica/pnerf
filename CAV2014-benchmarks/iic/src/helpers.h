// vim:sw=4
/*
   This file is part of IC3WSTS.

   IC3WSTS is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2 of the License, or
   (at your option) any later version.

   IC3WSTS is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with IC3WSTS; if not, write to the Free Software
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA

   Copyright 2012, Johannes Kloos
 */
#ifndef IC3_HELPERS_H
#define IC3_HELPERS_H 1

#include <boost/unordered_set.hpp>
#include <iostream>

#ifndef IC3_SUPPRESS_STD_CERR

#define debuglog std::cerr

#else

struct dummy {
    template<typename T> dummy operator<<(T) const {
	return *this;
    }
    dummy operator<<(std::ostream& (*pf)(std::ostream&)) const {
	return *this;
    }
    dummy operator<<(std::ios& (*pf)(std::ios&)) const {
	return *this;
    }
    dummy operator<<(std::ios_base& (*pf)(std::ios_base&)) const {
	return *this;
    }
};
#define debuglog dummy()

#endif

/** Create a singleton set. */
template<typename T>
boost::unordered_set<T> singleton(const T& t) {
    boost::unordered_set<T> res;
    res.insert(t);
    return res;
}

#endif
