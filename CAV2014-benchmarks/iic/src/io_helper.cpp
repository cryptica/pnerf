// vim:sw=4:cindent
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

   Copyright 2012 Johannes Kloos.
 */
#include "vass_state_sets.h"
#include <iostream>

std::ostream& operator<<(std::ostream& os, const ic3_state& s) {
    const char *sep = "[ ";
    for (ic3_state_it it(s.begin()); it != s.end(); it++) {
        os << sep << *it;
        sep = ", ";
    }
    return (os << "]");
}

std::ostream& operator<<(std::ostream& os, const timed_state& ts) {
    return os << ts.s << '@' << ts.t;
}

std::ostream& operator<<(std::ostream& os, const ic3_closed_set& s) {
    s.write(os);
    return os;
}

