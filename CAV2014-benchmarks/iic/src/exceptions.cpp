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

 Copyright 2012 Filip Niksic.
 */

#include "exceptions.h"

const char * parse_exception::EX_TYPE_MSG[] = { "Inconsistent initial condition.", "Target not upward closed.", "Guard not upward closed." };

parse_exception::parse_exception(ParseExceptionType parseExceptionType) throw () :
		_parseExceptionType(parseExceptionType) {
}

parse_exception::~parse_exception() throw () {
}

const char* parse_exception::what() const throw () {
	return EX_TYPE_MSG[_parseExceptionType];
}
