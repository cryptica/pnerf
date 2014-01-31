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

#ifndef IC3_EXCEPTION_H_
#define IC3_EXCEPTION_H_

#include <exception>

class parse_exception: public std::exception {
public:
	enum ParseExceptionType {
		INCONSISTENT_INITIAL_CONDITION, TARGET_NOT_UPWARD_CLOSED, GUARD_NOT_UPWARD_CLOSED
	};
private:
	static const char * EX_TYPE_MSG[];

	const ParseExceptionType _parseExceptionType;
public:
	explicit parse_exception(ParseExceptionType) throw ();
	virtual ~parse_exception() throw ();
	virtual const char* what() const throw ();
};

#endif /* IC3_EXCEPTION_H_ */
