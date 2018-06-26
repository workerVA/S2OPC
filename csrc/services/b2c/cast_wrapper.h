/*
 * cast_wrapper.h
 *
 *  Created on: 25 juin 2018
 *      Author: simon
 */

#ifndef CAST_WRAPPER_H_
#define CAST_WRAPPER_H_

#ifdef __FRAMAC__
// Let us use asserts for defensive programming, but make them invisible to
// FramaC.
#undef assert
#define assert(x) ;
#endif // __FRAMAC__


#endif /* CAST_WRAPPER_H_ */
