/*
 * frama_c_assert.h
 *
 *  Created on: 25 juin 2018
 *      Author: simon
 */

#ifndef FRAMA_C_ASSERT_H_
#define FRAMA_C_ASSERT_H_

#ifdef __FRAMAC__
// Let us use asserts for defensive programming, but make them invisible to
// FramaC.
#undef assert
#define assert(x) ;
#endif // __FRAMAC__

#endif /* FRAMA_C_ASSERT_H_ */
