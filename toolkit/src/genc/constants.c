/******************************************************************************

 File Name            : constants.c

 Date                 : 08/08/2017 11:53:13

 C Translator Version : tradc Java V1.0 (14/03/2012)

******************************************************************************/

/*------------------------
   Exported Declarations
  ------------------------*/
#include "constants.h"

/*------------------------
   INITIALISATION Clause
  ------------------------*/
void constants__INITIALISATION(void) {
}

/*--------------------
   OPERATIONS Clause
  --------------------*/
void constants__read_cast_t_ReadValue(
   const t_entier4 constants__ii,
   constants__t_ReadValue_i * const constants__rvi) {
   *constants__rvi = constants__ii;
}

void constants__get_cast_t_WriteValue(
   const t_entier4 constants__ii,
   constants__t_WriteValue_i * const constants__wvi) {
   *constants__wvi = constants__ii;
}

