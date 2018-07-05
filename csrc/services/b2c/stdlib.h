#include <stddef.h>

/*@ assigns \result;
    ensures \result == \null || \valid((int*) \result + (0 .. size));
*/
extern int* malloc(size_t size);

/*@ requires \null == ptr || \true
    assigns \nothing;
    ensures \true;
 */

extern void free(void* ptr);
