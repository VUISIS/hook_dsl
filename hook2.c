/*@ ensures \result > 1 && \result < 10;
 @ hook \foo_hook_special;
 */
int foo(int a, char b);


/*@ requires b != \null;
 @ hook;
 */
void bar(float a, void *b);


/*@ ensures \result != \null;
 @ hook;
 */
char *baz();

