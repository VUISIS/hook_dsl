/*@ ensures \result > 1 && \result < 10; */
int foo(int a, char b);


/*@ requires b != \null; */
void bar(float a, void *b);

