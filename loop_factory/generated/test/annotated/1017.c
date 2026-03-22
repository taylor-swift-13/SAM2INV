int main1(){
  int x, sx, n7ui;
  x=67;
  sx=0;
  n7ui=sx;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sx == 5 * n7ui;
  loop invariant 0 <= n7ui;
  loop assigns n7ui, sx;
*/
for (; sx<x; sx = sx + 5) {
      n7ui = n7ui + 1;
  }
}