int main1(int q){
  int jc8h;
  jc8h=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= jc8h;
  loop invariant jc8h <= 1;
  loop assigns jc8h;
*/
while (jc8h!=jc8h) {
      if (jc8h>jc8h) {
          jc8h = jc8h - jc8h;
          jc8h = jc8h - jc8h;
          jc8h = jc8h - jc8h;
      }
      else {
          jc8h = jc8h - jc8h;
          jc8h = jc8h - jc8h;
          jc8h = jc8h - jc8h;
      }
  }
}