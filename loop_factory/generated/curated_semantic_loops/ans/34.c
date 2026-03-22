int main1(int b){
  int pj, e5, e9r5, g, jb9j, i0bs;
  pj=b;
  e5=0;
  e9r5=0;
  g=0;
  jb9j=0;
  i0bs=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i0bs + jb9j + g + e9r5 == e5;
  loop invariant b >= \at(b, Pre);
  loop invariant i0bs >= 0;
  loop invariant jb9j >= 0;
  loop invariant g >= 0;
  loop invariant e9r5 >= 0;
  loop invariant pj == \at(b, Pre);
  loop invariant (pj >= 0) ==> (e5 <= pj);
  loop assigns b, e5, i0bs, jb9j, g, e9r5;
*/
while (e5<pj) {
      if (e5%11==0) {
          i0bs = i0bs + 1;
      }
      else {
          if (e5%9==0) {
              jb9j++;
          }
          else {
              if (e5%3==0) {
                  g++;
              }
              else {
                  e9r5++;
              }
          }
      }
      e5++;
      b = b + e9r5;
  }
/*@
  assert !(e5<pj) &&
         (i0bs + jb9j + g + e9r5 == e5);
*/


  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g >= 0;
  loop invariant jb9j >= 0;
  loop invariant i0bs + jb9j + g + e9r5 == e5;
  loop assigns g, jb9j;
*/
  while (g > 0) {
      if (g >= 2) {
          g = g - 2;
          jb9j = jb9j + 2;
      } else {
          g = g - 1;
          jb9j = jb9j + 1;
      }
  }
/*@
  assert !(g > 0) &&
         (i0bs + jb9j + g + e9r5 == e5);
*/
}