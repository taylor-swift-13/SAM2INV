int main1(int m,int q){
  int x, z, a;

  x=(q%18)+13;
  z=2;
  a=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant x == (q % 18) + 13;
  loop invariant a >= m;
  loop invariant (a - m) % 5 == 0;
  loop invariant x == (\at(q, Pre) % 18 + 13);
  loop invariant ((a - \at(m, Pre)) % 5) == 0;
  loop invariant a >= \at(m, Pre);
  loop invariant (a - \at(m,Pre)) % 5 == 0;
  loop invariant x == (\at(q,Pre) % 18) + 13;
  loop assigns a;
*/
while (1) {
      a = a+4;
      if (a+4<x) {
          a = a+1;
      }
      else {
          a = a+1;
      }
  }

}
