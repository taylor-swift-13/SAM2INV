int main1(int k,int m){
  int f, x, v, q;

  f=33;
  x=0;
  v=0;
  q=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (v <= f);
  loop invariant (v < f/2) ==> (q == 2*v);
  loop invariant (v >= f/2) ==> (q == 2*(f - 1 - v));
  loop invariant (q % 2 == 0);
  loop invariant (k == \at(k, Pre));
  loop invariant (m == \at(m, Pre));
  loop invariant v <= f;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= v && v <= f;
  loop invariant (v <= f/2) ==> q == 2*v;
  loop invariant -2*v <= q && q <= 2*v;
  loop invariant q % 2 == 0;
  loop invariant f == 33;
  loop invariant q % 2 == 0 && k == \at(k, Pre) && m == \at(m, Pre);
  loop invariant k == \at(k, Pre) && m == \at(m, Pre) && v <= f;
  loop invariant v <= f && q % 2 == 0 && -2*v <= q && q <= 2*v;

  loop invariant 0 <= v;
  loop invariant (v < f/2) ==> (q <= 2*v);
  loop invariant (v >= f/2) ==> (q <= 2*(f - 1 - v));
  loop invariant 0 <= v <= f;
  loop invariant (v <= f/2) ==> (q == 2*v);
  loop assigns q, v;
*/
while (v<f) {
      if (v<f/2) {
          q = q+2;
      }
      else {
          q = q-2;
      }
      v = v+1;
  }
/*@
  assert !(v<f) &&
         ((v <= f));
*/


}
