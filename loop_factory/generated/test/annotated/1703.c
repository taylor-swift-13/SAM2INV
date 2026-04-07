int main1(int v){
  int bk8o, nx, ej, e09;
  bk8o=v;
  nx=0;
  ej=0;
  e09=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bk8o == \at(v, Pre);
  loop invariant v >= \at(v, Pre);
  loop invariant (nx == 0) || (nx == bk8o);
  loop invariant (e09 == 0) || (e09 == ej + v);
  loop invariant (nx == 0) ==> (v == \at(v, Pre));
  loop invariant (nx > 0) ==> (e09 == ej + v);
  loop invariant ej == 0;
  loop assigns nx, v, e09;
*/
while (nx < bk8o) {
      if (bk8o>nx) {
          nx = bk8o;
      }
      v++;
      e09 = e09+ej-e09;
      e09 += v;
  }
}