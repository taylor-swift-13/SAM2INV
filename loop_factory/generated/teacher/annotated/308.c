int main1(int k,int m){
  int f, x, v, q;

  f=33;
  x=f;
  v=x;
  q=f;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v > 0;

  loop invariant v + q <= 66;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v >= 0;
  loop invariant q >= 0;
  loop invariant v % 33 == 0;
  loop invariant q % 33 == 0;
  loop invariant f == 33;
  loop invariant 0 <= v;
  loop invariant 0 <= q;
  loop invariant v <= 33;
  loop invariant q <= 33;
  loop assigns v, q;
*/
while (v!=0&&q!=0) {
      if (v>q) {
          v = v-q;
      }
      else {
          q = q-v;
      }
  }

}
