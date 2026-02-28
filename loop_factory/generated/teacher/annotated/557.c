int main1(int b,int k){
  int v, o, t, d;

  v=b+23;
  o=0;
  t=k;
  d=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == k + 3*o;
  loop invariant 0 <= o;
  loop invariant t >= k;
  loop invariant v == b + 23;
  loop invariant k == \at(k, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant t == \at(k, Pre) + 3*o;
  loop invariant o >= 0;

  loop invariant v == \at(b, Pre) + 23;
  loop assigns o, t;
*/
while (1) {
      if (o>=v) {
          break;
      }
      t = t+3;
      o = o+1;
  }

}
