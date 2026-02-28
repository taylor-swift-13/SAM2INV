int main1(int k,int q){
  int m, v, t, d;

  m=(k%22)+20;
  v=0;
  t=0;
  d=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= t;

  loop invariant (t <= m/2) ==> (d == t);

  loop invariant m >= 0 ==> (0 <= t && t <= m);
  loop invariant m == ((\at(k, Pre) % 22) + 20);

  loop invariant d <= t;
  loop assigns d, t;
*/
while (t<m) {
      if (t<m/2) {
          d = d+1;
      }
      else {
          d = d-1;
      }
      t = t+1;
  }

}
