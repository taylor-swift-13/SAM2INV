int main1(int a,int m){
  int t, k, o;

  t=a;
  k=0;
  o=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == a;
  loop invariant o - t == k*(k-1)/2;
  loop invariant t == \at(a, Pre) && o >= t;
  loop invariant o == t + k*(k-1)/2;
  loop invariant a == \at(a, Pre) && m == \at(m, Pre) && t == a;
  loop invariant 0 <= k && o >= t && o - t <= k*(k+1)/2;
  loop invariant t == \at(a, Pre);
  loop invariant 0 <= k;

  loop invariant o >= t;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant o <= t + k*(k+1)/2;
  loop invariant k >= 0;
  loop invariant (t >= 0) ==> (0 <= k && k <= t);
  loop invariant o == a + k*(k-1)/2 && t == a && m == \at(m, Pre) && a == \at(a, Pre);

  loop invariant t + k*(k-1)/2 <= o && o <= t + k*(k+1)/2;
  loop invariant a == \at(a, Pre) && m == \at(m, Pre);
  loop assigns o, k;
*/
while (k<=t-1) {
      o = o+k;
      if (o+6<t) {
          o = o+1;
      }
      k = k+1;
  }

}
