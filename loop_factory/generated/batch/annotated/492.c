int main1(int b,int k){
  int v, o, t, d;

  v=b+23;
  o=0;
  t=k;
  d=o;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t >= k;
  loop invariant (t - k) % 3 == 0;
  loop invariant d == 0 || d == 4;
  loop invariant v == b + 23;
  loop invariant k == \at(k, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant (t - \at(k, Pre)) % 3 == 0;
  loop invariant t >= \at(k, Pre);
  loop invariant (b == \at(b, Pre));
  loop invariant (k == \at(k, Pre));
  loop invariant (t >= k);
  loop invariant ((t - k) % 3 == 0) && (d == 0 || d == 4) && (v == b + 23);
  loop invariant d == 0 ==> t == k;
  loop invariant (d == 0) || (d == 4);
  loop assigns d, t;
*/
while (1) {
      d = t;
      t = t+2;
      t = t+1;
      d = d-1;
      d = t-d;
  }

}
