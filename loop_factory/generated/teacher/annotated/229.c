int main1(int k,int m){
  int l, t, v, b;

  l=52;
  t=0;
  v=2;
  b=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= t <= l;
  loop invariant v >= 2;
  loop invariant v % 2 == 0;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant t >= 0;
  loop invariant t <= l;
  loop invariant l == 52;
  loop invariant v >= 0;
  loop invariant 0 <= t;
  loop invariant ((t == 0) ==> (v == 2)) && ((t > 0) ==> (v % 3 == 0));
  loop assigns v, t;
*/
while (t<=l-1) {
      v = v*3;
      t = t+1;
  }

}
