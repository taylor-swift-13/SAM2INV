int main1(int k,int m){
  int l, t, v, b;

  l=52;
  t=0;
  v=2;
  b=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant l == 52;
  loop invariant t == 0;
  loop invariant v >= 2;
  loop invariant b >= -2;
  loop invariant v % 7 == 2;
  loop invariant b % 2 == 0;
  loop invariant (v - 2) % 7 == 0;
  loop invariant 0 <= t;
  loop invariant t <= l;
  loop assigns v, b;
*/
while (t<=l-1) {
      v = v+2;
      v = v+5;
      b = b+v;
      b = b+b;
  }

}
