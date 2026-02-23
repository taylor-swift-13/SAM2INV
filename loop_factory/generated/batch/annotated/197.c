int main1(int k,int m){
  int l, t, v, b;

  l=52;
  t=0;
  v=2;
  b=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t <= l;
  loop invariant v == 2 + 4*t;
  loop invariant b == -2 + 3*t;
  loop invariant l == 52;
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant t >= 0;
  loop assigns v, b, t;
*/
while (t<=l-1) {
      v = v+4;
      b = b+3;
      t = t+1;
  }

}
