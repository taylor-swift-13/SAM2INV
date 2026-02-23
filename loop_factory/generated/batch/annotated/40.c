int main1(int b,int q){
  int j, t, x, s, v, d;

  j=b;
  t=0;
  x=j;
  s=0;
  v=q;
  d=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3*s == v*t;

  loop invariant t >= 0;
  loop invariant v == \at(q, Pre);
  loop invariant j == \at(b, Pre);
  loop invariant t % 3 == 0;
  loop invariant s == v * (t / 3);
  loop invariant (j <= 0) || t <= j + 2;


  loop invariant v == q;
  loop invariant j == b;
  loop invariant s == (t/3) * v;
  loop assigns s, t;
*/
while (t<j) {
      s = s+v;
      t = t+3;
  }

}
