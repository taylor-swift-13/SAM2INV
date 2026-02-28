int main1(int b,int m){
  int d, t, v;

  d=m;
  t=0;
  v=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (m == \at(m, Pre));
  loop invariant (d == m);
  loop invariant v == t*(t - 1) / 2;
  loop invariant t >= 0;
  loop invariant m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant d == m;
  loop assigns v, t;
*/
while (1) {
      v = v+t;
      t = t+1;
  }

}
