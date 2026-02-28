int main1(int a,int b,int k,int m){
  int y, u, l, v, t, w;

  y=63;
  u=1;
  l=u;
  v=5;
  t=m;
  w=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == u;
  loop invariant u == 1;
  loop invariant t >= m;
  loop invariant a == \at(a,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant y == 63;
  loop invariant v == 5 + (t - m) * (m + 2) + (t - m) * (t - m - 1) / 2;
  loop invariant b == \at(b,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant l == 1;
  loop invariant v == 5 + (t - m) * (m + 2) + ((t - m) * (t - m - 1)) / 2;
  loop invariant 2*v == t*t + 3*t - 3*m - m*m + 10;
  loop assigns v, t;
*/
while (1) {
      v = v+l;
      v = v+t;
      t = t+l;
      if ((u%2)==0) {
          t = t+u;
      }
      else {
          v = v+u;
      }
  }

}
