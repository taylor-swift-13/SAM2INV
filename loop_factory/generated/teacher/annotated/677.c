int main1(int b,int k,int m,int n){
  int c, u, t, v, x, w;

  c=10;
  u=0;
  t=u;
  v=k;
  x=m;
  w=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant c == 10;
  loop invariant t == 0;
  loop invariant u == 0;
  loop assigns t, u;
*/
while (1) {
      t = t*2;
      u = u+0;
  }

}
