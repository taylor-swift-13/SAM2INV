int main1(int b,int p){
  int u, v, e, n;

  u=p-7;
  v=0;
  e=u;
  n=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == p - 7;
  loop invariant e >= p - 7;
  loop invariant (e - p) % 7 == 0;
  loop invariant e >= (\at(p, Pre) - 7);
  loop invariant ((e - (\at(p, Pre) - 7)) % 7 == 0);
  loop invariant (p == \at(p, Pre));
  loop invariant n >= 3;
  loop invariant v == 0;
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant e >= \at(p, Pre) - 7;
  loop invariant (e - (\at(p, Pre) - 7)) % 7 == 0;
  loop invariant e <= p + 7*n - 21;
  loop invariant e >= u;
  loop assigns e, n;
*/
while (1) {
      e = e+1;
      n = n-1;
      n = n+n;
      e = e+6;
      n = n+v;
  }

}
