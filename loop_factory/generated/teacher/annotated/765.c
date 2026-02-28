int main1(int b,int k,int n,int p){
  int d, s, v, u;

  d=29;
  s=0;
  v=p;
  u=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 4*v - (u - 29) * (u - 29) - 67 * (u - 29) == 4 * \at(p, Pre);
  loop invariant u >= 29;
  loop invariant ((u - 29) % 4) == 0;
  loop invariant v >= p;
  loop invariant p == \at(p, Pre);
  loop invariant 4*(v - \at(p,Pre)) == (u - 29)*(u - 29) + 67*(u - 29);
  loop invariant v >= \at(p,Pre);
  loop invariant b == \at(b,Pre);
  loop invariant k == \at(k,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant 4*v - u*u - 9*u + 1102 == 4*p;
  loop invariant 4*v == 4*p + u*u + 9*u - 1102;
  loop invariant (u - 29) % 4 == 0;
  loop invariant d == 29;
  loop invariant 4*(v - p) == u*u + 9*u - 1102;
  loop assigns v, u;
*/
while (1) {
      v = v+4;
      u = u+4;
      v = v+u+u;
      v = v+1;
  }

}
