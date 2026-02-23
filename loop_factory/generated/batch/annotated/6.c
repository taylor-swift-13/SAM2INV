int main1(int k,int m){
  int j, d, l, o, u, y;

  j=46;
  d=j;
  l=-2;
  o=j;
  u=m;
  y=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= d && d <= j;
  loop invariant l == -2 + 4*(j - d);
  loop invariant u == \at(m, Pre) + 2*(j - d);
  loop invariant m == \at(m, Pre);
  loop invariant l + 4*d == 182;
  loop invariant u + 2*d == m + 92;
  loop invariant d >= 0;
  loop invariant k == \at(k, Pre);
  loop invariant u + 2*d == \at(m, Pre) + 92;
  loop invariant 0 <= d;
  loop invariant d <= 46;
  loop assigns l, u, d;
*/
while (d>0) {
      l = l+4;
      u = u+2;
      d = d-1;
  }

}
