int main1(int a,int n,int p,int q){
  int b, j, v, e, y, z, c;

  b=27;
  j=b;
  v=b;
  e=-8;
  y=n;
  z=-8;
  c=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v == 6*j - 5*b;
  loop invariant e == -8 + (j - 27)*27 + 3*(j - 27)*(j - 26);
  loop invariant v == 6*j - 135;
  loop invariant e == -8 + 3*(j - 27)*(j - 27) + 30*(j - 27);
  loop invariant j >= 27;
  loop invariant v - 27 == 6*(j - 27);
  loop invariant j <= b;
  loop assigns v, j, e;
*/
while (1) {
      if (j>=b) {
          break;
      }
      v = v+1;
      j = j+1;
      v = v+5;
      e = e+v;
  }

}
