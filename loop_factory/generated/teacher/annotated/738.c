int main1(int b,int m,int n,int p){
  int y, f, v, d, e, g;

  y=p;
  f=y;
  v=b;
  d=1;
  e=m;
  g=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == p;
  loop invariant f <= y;
  loop invariant v == b + 6*(f - y);
  loop invariant d == 1 + (f - y) * b + 3 * (f - y) * (f - y + 1);
  loop invariant e == m + (f - y) + b*(f - y)*(f - y + 1)/2 + (f - y)*(f - y + 1)*(f - y + 2);
  loop invariant v == \at(b, Pre) + 6*(f - \at(p, Pre));
  loop invariant d == 1 + \at(b, Pre)*(f - \at(p, Pre)) + 3*(f - \at(p, Pre))*((f - \at(p, Pre)) + 1);
  loop invariant e == \at(m, Pre) + (f - \at(p, Pre)) + \at(b, Pre)*(((f - \at(p, Pre))*((f - \at(p, Pre)) + 1))/2) + ((f - \at(p, Pre))*((f - \at(p, Pre)) + 1)*((f - \at(p, Pre)) + 2));
  loop invariant p == \at(p, Pre);
  loop invariant v == b + 6*(f - p);
  loop invariant d == 1 + b*(f - p) + 3*(f - p)*(f - p + 1);
  loop invariant e == m + (f - p) + (b*(f - p)*(f - p + 1))/2 + (f - p)*(f - p + 1)*(f - p + 2);
  loop invariant d == 1 + (f - y)*b + 3*(f - y)*((f - y) + 1);
  loop invariant e == m + (f - y) + (b*(f - y)*((f - y) + 1))/2 + (f - y)*((f - y) + 1)*((f - y) + 2);
  loop invariant f >= \at(p,Pre);
  loop invariant v == 6*f + (\at(b,Pre) - 6*\at(p,Pre));
  loop invariant d == 1 + (f - \at(p,Pre))*\at(b,Pre) + 3*(f - \at(p,Pre))*((f - \at(p,Pre)) + 1);
  loop invariant e == \at(m,Pre) + (f - \at(p,Pre)) + \at(b,Pre) * ((f - \at(p,Pre))*((f - \at(p,Pre)) + 1)) / 2 + (f - \at(p,Pre))*((f - \at(p,Pre)) + 1)*((f - \at(p,Pre)) + 2);
  loop assigns v, f, d, e;
*/
while (1) {
      if (f>=y) {
          break;
      }
      v = v+3;
      f = f+1;
      v = v+3;
      d = d+v;
      e = e+d;
  }

}
