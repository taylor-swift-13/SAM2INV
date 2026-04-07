int main1(){
  int l7k, fy, qcp, u, zl;
  l7k=(1%9)+19;
  fy=0;
  qcp=1;
  u=l7k;
  zl=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= fy <= l7k;
  loop invariant zl == 7 + 3*fy;
  loop invariant qcp > 0;
  loop invariant u > 0;
  loop invariant u >= l7k;
  loop assigns fy, qcp, u, zl;
*/
while (1) {
      if (!(fy < l7k)) {
          break;
      }
      fy++;
      qcp = qcp * u;
      u += qcp;
      zl = zl + 3;
  }
}