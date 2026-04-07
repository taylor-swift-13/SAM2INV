int main1(){
  int qm, v, x, s9d, xf, qok6, fc2u, l4;
  qm=9;
  v=2;
  x=0;
  s9d=1;
  xf=0;
  qok6=0;
  fc2u=qm;
  l4=v;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= xf;
  loop invariant xf <= s9d;
  loop invariant 1 <= s9d;
  loop invariant qm == 9;
  loop invariant l4 == 2;
  loop invariant qok6 >= 0;
  loop invariant fc2u - xf >= 9;
  loop assigns fc2u, x, xf, s9d, qok6;
*/
while (x>=0&&x<3) {
      if (x==0&&s9d>=qm) {
          x = 3;
      }
      else {
          if (x==1&&xf<s9d) {
              qok6 = qok6+s9d-xf;
              xf = xf + 1;
          }
          else {
              if (x==1&&xf>=s9d) {
                  x = 2;
              }
              else {
                  if (x==2) {
                      s9d += 1;
                      x = 0;
                  }
              }
          }
      }
      fc2u += xf;
      fc2u = fc2u+l4+l4;
  }
}