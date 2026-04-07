int main1(){
  int svt, jp, hlf, n, x7, y, smzq, vd;
  svt=1;
  jp=-1;
  hlf=0;
  n=1;
  x7=0;
  y=0;
  smzq=jp;
  vd=svt;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant svt == 1;
  loop invariant hlf <= 3;
  loop invariant 0 <= y;
  loop invariant n >= 1;
  loop invariant smzq >= -1;
  loop invariant vd >= 1;
  loop invariant 0 <= hlf;
  loop invariant 0 <= x7;
  loop invariant x7 <= n;
  loop assigns hlf, n, y, x7, smzq, vd;
*/
while (1) {
      if (!(hlf>=0&&hlf<3)) {
          break;
      }
      if (hlf==0&&n>=svt) {
          hlf = 3;
      }
      else {
          if (hlf==1&&x7<n) {
              y = y+n-x7;
              x7++;
          }
          else {
              if (hlf==1&&x7>=n) {
                  hlf = 2;
              }
              else {
                  if (hlf==2) {
                      n += 1;
                      hlf = 0;
                  }
              }
          }
      }
      smzq = smzq + 1;
      vd += hlf;
  }
}