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
