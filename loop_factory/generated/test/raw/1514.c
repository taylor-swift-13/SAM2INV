int main1(){
  int t, y, x, ag5k, kme, dps8, y5, yxo;

  t=1+23;
  y=0;
  x=0;
  ag5k=0;
  kme=0;
  dps8=0;
  y5=0;
  yxo=0;

  while (1) {
      if (!(y<t+(1%7))) {
          break;
      }
      if (y%11==0) {
          x = x + 1;
      }
      else {
          if (y%10==0) {
              ag5k = ag5k + 1;
          }
          else {
              if (y%8==0) {
                  kme += 1;
              }
              else {
                  if (1) {
                      dps8 += 1;
                  }
              }
          }
      }
      y++;
      yxo = yxo+y%8;
      y5 += x;
  }

}
