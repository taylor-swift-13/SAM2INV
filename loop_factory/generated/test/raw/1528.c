int main1(){
  int a, mk, waa, v5, wiz, gt, ky5i;

  a=66;
  mk=0;
  waa=1;
  v5=0;
  wiz=0;
  gt=a;
  ky5i=a;

  while (1) {
      if (!(mk>=0&&mk<3)) {
          break;
      }
      if (!(!(mk==0&&waa>=a))) {
          mk = 3;
      }
      else {
          if (mk==1&&v5<waa) {
              wiz = wiz+waa-v5;
              v5 = v5 + 1;
          }
          else {
              if (mk==1&&v5>=waa) {
                  mk = 2;
              }
              else {
                  if (mk==2) {
                      waa++;
                      mk = 0;
                  }
              }
          }
      }
      ky5i += wiz;
      gt += mk;
  }

}
