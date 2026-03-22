int main1(){
  int a, mk, waa, v5, wiz, gt, ky5i;
  a=66;
  mk=0;
  waa=1;
  v5=0;
  wiz=0;
  gt=a;
  ky5i=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == 66;
  loop invariant 0 <= mk <= 3;
  loop invariant 0 <= v5 <= waa;
  loop invariant 1 <= waa;
  loop invariant wiz >= 0;
  loop invariant ky5i - wiz >= 66;
  loop invariant ky5i >= 66;
  loop invariant gt >= 66;
  loop assigns mk, v5, wiz, waa, ky5i, gt;
*/
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