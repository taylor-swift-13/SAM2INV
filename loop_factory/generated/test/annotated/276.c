int main1(){
  int iq, ko, u3, gy;
  iq=(1%25)+8;
  ko=2;
  u3=1;
  gy=iq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((u3 == 1) || (u3 == 2)) && (gy >= iq);
  loop invariant iq == 1 % 25 + 8;
  loop invariant ko == 2;
  loop assigns gy, u3;
*/
while (ko<=iq-2) {
      if (u3==1) {
          u3 = 2;
      }
      else {
          if (u3==2) {
              u3 = 1;
          }
      }
      gy += u3;
      gy += ko;
  }
}