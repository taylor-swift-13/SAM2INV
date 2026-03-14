int main1(int d,int a){
  int ra5, mng2, u, yh, e;
  ra5=18;
  mng2=0;
  u=15;
  yh=1;
  e=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yh == mng2 + 1;
  loop invariant u >= 0;
  loop invariant 1 <= yh;
  loop invariant yh <= ra5 + 1;
  loop invariant u <= 15;
  loop invariant e == yh - 1;
  loop assigns u, e, yh, mng2;
*/
for (; u>0&&yh<=ra5; mng2 = mng2 + 1) {
      if (u>yh) {
          u = u - yh;
      }
      else {
          u = 0;
      }
      e += 1;
      yh = yh + 1;
  }
}