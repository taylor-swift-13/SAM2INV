int main1(){
  int i9y, yg, oer, t;
  i9y=11;
  yg=0;
  oer=0;
  t=1*4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yg == (oer % 7);
  loop invariant i9y == 11;
  loop invariant 0 <= oer <= i9y;
  loop invariant t == 4 + 21*(oer/7) + ((oer%7) * ((oer%7) + 1)) / 2;
  loop assigns yg, oer, t;
*/
while (oer<i9y) {
      yg = (yg+1)%7;
      oer += 1;
      t += yg;
  }
}