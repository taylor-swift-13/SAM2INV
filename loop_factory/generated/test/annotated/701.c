int main1(){
  int ueq, hwng, l7y8, wtz;
  ueq=0;
  hwng=0;
  l7y8=0;
  wtz=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hwng == l7y8;
  loop invariant ueq >= 7 * l7y8;
  loop invariant l7y8 >= 0;
  loop invariant ueq % 7 == 0;
  loop invariant l7y8 <= 6;
  loop invariant l7y8 + wtz == 6;
  loop assigns wtz, l7y8, ueq, hwng;
*/
while (wtz>0) {
      wtz = (wtz)+(-(1));
      l7y8 = l7y8+1*1;
      ueq = ueq+1*1;
      hwng = hwng+1*1;
      ueq = ueq*3+4;
  }
}