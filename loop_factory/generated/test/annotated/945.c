int main1(){
  int bb, tv, lw;
  bb=0;
  tv=(1%20)+10;
  lw=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tv == 11 - ((bb + 1) / 2);
  loop invariant lw == 9 - (bb / 2);
  loop invariant 0 <= bb;
  loop invariant bb <= 18;
  loop invariant tv >= 0;
  loop invariant lw >= 0;
  loop invariant tv + lw + bb == 20;
  loop assigns bb, tv, lw;
*/
for (; tv>0&&lw>0; bb++) {
      if (!(!(bb%2==0))) {
          tv--;
      }
      else {
          lw = lw - 1;
      }
  }
}