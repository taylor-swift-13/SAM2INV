int main1(){
  int frd, njx, gxj;
  frd=(1%22)+7;
  njx=frd;
  gxj=(1%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant frd == 8;
  loop invariant gxj >= 0;
  loop invariant njx >= frd;
  loop invariant njx <= frd + 1;
  loop invariant gxj <= 9;
  loop invariant gxj == 0 || njx == frd;
  loop assigns gxj, njx;
*/
while (gxj>0&&gxj>0) {
      if (njx%2==0) {
          gxj = gxj - 1;
      }
      else {
          gxj = gxj - 1;
      }
      njx = njx + 1;
      gxj = gxj - gxj;
  }
}