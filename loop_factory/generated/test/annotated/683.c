int main1(){
  int bx, mr, jp, ut, bqk;
  bx=(1%18)+7;
  mr=0;
  jp=(1%40)+2;
  ut=0;
  bqk=mr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bqk == 3 - jp;
  loop invariant (jp == 2) || (jp == 3);
  loop invariant bx == 8;
  loop invariant (ut == 0) || (ut == 2) || (ut == 3);
  loop assigns ut, jp, bqk;
*/
while (1) {
      if (!(jp!=ut)) {
          break;
      }
      ut = jp;
      jp = (jp+bx/jp)/2;
      bqk = bqk+ut-jp;
  }
}