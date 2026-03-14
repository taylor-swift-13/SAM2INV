int main1(int v){
  int yt, pz, ce, fr;
  yt=v+6;
  pz=0;
  ce=0;
  fr=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ce <= 10;
  loop invariant yt == \at(v, Pre) + 6;
  loop invariant fr == 1 || fr == -1;
  loop assigns ce, fr, pz;
*/
while (pz<yt) {
      if (ce>=10) {
          fr = -1;
      }
      if (ce<=0) {
          fr = 1;
      }
      ce += fr;
      pz = pz + 1;
  }
}