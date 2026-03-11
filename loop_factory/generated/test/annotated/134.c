int main1(){
  int psj, n0, bcp, hd;
  psj=(1%13)+17;
  n0=psj;
  bcp=-1;
  hd=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant psj == n0;
  loop invariant hd >= 0;
  loop invariant (bcp == -1 && hd == 0) || (hd + bcp == psj + n0);
  loop invariant (-1 <= bcp && bcp <= psj);
  loop invariant (bcp >= 0) ==> (hd + bcp == psj + n0);
  loop assigns bcp, hd;
*/
while (bcp<psj) {
      bcp = bcp + 1;
      hd = psj-bcp;
      if (psj<psj+3) {
          hd += n0;
      }
  }
}