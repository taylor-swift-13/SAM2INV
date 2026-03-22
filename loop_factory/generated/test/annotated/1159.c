int main1(){
  int lp, zwv, rs77, cpg, njb;
  lp=43;
  zwv=0;
  rs77=0;
  cpg=(1%28)+10;
  njb=lp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cpg == ((1%28) + 10) - rs77*(rs77 - 1)/2;
  loop invariant njb == 43 + rs77*(lp + zwv);
  loop invariant rs77 >= 0;
  loop assigns cpg, rs77, njb;
*/
while (1) {
      if (!(cpg>rs77)) {
          break;
      }
      cpg = cpg - rs77;
      rs77 = rs77 + 1;
      njb += lp;
      njb = njb + zwv;
  }
}