int main1(){
  int nf9, pf, c;
  nf9=(1%30)+4;
  pf=0;
  c=nf9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pf <= nf9;
  loop invariant c >= 5;
  loop invariant c >= nf9;
  loop invariant ((c + 4) % (nf9 + 4) == 0);
  loop invariant (pf == 0 ==> c == nf9) && (pf >= 0);
  loop invariant 0 <= pf;
  loop invariant nf9 == 5;
  loop invariant c >= nf9 + 2*pf;
  loop invariant pf >= 0;
  loop assigns c, pf;
*/
while (pf<nf9) {
      c += 2;
      pf++;
      c = c + c;
  }
}