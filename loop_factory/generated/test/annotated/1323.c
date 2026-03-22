int main1(int l,int y){
  int cwna, etq, vcf, ev, av, b1;
  cwna=58;
  etq=cwna;
  vcf=0;
  ev=1;
  av=1;
  b1=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant av == 1 + 2 * vcf;
  loop invariant b1 == 5 + etq * vcf;
  loop invariant ev == (vcf + 1) * (vcf + 1);
  loop invariant vcf >= 0;
  loop invariant cwna == etq;
  loop assigns vcf, av, b1, ev;
*/
while (ev<=cwna) {
      vcf++;
      av += 2;
      b1 += etq;
      ev = ev + av;
  }
}