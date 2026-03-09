int main1(){
  int is8, nr, ssc, i6cn;
  is8=(1%14)+13;
  nr=0;
  ssc=is8;
  i6cn=nr;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i6cn == ssc*(ssc+1)/2 - is8*(is8+1)/2;
  loop invariant 0 <= ssc <= is8;
  loop invariant i6cn == 14*(ssc - 14) + ((ssc - 14)*(ssc - 13)) / 2;
  loop assigns ssc, i6cn;
*/
while (1) {
      if (!(ssc<is8)) {
          break;
      }
      ssc += 1;
      i6cn = i6cn + ssc;
  }
}