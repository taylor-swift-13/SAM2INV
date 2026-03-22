int main1(){
  int afog, wd, ny7, a, kto;
  afog=1;
  wd=afog;
  ny7=0;
  a=1;
  kto=(1%35)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ny7 >= 0;
  loop invariant afog == 1;
  loop invariant 0 <= kto <= 9;
  loop invariant a == ny7 + 1;
  loop assigns a, wd, ny7, kto;
*/
while (kto>0) {
      a = a+kto*kto;
      wd = wd+ny7*ny7;
      ny7 = (kto*kto)+(ny7);
      wd = wd*4+5;
      kto -= 1;
  }
}