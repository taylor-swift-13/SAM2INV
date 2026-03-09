int main1(){
  int kka, p, ym4;
  kka=(1%20)+5;
  p=(1%20)+5;
  ym4=(1%20)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kka == ym4;
  loop invariant 0 <= ym4;
  loop invariant p >= 0;
  loop invariant ym4 <= (1%20)+5;
  loop assigns kka, p, ym4;
*/
while (kka>=1) {
      if (p>0) {
          if (ym4>0) {
              kka = kka - 1;
              p -= 1;
              ym4--;
          }
      }
      p = p+ym4+ym4;
  }
}