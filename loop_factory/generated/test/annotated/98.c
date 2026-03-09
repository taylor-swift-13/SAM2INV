int main1(){
  int kpp, ik3g, pz30;
  kpp=1;
  ik3g=0;
  pz30=kpp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pz30 == 1 + 6*ik3g;
  loop invariant 0 <= ik3g <= kpp;
  loop invariant (ik3g >= kpp/2) ==> (pz30 == 1 + 2*ik3g + 4*(ik3g - kpp/2));
  loop assigns ik3g, pz30;
*/
while (ik3g<kpp) {
      if (ik3g>=kpp/2) {
          pz30 += 4;
      }
      ik3g = ik3g + 1;
      pz30 += 2;
  }
}