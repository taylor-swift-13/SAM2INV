int main1(int m){
  int yo, ea, kt, du1, nrg;
  yo=m-8;
  ea=0;
  kt=0;
  du1=ea;
  nrg=ea;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ea == 0;
  loop invariant yo == \at(m, Pre) - 8;
  loop invariant nrg == ea * kt;
  loop invariant kt >= 0;
  loop invariant (yo >= 0) ==> (kt <= yo);
  loop invariant du1 == ea;
  loop invariant (yo <= 0 ==> kt == 0);
  loop assigns nrg, du1, kt;
*/
while (1) {
      if (kt>=yo) {
          break;
      }
      if (nrg<=du1) {
          du1 = nrg;
      }
      nrg += ea;
      kt++;
  }
}