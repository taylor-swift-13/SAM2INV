int main1(){
  int e3, fub3, dl, z0;
  e3=40;
  fub3=0;
  dl=e3;
  z0=e3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z0 == dl;
  loop invariant 0 <= fub3 <= e3;
  loop invariant ((fub3 == 0) ==> (dl == e3) && (z0 == e3));
  loop invariant ((fub3 > 0) ==> (dl == fub3) && (z0 == fub3));
  loop assigns fub3, dl, z0;
*/
while (fub3 < e3) {
      fub3 += 1;
      dl = fub3;
      z0 = dl;
  }
}