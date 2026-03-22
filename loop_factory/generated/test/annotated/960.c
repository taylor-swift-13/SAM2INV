int main1(int z){
  int nw6, siy, bu;
  nw6=z;
  siy=nw6;
  bu=siy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (bu - siy) >= 0;
  loop invariant 5*(bu - \at(z,Pre)) == \at(z,Pre) - siy;
  loop invariant siy <= \at(z,Pre);
  loop invariant bu - siy == 6 * ((z - siy) / 5);
  loop invariant ((z - siy) % 5) == 0;
  loop assigns bu, siy;
*/
for (; siy>4; siy = siy - 5) {
      bu += 1;
  }
}