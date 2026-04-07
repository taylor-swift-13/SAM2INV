int main1(int o){
  int dz, fk, e, cbp, xb, np4;
  dz=o-8;
  fk=1;
  e=fk;
  cbp=dz;
  xb=8;
  np4=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (cbp - e) == (dz - 1);
  loop invariant ((xb - ((e - 1) * (e + 2)) / 2) == 8);
  loop invariant e == np4 - 6;
  loop invariant cbp - dz == np4 - 7;
  loop invariant xb == 8 + (np4 - 7) * (np4 - 4) / 2;
  loop invariant xb == ((e * (e + 1)) / 2) + 7;
  loop invariant (np4 - e) == 6;
  loop invariant cbp == dz + (e - 1);
  loop invariant np4 == e + 6;
  loop invariant xb == 8 + ((e - 1) * (e + 2)) / 2;
  loop invariant cbp - e == \at(o, Pre) - 9;
  loop invariant np4 - e == 6;
  loop assigns e, cbp, np4, xb;
*/
while (e<dz) {
      e += 1;
      cbp = cbp + 1;
      np4++;
      xb = xb + e;
  }
}