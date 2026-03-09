int main1(){
  int bz1, v0um, hh6, b09u, hl;
  bz1=11;
  v0um=bz1;
  hh6=v0um;
  b09u=v0um;
  hl=bz1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant hh6 == 11;
  loop invariant bz1 == 11;
  loop invariant v0um >= 11;
  loop invariant hl == 14*v0um - 143;
  loop invariant b09u == 2*v0um - 11;
  loop assigns hl, b09u, hh6, v0um;
*/
while (1) {
      if (!(v0um-3>=0)) {
          break;
      }
      if (!(!(hh6+3<=bz1))) {
          hh6 = hh6 + 3;
      }
      else {
          hh6 = bz1;
      }
      hl += hh6;
      b09u += 2;
      hl = hl + 3;
      v0um += 1;
  }
}