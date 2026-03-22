int main1(){
  int gs, eut, pz, p, od, y, i, n4, trc;
  gs=44;
  eut=0;
  pz=0;
  p=0;
  od=eut;
  y=gs;
  i=gs;
  n4=-8;
  trc=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p == 3 * eut;
  loop invariant od == 3 * eut;
  loop invariant n4 == -8 + gs * eut;
  loop invariant pz >= 0;
  loop invariant (eut == 0) ==> (i == p + od + y);
  loop invariant (eut > 0) ==> (i == p + od + y - 1);
  loop invariant 0 <= eut <= gs;
  loop assigns pz, trc, n4, p, od, i, eut;
*/
while (1) {
      if (eut<gs/2) {
          pz += p;
      }
      else {
          pz = pz + 1;
      }
      if (eut+5<=n4+gs) {
          trc += n4;
      }
      n4 += gs;
      p += 2;
      od = od + 3;
      i = p+od+y;
      p++;
      if ((eut%4)==0) {
          trc = trc + od;
      }
      eut++;
      if (eut>=gs) {
          break;
      }
  }
}