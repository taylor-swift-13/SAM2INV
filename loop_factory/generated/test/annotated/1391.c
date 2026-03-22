int main1(){
  int sw, yu, oea, l, wgs, mc;
  sw=1*3;
  yu=0;
  oea=1;
  l=6;
  wgs=0;
  mc=sw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yu == wgs*wgs*wgs;
  loop invariant oea == 1 + 3*wgs*(wgs+1);
  loop invariant l == 6*(wgs+1);
  loop invariant 4*mc == wgs*wgs*wgs*wgs + 6*wgs*wgs*wgs + 13*wgs*wgs + 12*wgs + 12;
  loop invariant wgs >= 0;
  loop invariant wgs <= sw + 1;
  loop assigns wgs, yu, oea, l, mc;
*/
while (1) {
      if (!(wgs<=sw)) {
          break;
      }
      wgs++;
      yu = yu + oea;
      oea += l;
      l += 6;
      mc = mc+yu+oea;
  }
}