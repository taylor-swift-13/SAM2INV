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
