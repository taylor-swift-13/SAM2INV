int main1(){
  int sw, yu, oea, l, wgs, mc;

  sw=1*3;
  yu=0;
  oea=1;
  l=6;
  wgs=0;
  mc=sw;

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
