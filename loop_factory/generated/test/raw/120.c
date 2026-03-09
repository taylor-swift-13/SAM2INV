int main1(int z,int x){
  int pn2z, y, tr, ky;

  pn2z=141;
  y=-6;
  tr=0;
  ky=-6;

  while (1) {
      if (!(tr<pn2z)) {
          break;
      }
      tr += 1;
      z = z + y;
      ky = pn2z-tr;
  }

}
