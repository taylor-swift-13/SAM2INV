int main1(int g){
  int ny, uq, h, m;

  ny=g;
  uq=0;
  h=ny;
  m=-8;

  while (1) {
      if (!(uq < ny)) {
          break;
      }
      uq += 1;
      h = h + m;
      g += uq;
  }

}
