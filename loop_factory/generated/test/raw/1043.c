int main1(int f,int d){
  int ijk, rx6, s, faa, m8;

  ijk=d-4;
  rx6=0;
  s=0;
  faa=d;
  m8=ijk;

  while (rx6<ijk) {
      s += rx6;
      faa = faa + s;
      rx6 = rx6 + 1;
  }

  while (1) {
      if (!(s+1<=m8)) {
          break;
      }
      s++;
  }

}
