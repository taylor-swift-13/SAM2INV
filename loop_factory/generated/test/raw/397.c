int main1(){
  int z1d, qbf, a1, o, cz;

  z1d=42;
  qbf=0;
  a1=0;
  o=5;
  cz=0;

  while (qbf<z1d) {
      cz += 1;
      o = o + 1;
      if (o>=4) {
          o -= 4;
          a1 += 1;
      }
      qbf++;
  }

}
