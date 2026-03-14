int main1(int z){
  int mbr, k, ba, gh9, kw, ka;

  mbr=z;
  k=mbr;
  ba=41;
  gh9=0;
  kw=1;
  ka=0;

  while (ba>0&&k<mbr) {
      if (ba<=kw) {
          ka = ba;
      }
      else {
          ka = kw;
      }
      k += 1;
      gh9 += ka;
      ba -= ka;
      kw++;
  }

}
