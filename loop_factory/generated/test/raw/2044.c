int main1(int z){
  int q, kj, c, s;

  q=18;
  kj=0;
  c=0;
  s=z;

  while (kj < q) {
      kj = (c += (2*kj < q ? 1 : -1), kj + 1);
      c += 2;
      s = s + c;
      z = z + c;
  }

}
