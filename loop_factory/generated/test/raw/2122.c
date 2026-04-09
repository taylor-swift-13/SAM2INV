int main1(){
  int it, z2, ro, d, p;

  it=(1%25)+11;
  z2=0;
  ro=z2;
  d=6;
  p=it;

  while (z2 < it) {
      z2 = (p = p + 1, d = d - 1, z2 + 1);
      ro += 2;
      p++;
      ro = ro+d+p;
  }

}
