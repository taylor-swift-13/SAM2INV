int main1(int y){
  int uh4, d3e, d7se, l, a9, d;

  uh4=(y%11)+19;
  d3e=0;
  d7se=d3e;
  l=3;
  a9=-1;
  d=0;

  while (1) {
      if (d>uh4) {
          break;
      }
      d7se += l;
      l += a9;
      a9 += 2;
      d++;
      y += d;
  }

}
