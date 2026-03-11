int main1(int s,int z){
  int m, hg, b5bi, h;

  m=z;
  hg=3;
  b5bi=3;
  h=1;

  for (; hg<=m-1; hg = hg + 1) {
      if (b5bi>=12) {
          h = -1;
      }
      if (!(b5bi>3)) {
          h = 1;
      }
      b5bi += h;
  }

}
