int main1(int k,int p){
  int r, c, v, y, l, s;

  r=30;
  c=r+3;
  v=r;
  y=-8;
  l=k;
  s=r;

  while (1) {
      if (v>=r) {
          break;
      }
      if (l<=y) {
          y = l;
      }
      v = v+1;
      v = v+c;
  }

}
