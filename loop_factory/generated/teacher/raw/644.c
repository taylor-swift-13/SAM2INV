int main1(int b,int q){
  int n, h, g, l, u, d;

  n=30;
  h=n;
  g=h;
  l=h;
  u=-2;
  d=b;

  while (g!=0&&l!=0) {
      if (g>l) {
          g = g-l;
      }
      else {
          l = l-g;
      }
  }

}
