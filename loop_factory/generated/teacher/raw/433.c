int main1(int a,int k){
  int v, r, g, p;

  v=(a%18)+14;
  r=v;
  g=-8;
  p=0;

  while (g!=0&&p!=0) {
      if (g>p) {
          g = g-p;
      }
      else {
          p = p-g;
      }
      g = g*g+g;
  }

}
