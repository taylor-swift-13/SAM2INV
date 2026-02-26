int main1(int k,int p){
  int b, u, v, g;

  b=54;
  u=1;
  v=b;
  g=k;

  while (1) {
      if (u>=b) {
          break;
      }
      v = v+3;
      u = u+1;
      v = v+1;
      g = g-1;
  }

}
