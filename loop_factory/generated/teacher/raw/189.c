int main1(int k,int n){
  int r, u, g, v;

  r=(k%34)+7;
  u=0;
  g=6;
  v=3;

  while (u+1<=r) {
      g = g+3;
      v = v+g;
      v = v+v;
      u = u+1;
  }

}
