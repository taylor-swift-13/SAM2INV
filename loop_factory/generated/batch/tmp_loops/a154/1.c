int main1(int b,int q){
  int h, g, u, v;

  h=(b%13)+6;
  g=h;
  u=q;
  v=b;

  while (g-4>=0) {
      u = u+1;
      v = v+1;
      u = u+2;
  }

}
