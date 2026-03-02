int main1(int a,int k){
  int y, u, v;

  y=a;
  u=0;
  v=u;

  while (1) {
      v = v+3;
      if ((u%4)==0) {
          v = v*v+v;
      }
  }

}
