int main1(int n,int p){
  int x, u, w;

  x=65;
  u=x;
  w=p;

  while (u>0) {
      if ((u%4)==0) {
          w = w+1;
      }
      u = u-1;
  }

}
