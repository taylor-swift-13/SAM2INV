int main1(int p,int q){
  int u, e, y;

  u=67;
  e=0;
  y=e;

  while (e+1<=u) {
      y = y+3;
      y = y*y;
      if ((e%7)==0) {
          y = y*y;
      }
      else {
          y = y*y;
      }
  }

}
