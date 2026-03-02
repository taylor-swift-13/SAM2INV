int main1(int n,int p){
  int u, x, v;

  u=(n%31)+20;
  x=0;
  v=-5;

  while (1) {
      v = v+2;
      if ((x%8)==0) {
          v = v+x;
      }
  }

}
