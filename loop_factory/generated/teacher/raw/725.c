int main1(int k,int m,int n,int q){
  int x, u, v;

  x=44;
  u=0;
  v=u;

  while (1) {
      v = v+4;
      if (v+3<x) {
          v = v+1;
      }
      else {
          v = v+v;
      }
  }

}
