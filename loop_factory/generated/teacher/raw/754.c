int main1(int k,int m,int n,int p){
  int s, w, v, u;

  s=(p%14)+18;
  w=0;
  v=w;
  u=m;

  while (1) {
      if (w>=s) {
          break;
      }
      v = v+3;
      w = w+1;
      v = v+5;
      u = u+v;
  }

}
