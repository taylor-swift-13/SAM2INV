int main1(int m,int q){
  int e, u, j, v, f;

  e=(m%12)+16;
  u=0;
  j=-8;
  v=m;
  f=e;

  while (u<e) {
      j = j+v+f;
      u = u+1;
  }

}
