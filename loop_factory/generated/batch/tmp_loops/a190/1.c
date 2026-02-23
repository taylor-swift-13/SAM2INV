int main1(int m,int q){
  int e, u, j, v;

  e=(m%15)+8;
  u=0;
  j=m;
  v=e;

  while (u<e) {
      if (u<e/2) {
          j = j+v;
      }
      else {
          j = j*v;
      }
      j = j*2;
  }

}
