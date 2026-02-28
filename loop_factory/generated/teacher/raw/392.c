int main1(int m,int q){
  int e, u, j, v;

  e=(m%15)+8;
  u=0;
  j=m;
  v=e;

  while (j!=0&&v!=0) {
      if (j>v) {
          j = j-v;
      }
      else {
          v = v-j;
      }
      j = j+4;
  }

}
