int main1(int n,int q){
  int m, k, x, v;

  m=(q%6)+4;
  k=0;
  x=k;
  v=8;

  while (k+3<=m) {
      if (k<m/2) {
          x = x+v;
      }
      else {
          x = x+1;
      }
      v = v+v;
  }

}
