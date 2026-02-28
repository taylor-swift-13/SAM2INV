int main1(int k,int q){
  int m, v, t, d;

  m=(k%22)+20;
  v=0;
  t=0;
  d=0;

  while (t<m) {
      if (t<m/2) {
          d = d+1;
      }
      else {
          d = d-1;
      }
      t = t+1;
  }

}
