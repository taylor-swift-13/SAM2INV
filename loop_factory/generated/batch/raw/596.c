int main1(int n,int q){
  int k, i, t, v;

  k=q+13;
  i=0;
  t=-1;
  v=-1;

  while (1) {
      if (i>=k) {
          break;
      }
      t = t+3;
      i = i+1;
      t = t+4;
      v = v+1;
      t = t+1;
      if (i+4<=t+k) {
          v = v+i;
      }
  }

}
