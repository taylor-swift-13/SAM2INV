int main1(int a,int b){
  int i, v, p, m;

  i=20;
  v=0;
  p=i;
  m=v;

  while (1) {
      if (v<i/2) {
          p = p+m;
      }
      else {
          p = p+1;
      }
      m = m+m;
  }

}
